-- Prove2me | solution 1 for Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a8a77dda-8abf-56b9-a469-96cc3fe969e0

import Mathlib
import Theorems.Thm_exteriorPower_map_mulLeft_apply_eq_norm_smul
import Theorems.Thm_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing

set_option autoImplicit false

open scoped TensorProduct

namespace N3Alg

theorem range_smul_id_eq {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V] (r : R) :
    LinearMap.range (r • (LinearMap.id : V →ₗ[R] V)) = Ideal.span {r} • (⊤ : Submodule R V) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) (Submodule.mem_top : w ∈ ⊤)
  · refine Submodule.smul_le.mpr fun a ha v _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨c • v, ?_⟩
    change r • (c • v) = (c * r) • v
    rw [mul_comm, mul_smul]

theorem ideal_eq_of_smul_top_eq {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} [Unique ι] (b : Module.Basis ι R V) {I J : Ideal R} (h : I • (⊤ : Submodule R V) = J • ⊤) : I = J := by

  let e : V ≃ₗ[R] R := b.repr ≪≫ₗ Finsupp.LinearEquiv.finsuppUnique R R ι
  have key : ∀ K : Ideal R, (K • (⊤ : Submodule R V)).map e.toLinearMap = K := fun K => by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, Ideal.smul_top_eq_map, Algebra.algebraMap_self,
      Ideal.map_id, Submodule.restrictScalars_self]
  rw [← key I, ← key J, h]

theorem norm_one_tmul_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι A B) (L : Type*) [CommRing L] [Algebra A L] (x : B) :
    Algebra.norm L ((1 : L) ⊗ₜ[A] x) = algebraMap A L (Algebra.norm A x) := by
  let bL := Algebra.TensorProduct.basis L b
  rw [Algebra.norm_eq_matrix_det bL, Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, bL,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

section AtM

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
  {K : Type*} [Field K] (χ : B →+* K) (hχ : Function.Surjective (χ.comp (algebraMap A B)))
  (g : B) (hg : RingHom.ker χ = Ideal.span {g})
  (𝔪 : Ideal A) (h𝔪 : RingHom.ker (χ.comp (algebraMap A B)) = 𝔪) [𝔪.IsMaximal]
  (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L 𝔪] [IsDomain L] [IsDiscreteValuationRing L]

set_option maxHeartbeats 6400000 in
include hχ hg h𝔪 in

theorem span_norm_tmul_eq_maximalIdeal :
    Ideal.span {Algebra.norm L ((1 : L) ⊗ₜ[A] g)} = IsLocalRing.maximalIdeal L := by
  classical
  have hunit : ∀ s : 𝔪.primeCompl, IsUnit ((χ.comp (algebraMap A B)) s) := fun s => by
    rw [isUnit_iff_ne_zero, ne_eq, ← RingHom.mem_ker, h𝔪]
    exact s.2
  obtain ⟨θ, hθ⟩ : ∃ θ : L →+* K, ∀ a : A, θ (algebraMap A L a) = χ (algebraMap A B a) :=
    ⟨IsLocalization.lift (M := 𝔪.primeCompl) hunit, IsLocalization.lift_eq hunit⟩
  letI : Algebra L K := θ.toAlgebra
  letI : Algebra A K := (θ.comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hθsurj : Function.Surjective θ := fun k => by
    obtain ⟨a, ha⟩ := hχ k
    exact ⟨algebraMap A L a, (hθ a).trans ha⟩
  have hkerθ : RingHom.ker θ = IsLocalRing.maximalIdeal L :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective θ hθsurj)
  let χₐ : B →ₐ[A] K := { toRingHom := χ, commutes' := fun a => (hθ a).symm }
  let Φ : L ⊗[A] B →ₐ[L] K := Algebra.TensorProduct.lift (Algebra.ofId L K) χₐ fun _ _ => mul_comm _ _
  have hΦ : ∀ (l : L) (b : B), Φ (l ⊗ₜ b) = θ l * χ b := fun l b => by
    simp only [Φ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
    rfl

  have hΦsurj : Function.Surjective Φ.toLinearMap := fun k => by
    obtain ⟨l, hl⟩ := hθsurj k
    exact ⟨l ⊗ₜ 1, by rw [AlgHom.toLinearMap_apply, hΦ, map_one, mul_one, hl]⟩
  let θₗ : L →ₗ[L] K := Algebra.linearMap L K
  have hθₗ : ∀ l, θₗ l = θ l := fun _ => rfl
  have hθₗsurj : Function.Surjective θₗ := hθsurj
  have hkerθₗ : LinearMap.ker θₗ = IsLocalRing.maximalIdeal L := by
    rw [← hkerθ]; ext x; rfl
  let eK : K ≃ₗ[L] (L ⧸ IsLocalRing.maximalIdeal L) :=
    (LinearMap.quotKerEquivOfSurjective θₗ hθₗsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hkerθₗ
  let ψ : L ⊗[A] B →ₗ[L] L ⧸ IsLocalRing.maximalIdeal L := eK.toLinearMap ∘ₗ Φ.toLinearMap
  have hψsurj : Function.Surjective ψ := eK.surjective.comp hΦsurj
  have hkerψ : LinearMap.ker ψ = LinearMap.ker Φ.toLinearMap := by
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

  let ι := Module.Free.ChooseBasisIndex A B
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  let bB : Module.Basis ι A B := Module.Free.chooseBasis A B
  let bL : Module.Basis ι L (L ⊗[A] B) := Algebra.TensorProduct.basis L bB
  haveI : Module.Free L (L ⊗[A] B) := Module.Free.of_basis bL
  haveI : Module.Finite L (L ⊗[A] B) := Module.Finite.of_basis bL
  have hd : Module.finrank L (L ⊗[A] B) = Fintype.card ι := Module.finrank_eq_card_basis bL
  let N : Submodule L (L ⊗[A] B) := LinearMap.ker Φ.toLinearMap
  have hED : LinearMap.range (exteriorPower.map (Fintype.card ι) N.subtype) = IsLocalRing.maximalIdeal L • ⊤ :=
    exteriorPower.range_map_subtype_eq_maximalIdeal_smul_top hd N
      ((Submodule.quotEquivOfEq _ _ hkerψ).symm ≪≫ₗ LinearMap.quotKerEquivOfSurjective ψ hψsurj)

  let μ : L ⊗[A] B →ₗ[L] L ⊗[A] B := LinearMap.mulLeft L ((1 : L) ⊗ₜ[A] g)
  have hχg : χ g = 0 := by rw [← RingHom.mem_ker, hg]; exact Ideal.mem_span_singleton_self g
  have hμN : ∀ z, μ z ∈ N := fun z => by
    change Φ ((1 ⊗ₜ g) * z) = 0
    rw [map_mul, hΦ, map_one, one_mul, hχg, zero_mul]
  haveI : IsLocalizedModule 𝔪.primeCompl (TensorProduct.mk A L B 1) :=
    (isLocalizedModule_iff_isBaseChange 𝔪.primeCompl L _).mpr (TensorProduct.isBaseChange A B L)
  have hμsurj : ∀ z ∈ N, ∃ w, μ w = z := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalizedModule.surj 𝔪.primeCompl (TensorProduct.mk A L B 1) z

    have hb : χ b = 0 := by
      have h1 : Φ ((1 : L) ⊗ₜ b) = 0 := by
        change Φ (TensorProduct.mk A L B 1 b) = 0
        rw [← hbs, Submonoid.smul_def, ← algebraMap_smul L (s : A) z, map_smul, show Φ z = 0 from hz, smul_zero]
      rwa [hΦ, map_one, one_mul] at h1
    obtain ⟨c, rfl⟩ : ∃ c, c * g = b := Ideal.mem_span_singleton'.mp (hg ▸ (RingHom.mem_ker).mpr hb)
    obtain ⟨u, hu⟩ := IsLocalization.map_units L s
    refine ⟨((u⁻¹ : Lˣ) : L) • ((1 : L) ⊗ₜ[A] c), ?_⟩
    rw [LinearMap.map_smul]
    change ((u⁻¹ : Lˣ) : L) • ((1 ⊗ₜ g) * (1 ⊗ₜ c)) = z
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm g c]
    have hz' : (u : L) • z = (1 : L) ⊗ₜ[A] (c * g) := by
      rw [hu, algebraMap_smul]; simpa [Submonoid.smul_def] using hbs
    rw [← hz', smul_smul, Units.inv_mul, one_smul]

  have hrange : LinearMap.range (exteriorPower.map (Fintype.card ι) μ) = IsLocalRing.maximalIdeal L • ⊤ := by
    have hfac : μ = N.subtype ∘ₗ LinearMap.codRestrict N μ hμN := LinearMap.ext fun _ => rfl
    have hsurj : Function.Surjective (LinearMap.codRestrict N μ hμN) := fun z => by
      obtain ⟨w, hw⟩ := hμsurj z z.2
      exact ⟨w, Subtype.ext hw⟩
    rw [hfac, exteriorPower.map_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (exteriorPower.map_surjective hsurj)), hED]

  have hμnorm : exteriorPower.map (Fintype.card ι) μ =
      Algebra.norm L ((1 : L) ⊗ₜ[A] g) • (LinearMap.id : ⋀[L]^(Fintype.card ι) (L ⊗[A] B) →ₗ[L] _) := by
    refine LinearMap.ext fun w => ?_
    exact exteriorPower.map_mulLeft_apply_eq_norm_smul bL rfl _ w
  rw [hμnorm, range_smul_id_eq] at hrange
  haveI : Unique (Set.powersetCard ι (Fintype.card ι)) :=
    { default := ⟨Finset.univ, Finset.card_univ⟩
      uniq := fun s => Subtype.ext (Finset.eq_univ_of_card _ s.2) }
  exact ideal_eq_of_smul_top_eq (bL.exteriorPower (Fintype.card ι)) hrange

end AtM

universe u

set_option maxHeartbeats 6400000 in

theorem _root_.P2MW.S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing.solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    {K : Type u} [Field K] (χ : B →+* K) (hχ : Function.Surjective (χ.comp (algebraMap A B)))
    (g : B) (hg : RingHom.ker χ = Ideal.span {g})
    (𝔪 : Ideal A) (h𝔪 : RingHom.ker (χ.comp (algebraMap A B)) = 𝔪) [𝔪.IsMaximal]
    (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ 𝔪]
    [IsDomain Aₘ] [IsDiscreteValuationRing Aₘ] :
    Ideal.span {Algebra.norm A g} = 𝔪 := by
  classical
  have hmap : ∀ {S : Type u} [CommRing S] [Algebra A S] (x : A),
      (Ideal.span {x}).map (algebraMap A S) = Ideal.span {algebraMap A S x} := fun x => by
    rw [Ideal.map_span, Set.image_singleton]
  apply Ideal.eq_of_localization_maximal
  intro P hP
  by_cases hP𝔪 : P = 𝔪
  · subst hP𝔪

    have key := span_norm_tmul_eq_maximalIdeal χ hχ g hg P h𝔪 Aₘ
    rw [norm_one_tmul_eq (Module.Free.chooseBasis A B) Aₘ g, ← hmap,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P Aₘ] at key

    let e : Localization.AtPrime P ≃ₐ[A] Aₘ := IsLocalization.algEquiv P.primeCompl _ _
    have he : (algebraMap A Aₘ) = (e : Localization.AtPrime P →+* Aₘ).comp (algebraMap A (Localization.AtPrime P)) := by
      ext a; exact (e.commutes a).symm
    have tr : ∀ I : Ideal A, I.map (algebraMap A (Localization.AtPrime P)) =
        (I.map (algebraMap A Aₘ)).map (e.symm : Aₘ →+* Localization.AtPrime P) := fun I => by
      rw [he, ← Ideal.map_map, Ideal.map_map (e : Localization.AtPrime P →+* Aₘ)]
      have : (e.symm : Aₘ →+* Localization.AtPrime P).comp (e : Localization.AtPrime P →+* Aₘ) = RingHom.id _ := by
        ext x; exact e.symm_apply_apply x
      rw [this, Ideal.map_id]
    rw [tr, tr, key]
  ·
    have hle : ¬ 𝔪 ≤ P := fun h => hP𝔪 ((Ideal.IsMaximal.eq_of_le inferInstance hP.ne_top h).symm)
    have htop : ∀ I : Ideal A, ¬ I ≤ P → I.map (algebraMap A (Localization.AtPrime P)) = ⊤ := fun I hI => by
      by_contra h
      refine hI fun x hx => ?_
      by_contra hxP
      exact Set.disjoint_left.mp ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl _ I).mp h) hxP hx
    rw [htop 𝔪 hle, htop]

    intro hNP
    obtain ⟨s, hs𝔪, hsP⟩ := Set.not_subset.mp hle
    have hs : algebraMap A B s ∈ RingHom.ker χ := by
      rw [RingHom.mem_ker]
      have : s ∈ RingHom.ker (χ.comp (algebraMap A B)) := h𝔪 ▸ hs𝔪
      exact this
    rw [hg] at hs
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hs
    have hnorm := congrArg (Algebra.norm A) hc
    rw [map_mul, Algebra.norm_algebraMap] at hnorm
    have hmem : s ^ Module.finrank A B ∈ P := by
      rw [← hnorm]
      exact hNP (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    exact hsP (hP.isPrime.mem_of_pow_mem _ hmem)

end N3Alg

end S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing
end P2MW
export P2MW.S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing (solution)
