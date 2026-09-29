-- Prove2me | solution 1 for Ideal.exists_map_localization_eq_span_of_baseChange_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1a06464e-ce2f-53eb-b1cf-a089ea688fec

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_map_localization_eq_span_of_baseChange_mvPolynomial

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u

namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap Quotient.algebraMap_eq Quotient.eq_zero_iff_mem mul_mem_right sum_mem primeCompl span mul_unit_mem_iff_mem IsMaximal Quotient.mk Quotient.field mul_mem_left map mem_sup_left ext Pure mem_map_of_mem span_le mem_sup_right mem_comap map_mono mem_span_range_iff_exists_fun subset_span Quotient.mk_surjective" end Ideal
p2m_open_scoped "Ideal" in
theorem Ideal.forall_mem_map_of_sum_mul_algebraMap_mem_of_flat_LCID
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] [Module.Flat R S] {μ : ℕ}
    (I 𝔫 : Ideal R) (j : Fin μ → R)
    (hindep : ∀ a : Fin μ → R, (∑ i, a i * j i) ∈ I → ∀ i, a i ∈ 𝔫)
    (a' : Fin μ → S) (ha' : (∑ i, a' i * algebraMap R S (j i)) ∈ I.map (algebraMap R S)) :
    ∀ i, a' i ∈ 𝔫.map (algebraMap R S) := by
  classical

  let ψ : (Fin μ → R) →ₗ[R] R :=
    { toFun := fun a => ∑ i, a i * j i
      map_add' := fun a b => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun q a => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  let Φ : (Fin μ → R) →ₗ[R] R ⧸ I := (Submodule.mkQ (I : Submodule R R)) ∘ₗ ψ
  have hΦ : ∀ a, Φ a = Ideal.Quotient.mk I (∑ i, a i * j i) := fun a => rfl
  have hexact : Function.Exact (LinearMap.ker Φ).subtype Φ := by
    intro y
    constructor
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨z, rfl⟩; exact z.2
  have hflat := Module.Flat.lTensor_exact S hexact

  let τ : S ⊗[R] (Fin μ → R) := ∑ i, a' i ⊗ₜ[R] (Pi.single i 1 : Fin μ → R)
  have hΦsingle : ∀ i, Φ (Pi.single i 1) = Ideal.Quotient.mk I (j i) := fun i => by
    rw [hΦ]
    congr 1
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_mul]
  have hτ : (Φ.lTensor S) τ = 0 := by
    have h1 : (Φ.lTensor S) τ = ∑ i, (a' i * algebraMap R S (j i)) ⊗ₜ[R] (1 : R ⧸ I) := by
      simp only [τ, map_sum, LinearMap.lTensor_tmul, hΦsingle]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show Ideal.Quotient.mk I (j i) = (j i) • (1 : R ⧸ I) by rw [Algebra.smul_def, mul_one]; rfl,
        ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
    rw [h1, ← TensorProduct.sum_tmul, ← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 ha', map_zero]
  obtain ⟨σ, hσ⟩ := (hflat τ).1 hτ

  let χ := TensorProduct.piScalarRight R S S (Fin μ)
  have hχ : ∀ (x : S) (f : Fin μ → R), χ (x ⊗ₜ[R] f) = fun l => f l • x := fun x f => by
    change TensorProduct.piScalarRight R S S (Fin μ) (x ⊗ₜ[R] f) = _
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have hχτ : χ τ = a' := by
    funext l
    simp only [τ, map_sum, hχ, Finset.sum_apply, Pi.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hχσ : ∀ (σ' : S ⊗[R] ↥(LinearMap.ker Φ)) (l : Fin μ),
      χ ((LinearMap.ker Φ).subtype.lTensor S σ') l ∈ 𝔫.map (algebraMap R S) := by
    intro σ' l
    induction σ' using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Ideal.zero_mem _
    | tmul x κ =>
      rw [LinearMap.lTensor_tmul, hχ]
      change (κ : Fin μ → R) l • x ∈ Ideal.map (algebraMap R S) 𝔫
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hindep _ ?_ l))
      exact Ideal.Quotient.eq_zero_iff_mem.1 ((hΦ _).symm.trans κ.2)
    | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply]
      exact Ideal.add_mem _ hx hy
  intro i
  have := hχσ σ i
  rwa [hσ, hχτ] at this

namespace MvPolynomial p2m_export "MvPolynomial" "X map R funext ext algebraMvPolynomial algebraMap_eq C coe_smul induction_on" end MvPolynomial
p2m_open_scoped "MvPolynomial" in
theorem MvPolynomial.exists_generators_mod_mul_and_forall_mem_of_sum_mul_mem_LCID
    {k : Type u} [Field k] {N : ℕ} (J 𝔫 : Ideal (MvPolynomial (Fin N) k)) [𝔫.IsMaximal] :
    ∃ (μ : ℕ) (j : Fin μ → MvPolynomial (Fin N) k), (∀ i, j i ∈ J) ∧
      (∀ x ∈ J, ∃ a : Fin μ → MvPolynomial (Fin N) k, x - ∑ i, a i * j i ∈ 𝔫 * J) ∧
      (∀ a : Fin μ → MvPolynomial (Fin N) k, (∑ i, a i * j i) ∈ 𝔫 * J → ∀ i, a i ∈ 𝔫) := by
  classical
  letI hF : Field (MvPolynomial (Fin N) k ⧸ 𝔫) := Ideal.Quotient.field 𝔫
  letI instV : Module (MvPolynomial (Fin N) k ⧸ 𝔫) (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J)) :=
    Module.instQuotientIdealSubmoduleHSMulTop (↥J) 𝔫
  letI instVd : DistribMulAction (MvPolynomial (Fin N) k ⧸ 𝔫) (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J)) :=
    instV.toDistribMulAction
  letI instVm : MulAction (MvPolynomial (Fin N) k ⧸ 𝔫) (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J)) :=
    instVd.toMulAction
  letI instVs : SMul (MvPolynomial (Fin N) k ⧸ 𝔫) (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J)) :=
    instVm.toSMul
  haveI instVT : IsScalarTower (MvPolynomial (Fin N) k) (MvPolynomial (Fin N) k ⧸ 𝔫)
      (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J)) :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_quotient_ideal_smul (↥J) 𝔫)
  haveI : Module.Finite (MvPolynomial (Fin N) k ⧸ 𝔫) (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J)) :=
    Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin N) k) _ _
  let b := Module.finBasis (MvPolynomial (Fin N) k ⧸ 𝔫) (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J))
  set μ := Module.finrank (MvPolynomial (Fin N) k ⧸ 𝔫) (↥J ⧸ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J)) with hμ
  choose jv hjv using fun i => Submodule.Quotient.mk_surjective (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J) (b i)
  let j : Fin μ → MvPolynomial (Fin N) k := fun i => (jv i : MvPolynomial (Fin N) k)
  have hjJ : ∀ i, j i ∈ J := fun i => (jv i).2
  have hmkQ : ∀ a : Fin μ → MvPolynomial (Fin N) k,
      (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J).mkQ (∑ i, a i • jv i) = ∑ i, Ideal.Quotient.mk 𝔫 (a i) • b i := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.mkQ_apply, hjv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hcoe : ∀ a : Fin μ → MvPolynomial (Fin N) k, ((∑ i, a i • jv i : ↥J) : MvPolynomial (Fin N) k) = ∑ i, a i * j i := by
    intro a
    rw [Submodule.coe_sum]
    rfl
  refine ⟨μ, j, hjJ, ?_, ?_⟩
  ·
    intro x hx
    let v := (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J).mkQ ⟨x, hx⟩
    choose a ha using fun i => Ideal.Quotient.mk_surjective (b.repr v i)
    refine ⟨a, ?_⟩
    have h1 : (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J).mkQ (⟨x, hx⟩ - ∑ i, a i • jv i) = 0 := by
      rw [map_sub, hmkQ, sub_eq_zero]
      simp_rw [ha]
      exact (b.sum_repr v).symm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff] at h1
    rw [← Ideal.smul_eq_mul]
    convert h1 using 1
    rw [Submodule.coe_sub, hcoe]
  ·
    intro a ha i
    have h1 : (∑ i, a i • jv i : ↥J) ∈ (𝔫 • ⊤ : Submodule (MvPolynomial (Fin N) k) ↥J) := by
      rw [Submodule.mem_smul_top_iff, hcoe, Ideal.smul_eq_mul]
      exact ha
    have h2 : ∑ i, Ideal.Quotient.mk 𝔫 (a i) • b i = 0 := by
      rw [← hmkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h1
    exact Ideal.Quotient.eq_zero_iff_mem.1
      (Fintype.linearIndependent_iff.1 b.linearIndependent (fun i => Ideal.Quotient.mk 𝔫 (a i)) h2 i)

p2m_open_scoped "MvPolynomial" in
theorem MvPolynomial.le_of_forall_sum_mul_mem_imp_of_map_eq_span_LCID
    {K : Type u} [Field K] {N μ M : ℕ} (J' 𝔫' : Ideal (MvPolynomial (Fin N) K)) [𝔫'.IsMaximal]
    (v : Fin μ → MvPolynomial (Fin N) K) (hv : ∀ i, v i ∈ J')
    (hrel : ∀ a' : Fin μ → MvPolynomial (Fin N) K, (∑ i, a' i * v i) ∈ 𝔫' * J' → ∀ i, a' i ∈ 𝔫')
    (g' : Fin M → Localization.AtPrime 𝔫')
    (hg' : J'.map (algebraMap (MvPolynomial (Fin N) K) (Localization.AtPrime 𝔫')) = Ideal.span (Set.range g')) :
    μ ≤ M := by
  classical
  letI hF' : Field (MvPolynomial (Fin N) K ⧸ 𝔫') := Ideal.Quotient.field 𝔫'
  letI instV' : Module (MvPolynomial (Fin N) K ⧸ 𝔫')
      (↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J')) :=
    Module.instQuotientIdealSubmoduleHSMulTop (↥J') 𝔫'
  letI instVd' : DistribMulAction (MvPolynomial (Fin N) K ⧸ 𝔫')
      (↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J')) :=
    instV'.toDistribMulAction
  letI instVm' : MulAction (MvPolynomial (Fin N) K ⧸ 𝔫')
      (↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J')) :=
    instVd'.toMulAction
  letI instVs' : SMul (MvPolynomial (Fin N) K ⧸ 𝔫')
      (↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J')) :=
    instVm'.toSMul
  haveI instVT' : IsScalarTower (MvPolynomial (Fin N) K) (MvPolynomial (Fin N) K ⧸ 𝔫')
      (↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J')) :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_quotient_ideal_smul (↥J') 𝔫')
  haveI : Module.Finite (MvPolynomial (Fin N) K ⧸ 𝔫')
      (↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J')) :=
    Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin N) K) _ _

  let jv' : Fin μ → ↥J' := fun i => ⟨v i, hv i⟩
  let w : Fin μ → ↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J') :=
    fun i => (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J').mkQ (jv' i)
  have hcoe' : ∀ a' : Fin μ → MvPolynomial (Fin N) K,
      ((∑ i, a' i • jv' i : ↥J') : MvPolynomial (Fin N) K) = ∑ i, a' i * v i := by
    intro a'
    rw [Submodule.coe_sum]
    rfl
  have hli : LinearIndependent (MvPolynomial (Fin N) K ⧸ 𝔫') w := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    choose a' ha' using fun i => Ideal.Quotient.mk_surjective (g i)
    have h1 : (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J').mkQ (∑ i, a' i • jv' i) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← ha' i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, hcoe', Ideal.smul_eq_mul] at h1
    rw [← ha' i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hrel a' h1 i)

  have hg'mem : ∀ t, g' t ∈ J'.map (algebraMap (MvPolynomial (Fin N) K) (Localization.AtPrime 𝔫')) :=
    fun t => hg' ▸ Ideal.subset_span ⟨t, rfl⟩
  choose ys hys using fun t => (IsLocalization.mem_map_algebraMap_iff 𝔫'.primeCompl _).1 (hg'mem t)
  let y : Fin M → MvPolynomial (Fin N) K := fun t => ((ys t).1 : MvPolynomial (Fin N) K)
  have hyJ : ∀ t, y t ∈ J' := fun t => (ys t).1.2
  have hJ'N : J'.map (algebraMap (MvPolynomial (Fin N) K) (Localization.AtPrime 𝔫')) =
      (Ideal.span (Set.range y)).map (algebraMap (MvPolynomial (Fin N) K) (Localization.AtPrime 𝔫')) := by
    refine le_antisymm ?_ (Ideal.map_mono (Ideal.span_le.2 (Set.range_subset_iff.2 hyJ)))
    rw [hg', Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    have hu : IsUnit (algebraMap (MvPolynomial (Fin N) K) (Localization.AtPrime 𝔫') ((ys t).2 : MvPolynomial (Fin N) K)) :=
      IsLocalization.map_units _ (ys t).2
    rw [SetLike.mem_coe, ← Ideal.mul_unit_mem_iff_mem _ hu, hys t]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨t, rfl⟩)
  have hsat' : ∀ x ∈ J', ∃ u : MvPolynomial (Fin N) K, u ∉ 𝔫' ∧ u * x ∈ Ideal.span (Set.range y) := by
    intro x hx
    have h1 : algebraMap _ (Localization.AtPrime 𝔫') x ∈
        (Ideal.span (Set.range y)).map (algebraMap _ (Localization.AtPrime 𝔫')) := by
      rw [← hJ'N]; exact Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨z, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔫'.primeCompl _).1 h1
    rw [← map_mul] at hzs
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔫'.primeCompl _).1 hzs
    refine ⟨c * s, (𝔫'.primeCompl.mul_mem c.2 s.2 : (c : MvPolynomial (Fin N) K) * s ∈ 𝔫'.primeCompl), ?_⟩
    rw [show (c : MvPolynomial (Fin N) K) * s * x = c * (x * s) by ring]
    change (c : MvPolynomial (Fin N) K) * (x * ((z, s) : _ × _).2) ∈ _
    rw [hc]
    exact Ideal.mul_mem_left _ _ z.2
  let w' : Fin M → ↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J') :=
    fun t => (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J').mkQ (ys t).1
  have hspan' : (⊤ : Submodule (MvPolynomial (Fin N) K ⧸ 𝔫') _) ≤
      Submodule.span (MvPolynomial (Fin N) K ⧸ 𝔫') (Set.range w') := by
    rintro q -
    obtain ⟨xv, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u, hu, hux⟩ := hsat' xv xv.2
    obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial (Fin N) K)).1 hux
    have h1 : (u • xv : ↥J') = ∑ t, e t • (ys t).1 := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_sum, smul_eq_mul, ← he]
      rfl
    have hu0 : (Ideal.Quotient.mk 𝔫' u) ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have h2 : (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J').mkQ (u • xv) ∈
        Submodule.span (MvPolynomial (Fin N) K ⧸ 𝔫') (Set.range w') := by
      rw [h1, map_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      rw [map_smul, ← algebraMap_smul (MvPolynomial (Fin N) K ⧸ 𝔫') (e t)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [map_smul, ← algebraMap_smul (MvPolynomial (Fin N) K ⧸ 𝔫') u, Ideal.Quotient.algebraMap_eq] at h2
    have h3 := Submodule.smul_mem _ (Ideal.Quotient.mk 𝔫' u)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at h3

  have h1 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h1
  have htop : Submodule.span (MvPolynomial (Fin N) K ⧸ 𝔫') (Set.range w') = ⊤ := top_le_iff.1 hspan'
  have h3 := finrank_range_le_card (R := MvPolynomial (Fin N) K ⧸ 𝔫') w'
  rw [Fintype.card_fin] at h3
  have h4 : Module.finrank (MvPolynomial (Fin N) K ⧸ 𝔫')
      ↥(Submodule.span (MvPolynomial (Fin N) K ⧸ 𝔫') (Set.range w')) =
      Module.finrank (MvPolynomial (Fin N) K ⧸ 𝔫') (↥J' ⧸ (𝔫' • ⊤ : Submodule (MvPolynomial (Fin N) K) ↥J')) :=
    (LinearEquiv.ofTop _ htop).finrank_eq
  rw [← h4] at h1
  exact h1.trans h3

theorem solution
    (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']
    (N M : ℕ) (J : Ideal (MvPolynomial (Fin N) k))
    (𝔫 : Ideal (MvPolynomial (Fin N) k)) [𝔫.IsMaximal] (h𝔫 : J ≤ 𝔫)
    (𝔫' : Ideal (MvPolynomial (Fin N) k')) [𝔫'.IsMaximal]
    (hover : Ideal.map (MvPolynomial.map (algebraMap k k')) 𝔫 ≤ 𝔫')
    (hgen : ∃ g : Fin M → Localization.AtPrime 𝔫',
      Ideal.map (algebraMap (MvPolynomial (Fin N) k') (Localization.AtPrime 𝔫'))
          (Ideal.map (MvPolynomial.map (algebraMap k k')) J) = Ideal.span (Set.range g)) :
    ∃ g : Fin M → Localization.AtPrime 𝔫, Ideal.map (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime 𝔫)) (J) = Ideal.span (Set.range g) := by
  classical
  let ι : MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) k' := MvPolynomial.map (algebraMap k k')

  obtain ⟨μ, j, hjJ, hspan, hindep⟩ :=
    MvPolynomial.exists_generators_mod_mul_and_forall_mem_of_sum_mul_mem_LCID J 𝔫

  have hindep' : ∀ a' : Fin μ → MvPolynomial (Fin N) k', (∑ i, a' i * ι (j i)) ∈ (𝔫 * J).map ι →
      ∀ i, a' i ∈ 𝔫.map ι := by
    intro a' ha'
    letI : Algebra (MvPolynomial (Fin N) k) (MvPolynomial (Fin N) k') := MvPolynomial.algebraMvPolynomial
    haveI : Module.Flat (MvPolynomial (Fin N) k) (MvPolynomial (Fin N) k') :=
      Module.Flat.isBaseChange k (MvPolynomial (Fin N) k) k' (MvPolynomial (Fin N) k') Algebra.IsPushout.out
    exact Ideal.forall_mem_map_of_sum_mul_algebraMap_mem_of_flat_LCID (𝔫 * J) 𝔫 j hindep a' ha'

  have hT : ∀ n ∈ J.map ι, ∃ d : Fin μ → MvPolynomial (Fin N) k', n - ∑ i, d i * ι (j i) ∈ (𝔫 * J).map ι := by
    intro n hn
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (show n ∈ Ideal.span (⇑ι '' ↑J) from hn)
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := hspan y hy
      refine ⟨fun i => ι (a i), ?_⟩
      have : ι y - ∑ i, ι (a i) * ι (j i) = ι (y - ∑ i, a i * j i) := by
        rw [map_sub, map_sum]; simp_rw [map_mul]
      rw [this]
      exact Ideal.mem_map_of_mem _ ha
    · exact ⟨0, by simp⟩
    · rintro x y - - ⟨d₁, h₁⟩ ⟨d₂, h₂⟩
      refine ⟨d₁ + d₂, ?_⟩
      have : x + y - ∑ i, (d₁ + d₂) i * ι (j i) = (x - ∑ i, d₁ i * ι (j i)) + (y - ∑ i, d₂ i * ι (j i)) := by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
      rw [this]
      exact Ideal.add_mem _ h₁ h₂
    · rintro q x - ⟨d, hd⟩
      refine ⟨fun i => q * d i, ?_⟩
      have : q • x - ∑ i, q * d i * ι (j i) = q * (x - ∑ i, d i * ι (j i)) := by
        rw [smul_eq_mul, mul_sub, Finset.mul_sum]; simp_rw [mul_assoc]
      rw [this]
      exact Ideal.mul_mem_left _ _ hd
  have hS : ∀ x' ∈ 𝔫' * J.map ι, ∃ c : Fin μ → MvPolynomial (Fin N) k', (∀ i, c i ∈ 𝔫') ∧
      x' - ∑ i, c i * ι (j i) ∈ (𝔫 * J).map ι := by
    intro x' hx'
    refine Submodule.mul_induction_on hx' ?_ ?_
    · intro m hm n hn
      obtain ⟨d, hd⟩ := hT n hn
      refine ⟨fun i => m * d i, fun i => Ideal.mul_mem_right _ _ hm, ?_⟩
      have : m * n - ∑ i, m * d i * ι (j i) = m * (n - ∑ i, d i * ι (j i)) := by
        rw [mul_sub, Finset.mul_sum]; simp_rw [mul_assoc]
      rw [this]
      exact Ideal.mul_mem_left _ _ hd
    · rintro x y ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
      refine ⟨c₁ + c₂, fun i => Ideal.add_mem _ (hc₁ i) (hc₂ i), ?_⟩
      have : x + y - ∑ i, (c₁ + c₂) i * ι (j i) = (x - ∑ i, c₁ i * ι (j i)) + (y - ∑ i, c₂ i * ι (j i)) := by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
      rw [this]
      exact Ideal.add_mem _ h₁ h₂
  have hrel : ∀ a' : Fin μ → MvPolynomial (Fin N) k', (∑ i, a' i * ι (j i)) ∈ 𝔫' * J.map ι → ∀ i, a' i ∈ 𝔫' := by
    intro a' ha' i
    obtain ⟨c, hc𝔫, hc⟩ := hS _ ha'
    have h1 : (∑ i, (a' i - c i) * ι (j i)) ∈ (𝔫 * J).map ι := by
      have : ∑ i, (a' i - c i) * ι (j i) = ∑ i, a' i * ι (j i) - ∑ i, c i * ι (j i) := by
        simp only [sub_mul, Finset.sum_sub_distrib]
      rw [this]; exact hc
    have h2 := hindep' _ h1 i
    have h3 : a' i - c i ∈ 𝔫' := hover h2
    simpa using Ideal.add_mem _ h3 (hc𝔫 i)

  obtain ⟨g', hg'⟩ := hgen
  have hμM : μ ≤ M :=
    MvPolynomial.le_of_forall_sum_mul_mem_imp_of_map_eq_span_LCID (J.map ι) 𝔫' (fun i => ι (j i))
      (fun i => Ideal.mem_map_of_mem ι (hjJ i)) hrel g' hg'

  let gfin : Fin M → Localization.AtPrime 𝔫 := fun t =>
    if h : (t : ℕ) < μ then algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime 𝔫) (j ⟨t, h⟩) else 0
  refine ⟨gfin, le_antisymm ?_ ?_⟩
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    obtain ⟨a, ha⟩ := hspan x hx
    rw [show x = (∑ i, a i * j i) + (x - ∑ i, a i * j i) by ring, map_add]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · rw [map_sum]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨i, lt_of_lt_of_le i.2 hμM⟩, ?_⟩)
      simp [gfin]
    · rw [Ideal.smul_eq_mul, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_mul]
      exact Ideal.mem_map_of_mem _ ha
  · rw [Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    by_cases h : (t : ℕ) < μ
    · simp only [gfin, dif_pos h, SetLike.mem_coe]
      exact Ideal.mem_map_of_mem _ (hjJ _)
    · simp only [gfin, dif_neg h, SetLike.mem_coe]
      exact Ideal.zero_mem _

end S_Ideal_exists_map_localization_eq_span_of_baseChange_mvPolynomial
end P2MW
export P2MW.S_Ideal_exists_map_localization_eq_span_of_baseChange_mvPolynomial (solution)
