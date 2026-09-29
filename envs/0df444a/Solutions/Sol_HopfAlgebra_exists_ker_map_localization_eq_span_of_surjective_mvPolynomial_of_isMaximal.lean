-- Prove2me | solution 1 for HopfAlgebra.exists_ker_map_localization_eq_span_of_surjective_mvPolynomial_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4eb8a13b-d217-59fc-ac51-de8796554f8e

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_algEquiv_pi_mvPolynomial_quotient_span_pow_of_isAlgClosed
import Theorems.Thm_Algebra_exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField
import Theorems.Thm_Ideal_exists_map_localization_eq_span_of_baseChange_mvPolynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_ker_map_localization_eq_span_of_surjective_mvPolynomial_of_isMaximal
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u v

open scoped TensorProduct

theorem solution
    (k : Type u) [Field k] (B : Type u) [CommRing B] [HopfAlgebra k B] [Module.Finite k B]
    (N : ℕ) (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Surjective φ)
    (𝔫 : Ideal (MvPolynomial (Fin N) k)) [𝔫.IsMaximal] (h𝔫 : RingHom.ker φ ≤ 𝔫) :
    ∃ g : Fin N → MvPolynomial (Fin N) k, (∀ i, g i ∈ RingHom.ker φ) ∧
      Ideal.map (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime 𝔫)) (RingHom.ker φ) =
        Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime 𝔫) (g i)) := by
  classical

  let P := MvPolynomial (Fin N) k
  let kb : Type u := AlgebraicClosure k
  let Pb := MvPolynomial (Fin N) kb
  let ι : P →+* Pb := MvPolynomial.map (algebraMap k kb)
  set J : Ideal P := RingHom.ker φ with hJdef

  let Bb := kb ⊗[k] B
  let τ : kb ⊗[k] P ≃ₐ[kb] Pb := MvPolynomial.algebraTensorAlgEquiv k kb
  let φb : Pb →ₐ[kb] Bb := (Algebra.TensorProduct.map (AlgHom.id kb kb) φ).comp τ.symm.toAlgHom
  have hτ : ∀ f : P, τ ((1 : kb) ⊗ₜ[k] f) = ι f := by
    intro f
    change MvPolynomial.algebraTensorAlgEquiv k kb ((1 : kb) ⊗ₜ[k] f) = MvPolynomial.map (algebraMap k kb) f
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have hφbs : Function.Surjective φb :=
    (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hφ).comp τ.symm.surjective
  haveI : Module.Finite kb Bb := inferInstance
  have hkerb : RingHom.ker φb = J.map ι := by
    apply le_antisymm
    · intro g hg
      obtain ⟨t, rfl⟩ := τ.surjective g
      have h0 : Algebra.TensorProduct.map (AlgHom.id kb kb) φ t = 0 := by
        have := hg
        rwa [RingHom.mem_ker, show φb (τ t) = Algebra.TensorProduct.map (AlgHom.id kb kb) φ (τ.symm (τ t)) from rfl,
          τ.symm_apply_apply] at this
      let ιJ : J.restrictScalars k →ₗ[k] P := (J.restrictScalars k).subtype
      have hex : Function.Exact (ιJ.lTensor kb) ((φ : P →ₐ[k] B).toLinearMap.lTensor kb) := by
        refine lTensor_exact kb (fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, ?_⟩) hφ
        rintro ⟨z, rfl⟩; exact z.2
      have h0' : ((φ : P →ₐ[k] B).toLinearMap.lTensor kb) t = 0 := by rw [← h0]; rfl
      obtain ⟨s, hs⟩ := (hex t).1 h0'
      rw [← hs]
      clear hs h0 h0' hg
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul c j =>
        rw [LinearMap.lTensor_tmul]
        change τ (c ⊗ₜ[k] (j : P)) ∈ J.map ι
        have : c ⊗ₜ[k] (j : P) = c • ((1 : kb) ⊗ₜ[k] (j : P)) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hτ, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem ι j.2)
      | add x y hx hy => rw [map_add, map_add]; exact Ideal.add_mem _ hx hy
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hτ]
      change Algebra.TensorProduct.map (AlgHom.id kb kb) φ (τ.symm (τ ((1 : kb) ⊗ₜ[k] f))) = 0
      rw [τ.symm_apply_apply, Algebra.TensorProduct.map_tmul, show φ f = 0 from hf, TensorProduct.tmul_zero]

  letI : Algebra P Pb := ι.toAlgebra
  have hιalg : (algebraMap P Pb : P →+* Pb) = ι := rfl
  haveI : IsScalarTower k P Pb := IsScalarTower.of_algebraMap_eq fun c => by
    change MvPolynomial.C (algebraMap k kb c) = MvPolynomial.map (algebraMap k kb) (MvPolynomial.C c)
    rw [MvPolynomial.map_C]
  haveI : Algebra.IsIntegral P Pb := by

    haveI : Algebra.IsIntegral P (P ⊗[k] kb) := Algebra.IsIntegral.tensorProduct k P kb
    let θ : P ⊗[k] kb →ₐ[P] Pb := Algebra.TensorProduct.lift (Algebra.ofId P Pb)
      ((IsScalarTower.toAlgHom k kb Pb).restrictScalars k) (fun _ _ => Commute.all _ _)
    refine Algebra.IsIntegral.of_surjective θ ?_
    intro g
    induction g using MvPolynomial.induction_on with
    | C c => exact ⟨(1 : P) ⊗ₜ[k] c, by simp [θ, Algebra.ofId_apply]; rfl⟩
    | add f g hf hg =>
      obtain ⟨x, rfl⟩ := hf; obtain ⟨y, rfl⟩ := hg; exact ⟨x + y, map_add _ _ _⟩
    | mul_X f i hf =>
      obtain ⟨x, rfl⟩ := hf
      refine ⟨x * ((MvPolynomial.X i : P) ⊗ₜ[k] (1 : kb)), ?_⟩
      rw [map_mul]
      congr 1
      simp [θ, Algebra.ofId_apply, hιalg, ι]
      exact MvPolynomial.map_X _ i
  obtain ⟨𝔫', h𝔫'max, hcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := Pb) 𝔫 (by
    have : RingHom.ker (algebraMap P Pb) = ⊥ := by
      rw [hιalg]; exact (RingHom.injective_iff_ker_eq_bot _).1 (MvPolynomial.map_injective _ (algebraMap k kb).injective)
    rw [this]; exact bot_le)
  haveI := h𝔫'max
  have hover : 𝔫.map ι ≤ 𝔫' := by rw [Ideal.map_le_iff_le_comap, ← hιalg, hcomap]
  have hJ𝔫' : RingHom.ker φb ≤ 𝔫' := hkerb ▸ (Ideal.map_mono h𝔫).trans hover

  obtain ⟨n, r, q, hq, ⟨σ⟩⟩ := HopfAlgebra.exists_algEquiv_pi_mvPolynomial_quotient_span_pow_of_isAlgClosed kb Bb

  let Pr := MvPolynomial (Fin r) kb
  let IC : Ideal Pr := Ideal.span (Set.range fun i => (MvPolynomial.X i : Pr) ^ q i)

  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Pb →+* (Fin n → Pr ⧸ IC), ∀ x, ρ x = σ (φb x) :=
    ⟨((σ : Bb →ₐ[kb] (Fin n → Pr ⧸ IC)).comp φb).toRingHom, fun _ => rfl⟩
  have hρs : Function.Surjective ρ := fun y => by
    obtain ⟨x, hx⟩ := (σ.surjective.comp hφbs) y; exact ⟨x, (hρdef x).trans hx⟩
  have hkerρ : RingHom.ker ρ = RingHom.ker φb := by
    ext x; rw [RingHom.mem_ker, RingHom.mem_ker, hρdef, map_eq_zero_iff _ σ.injective]
  obtain ⟨M', hM'def⟩ : ∃ M' : Ideal (Fin n → Pr ⧸ IC), M' = 𝔫'.map ρ := ⟨_, rfl⟩
  have hcm : M'.comap ρ = 𝔫' := by
    rw [hM'def, Ideal.comap_map_of_surjective _ hρs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 (show RingHom.ker ρ ≤ 𝔫' from hkerρ ▸ hJ𝔫')
  have hM'max : M'.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective ρ hρs h𝔫'max with htop | hm
    · exfalso; apply h𝔫'max.ne_top; rw [← hcm, hM'def, htop, Ideal.comap_top]
    · rw [hM'def]; exact hm

  have hej : ∃ j : Fin n, (Pi.single j 1 : Fin n → Pr ⧸ IC) ∉ M' := by
    by_contra hall
    push Not at hall
    apply hM'max.ne_top
    rw [Ideal.eq_top_iff_one, show (1 : Fin n → Pr ⧸ IC) = ∑ j, Pi.single j 1 from (Finset.univ_sum_single 1).symm]
    exact Ideal.sum_mem _ fun j _ => hall j
  obtain ⟨j, hj⟩ := hej
  haveI : Nonempty (Fin n) := ⟨j⟩
  let C := Pr ⧸ IC
  obtain ⟨ψ, hρψ⟩ : ∃ ψ : Pb →ₐ[kb] C, ∀ x, ψ x = ρ x j :=
    ⟨(Pi.evalAlgHom kb (fun _ : Fin n => C) j).comp ((σ : Bb →ₐ[kb] (Fin n → Pr ⧸ IC)).comp φb), fun x => by
      rw [hρdef]; rfl⟩
  have hψs : Function.Surjective ψ := fun c => by
    obtain ⟨y, hy⟩ := hρs (Pi.single j c); exact ⟨y, by rw [hρψ, hy, Pi.single_eq_same]⟩

  obtain ⟨t, ht⟩ := hρs (1 - Pi.single j 1)
  have h1t : 1 - t ∉ 𝔫' := by
    intro hmem
    apply hj
    have : ρ (1 - t) = Pi.single j 1 := by rw [map_sub, map_one, ht, sub_sub_cancel]
    rw [← this, hM'def]
    exact Ideal.mem_map_of_mem _ hmem
  have hkψ : ∀ x ∈ RingHom.ker ψ, x * (1 - t) ∈ RingHom.ker φb := by
    intro x hx
    rw [← hkerρ, RingHom.mem_ker, map_mul, map_sub, map_one, ht, sub_sub_cancel]
    rw [RingHom.mem_ker, hρψ] at hx
    ext i
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hi : i = j
    · subst hi; rw [hx, zero_mul]
    · rw [Pi.single_eq_of_ne hi, mul_zero]
  have hkerψ𝔫 : RingHom.ker ψ ≤ 𝔫' := by
    intro x hx
    have hprime := h𝔫'max.isPrime
    rcases hprime.mem_or_mem (hJ𝔫' (hkψ x hx)) with h | h
    · exact h
    · exact absurd h h1t
  have hkerφψ : RingHom.ker φb ≤ RingHom.ker ψ := by
    intro x hx
    have hx' : ρ x = 0 := by rw [← RingHom.mem_ker, hkerρ]; exact hx
    rw [RingHom.mem_ker, hρψ, hx', Pi.zero_apply]

  have hlocψ : (RingHom.ker ψ).map (algebraMap Pb (Localization.AtPrime 𝔫')) =
      (RingHom.ker φb).map (algebraMap Pb (Localization.AtPrime 𝔫')) := by
    apply le_antisymm _ (Ideal.map_mono hkerφψ)
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap Pb (Localization.AtPrime 𝔫') (1 - t)) :=
      IsLocalization.map_units (Localization.AtPrime 𝔫') ⟨1 - t, show 1 - t ∈ 𝔫'.primeCompl from h1t⟩
    have := Ideal.mem_map_of_mem (algebraMap Pb (Localization.AtPrime 𝔫')) (hkψ x hx)
    rw [map_mul] at this
    exact (Ideal.mul_unit_mem_iff_mem _ hu).1 this

  haveI : Module.Finite kb (Fin n → C) := Module.Finite.equiv σ.toLinearEquiv
  haveI : Module.Finite kb C :=
    Module.Finite.of_surjective (Pi.evalAlgHom kb (fun _ : Fin n => C) j).toLinearMap (Function.surjective_eval j)
  have hXq : ∀ a ∈ IC, MvPolynomial.aeval (fun _ : Fin r => (0 : kb)) a = 0 := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => MvPolynomial.aeval (fun _ : Fin r => (0 : kb)) a = 0) ?_ (map_zero _) ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩
      rw [map_pow, MvPolynomial.aeval_X, zero_pow (by have := (hq i).1; omega)]
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro c x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  let ev : C →ₐ[kb] kb := Ideal.Quotient.liftₐ IC (MvPolynomial.aeval fun _ : Fin r => (0 : kb)) hXq
  have hnil : ∀ x : C, IsNilpotent (x - algebraMap kb C (ev x)) := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change IsNilpotent (Ideal.Quotient.mk IC f - algebraMap kb C (MvPolynomial.aeval (fun _ : Fin r => (0 : kb)) f))
    induction f using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.aeval_C]; exact ⟨1, by rw [pow_one, sub_eq_zero]; rfl⟩
    | add f g hf hg =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact Commute.isNilpotent_add (Commute.all _ _) hf hg
    | mul_X f i hf =>
      rw [map_mul, map_mul, MvPolynomial.aeval_X, mul_zero, map_zero, sub_zero]
      exact Commute.isNilpotent_mul_left (Commute.all _ _)
        ⟨q i, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span ⟨i, rfl⟩⟩
  haveI : Nontrivial C := ⟨⟨0, 1, fun h => (zero_ne_one (α := kb)) (by simpa using congrArg ev h)⟩⟩
  haveI : IsLocalRing C := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
    by_cases hc : ev x = 0
    · right
      have : 1 - x = 1 + (-(x - algebraMap kb C (ev x))) := by rw [hc, map_zero, sub_zero, ← sub_eq_add_neg]
      rw [this]; exact (hnil x).neg.isUnit_one_add
    · left
      have hu : IsUnit (algebraMap kb C (ev x)) := (Ne.isUnit hc).map _
      obtain ⟨u, hu'⟩ := hu
      have : x = u * (1 + ↑u⁻¹ * (x - algebraMap kb C (ev x))) := by
        rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hu', add_sub_cancel]
      rw [this]
      exact (Units.isUnit u).mul ((Commute.isNilpotent_mul_left (Commute.all (↑u⁻¹ : C) (x - algebraMap kb C (ev x))) (hnil x)).isUnit_one_add)

  have hres : Function.Surjective (algebraMap kb (IsLocalRing.ResidueField C)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨ev x, ?_⟩
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal C) (algebraMap kb C (ev x)) = Ideal.Quotient.mk _ x
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← Ideal.neg_mem_iff, neg_sub, IsLocalRing.mem_maximalIdeal]
    exact (hnil x).not_isUnit

  obtain ⟨gb, hgb⟩ := Algebra.exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField kb C hres ⟨r, fun i => (MvPolynomial.X i : Pr) ^ q i, ⟨AlgEquiv.refl⟩⟩ N ψ hψs 𝔫' hkerψ𝔫
  rw [hlocψ, hkerb] at hgb

  obtain ⟨g, hg⟩ := Ideal.exists_map_localization_eq_span_of_baseChange_mvPolynomial k kb N N J 𝔫 h𝔫 𝔫' hover ⟨gb, hgb⟩

  have hgi : ∀ i, ∃ (ji : P) (si : 𝔫.primeCompl), ji ∈ J ∧
      g i * algebraMap P (Localization.AtPrime 𝔫) si = algebraMap P (Localization.AtPrime 𝔫) ji := by
    intro i
    have hmem : g i ∈ J.map (algebraMap P (Localization.AtPrime 𝔫)) := by rw [hg]; exact Ideal.subset_span ⟨i, rfl⟩
    obtain ⟨⟨⟨ji, hji⟩, si⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔫.primeCompl (Localization.AtPrime 𝔫)).1 hmem
    exact ⟨ji, si, hji, h⟩
  choose jg sg hjg hsg using hgi
  refine ⟨jg, hjg, ?_⟩
  rw [hg]
  apply le_antisymm
  · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
    have hu : IsUnit (algebraMap P (Localization.AtPrime 𝔫) (sg i)) := IsLocalization.map_units _ (sg i)
    rw [show g i = algebraMap P (Localization.AtPrime 𝔫) (jg i) * ↑hu.unit⁻¹ by
      rw [← hsg i, mul_assoc, IsUnit.mul_val_inv, mul_one]]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
    change algebraMap P (Localization.AtPrime 𝔫) (jg i) ∈ Ideal.span (Set.range g)
    rw [← hsg i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

end S_HopfAlgebra_exists_ker_map_localization_eq_span_of_surjective_mvPolynomial_of_isMaximal
end P2MW
export P2MW.S_HopfAlgebra_exists_ker_map_localization_eq_span_of_surjective_mvPolynomial_of_isMaximal (solution)
