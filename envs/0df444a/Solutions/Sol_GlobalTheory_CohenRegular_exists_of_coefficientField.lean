-- Prove2me | solution 1 for GlobalTheory.CohenRegular.exists_of_coefficientField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:38:38.977251+00:00
-- url     : https://prove2.me/submissions/8dc9e1c6-5412-4760-8079-595dbdfb625a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCoefficientFieldOfCharZero
import Theorems.Thm_GlobalTheory_CohenStructure_finite_quotient_of_pow_le
import Theorems.Thm_GlobalTheory_CohenStructure_injective_of_ringKrullDim_eq
import Theorems.Thm_GlobalTheory_CohenStructure_isAdicComplete_mvPowerSeries
import Theorems.Thm_GlobalTheory_CohenStructure_isDomain_mvPowerSeries
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finite_quotient_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_quotient_of_pow_le
import Theorems.Thm_GlobalTheory_FormalIsogeny_isRegularLocalRing_mvPowerSeries
import Theorems.Thm_GlobalTheory_FormalIsogeny_mem_maximalIdeal_iff_constantCoeff
import Theorems.Thm_GlobalTheory_FormalIsogeny_ringKrullDim_mvPowerSeries
import Theorems.Thm_GlobalTheory_algHom_sub_constantCoeff_mem
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_exists_systemOfParameters_insert
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CohenRegular
open MvPowerSeries GlobalTheory.CohenStructure
namespace GlobalTheory.CohenRegular
theorem _root_.solution (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] (Λ : Subring S) (hF : IsField Λ)
    (h1 : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
      Function.Injective i ∧ i.Finite := by
  by_cases hm : maximalIdeal S = ⊥
  · letI := (isField_iff_maximalIdeal_eq.2 hm).toField
    exact ⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  letI := hF.toField
  obtain ⟨n, x₀, hx₀, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S a ha0 ha
  let x : Fin (n + 1) → S := Fin.cons a x₀
  have hx : ∀ i, x i ∈ maximalIdeal S := fun i => Fin.cases ha hx₀ i
  let A := MvPowerSeries (Fin (n + 1)) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ (n + 1)
  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  have : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  have hA := isAdicComplete_mvPowerSeries Λ (n + 1)
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rw [← Fin.range_cons]
    rintro _ ⟨i, rfl⟩
    show x i ∈ _
    rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
    exact Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, FormalIsogeny.isRegularLocalRing_mvPowerSeries Λ (Fin (n + 1)),
    algebraMap A S, injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
end GlobalTheory.CohenRegular
