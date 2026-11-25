-- Prove2me | solution 1 for GlobalTheory.CohenRegular.exists_of_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:21.200887+00:00
-- url     : https://prove2.me/submissions/ec539e9a-31d2-4d17-ac91-284483013cf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCoefficientFieldOfCharZero
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_coeffSubring
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
import Theorems.Thm_GlobalTheory_PBasis_exists_pBasis
import Theorems.Thm_GlobalTheory_algHom_sub_constantCoeff_mem
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_exists_systemOfParameters_insert
import Theorems.Thm_GlobalTheory_isDVR_of_closed_subring_principal
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
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] {p : ℕ} (hp : p.Prime)
    (h0 : (p : S) ∈ maximalIdeal S) (hp0 : (p : S) ≠ 0) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
      Function.Injective i ∧ i.Finite := by
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)
  obtain ⟨Λ, h1, h2, h3⟩ := CoeffSubring.exists_coeffSubring hp hp0 h0 hB hB'
  obtain ⟨_, hm, hΛ⟩ := GlobalTheory.isDVR_of_closed_subring_principal S Λ p (by simpa using hp0) (by simpa using h0) hc h1 h2 h3
  obtain ⟨n, x, hx, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S p hp0 h0
  let A := MvPowerSeries (Fin n) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ n
  have hA := isAdicComplete_mvPowerSeries Λ n
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hm, Ideal.mem_span_singleton] at h5
    obtain ⟨c, hc⟩ := h5
    have h6 : algebraMap Λ S (constantCoeff g) ∈ maximalIdeal S := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ h0
    have h7 := add_mem h4 h6
    rwa [sub_add_cancel] at h7
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · rw [← map_natCast (algebraMap A S)]
      refine Ideal.mem_map_of_mem _ (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_)
      rw [map_natCast, hm]
      exact Ideal.mem_span_singleton_self _
    · rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
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
  refine ⟨A, inferInstance, FormalIsogeny.isRegularLocalRing_mvPowerSeries Λ (Fin n),
    algebraMap A S, injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
    Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
  norm_cast
end GlobalTheory.CohenRegular
