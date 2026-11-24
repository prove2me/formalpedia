-- Prove2me | solution 1 for GlobalTheory.DetBound.val_bounds_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:11:00.32593+00:00
-- url     : https://prove2.me/submissions/ec15b6f6-bccb-44d4-9800-48e225211cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (l : ℕ) (hl : (l : O) ≠ 0) (hlm : (l : O) ∈ IsLocalRing.maximalIdeal O) (u D : O) (n : ℕ)
    (hD : D ≠ 0) (hu : u ∣ D ^ n) :
    0 ≤ val_vp O l (algebraMap O K u) ∧ val_vp O l (algebraMap O K u) ≤ n • val_vp O l (algebraMap O K D) := by
  obtain ⟨w, hw⟩ := hu
  have hDn : D ^ n ≠ 0 := pow_ne_zero _ hD
  have hu0 : u ≠ 0 := by rintro rfl; exact hDn (by simp [hw])
  have hw0 : w ≠ 0 := by rintro rfl; exact hDn (by simp [hw])
  have hinj := IsFractionRing.injective O K
  have hne : ∀ a : O, a ≠ 0 → algebraMap O K a ≠ 0 := fun a ha => (map_ne_zero_iff _ hinj).2 ha
  have hVne : ∀ a : O, a ≠ 0 →
      (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K a) ≠ 0 := by
    intro a ha; simpa using hne a ha
  have key : ∀ a : O, a ≠ 0 → 0 ≤ ord_vw O (algebraMap O K a) := by
    intro a ha
    unfold ord_vw
    rw [neg_nonneg, WithZero.log_le_iff_le_exp (hVne a ha), WithZero.exp_zero]
    exact HeightOneSpectrum.valuation_le_one _ a
  have hmul : ord_vw O (algebraMap O K (D ^ n)) = ord_vw O (algebraMap O K u) + ord_vw O (algebraMap O K w) := by
    unfold ord_vw
    rw [hw, map_mul, Valuation.map_mul, WithZero.log_mul (hVne u hu0) (hVne w hw0), neg_add]
  have hpow : ord_vw O (algebraMap O K (D ^ n)) = n * ord_vw O (algebraMap O K D) := by
    unfold ord_vw
    rw [map_pow, Valuation.map_pow, WithZero.log_pow, nsmul_eq_mul, mul_neg]
  have hlK : (l : K) = algebraMap O K (l : O) := (map_natCast _ _).symm
  have hlpos : 0 < ord_vw O (l : K) := by
    rw [hlK]
    refine lt_of_le_of_ne (key _ hl) ?_
    intro h4
    have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K (l : O)) < 1 := by
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hlm
    unfold ord_vw at h4
    have := WithZero.exp_log (hVne _ hl)
    rw [neg_eq_zero.1 h4.symm, WithZero.exp_zero] at this
    exact h1.ne this.symm
  have hw' := key w hw0
  have hu' := key u hu0
  rw [val_vp, if_neg (hne u hu0), val_vp, if_neg (hne D hD)]
  have hL : (0 : ℚ) < (ord_vw O (l : K) : ℚ) := by exact_mod_cast hlpos
  refine ⟨WithTop.coe_nonneg.2 (div_nonneg (by exact_mod_cast hu') hL.le), ?_⟩
  rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hL.le
  have : ord_vw O (algebraMap O K u) ≤ n * ord_vw O (algebraMap O K D) := by omega
  exact_mod_cast this
end GlobalTheory.DetBound
