-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.sec_neg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:08:53.268451+00:00
-- url     : https://prove2.me/submissions/af987af7-f56a-405a-be77-dacd09b2041f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_Model_eq_zero_of_mul_ratio_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}
namespace GlobalTheory.ProjSpace.Model
theorem _root_.solution (k : ℕ) (s : (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).Sec)
    (i : PUnit → Fin (N + 2)) : s.f i = 0 := by
  obtain ⟨j, hj⟩ := exists_ne (i PUnit.unit)
  have hUi := On_U R (N + 1) (-((k + 1 : ℕ) : ℤ)) i
  have hUj := On_U R (N + 1) (-((k + 1 : ℕ) : ℤ)) (fun _ => j)
  have hc := s.compat i (fun _ => j)
  rw [On_g, zpow_neg, zpow_natCast] at hc
  have h0 := eq_zero_of_mul_ratio_pow hj k (inf_le_left.trans hUi.le) (inf_le_right.trans hUj.le)
    (by rw [hUi, hUj]) (resG _ hUi.ge (s.f i)) (resG _ hUj.ge (s.f fun _ => j)) (by
      have e1 : resG _ (inf_le_left.trans hUi.le : _ ⊓ (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).U (fun _ => j) ≤ _)
          (resG _ hUi.ge (s.f i)) = resG _ inf_le_left (s.f i) := rfl
      have e2 : resG _ (inf_le_right.trans hUj.le : (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).U i ⊓ _ ≤ _)
          (resG _ hUj.ge (s.f fun _ => j)) = resG _ inf_le_right (s.f fun _ => j) := rfl
      rw [e1, e2]
      erw [hc]
      rw [← val_ratioUnit (hj := inf_le_right.trans hUj.le), ← Units.val_pow_eq_pow_val, mul_right_comm,
        Units.inv_mul, one_mul])
  have e : s.f i = resG _ hUi.le (resG _ hUi.ge (s.f i)) := rfl
  rw [e, h0, map_zero]
end GlobalTheory.ProjSpace.Model
