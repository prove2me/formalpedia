-- Prove2me | solution 1 for GlobalTheory.torsion_zero_count_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:34:21.230155+00:00
-- url     : https://prove2.me/submissions/b7c4d36c-7ef9-4327-9c74-e98f9a982062

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
import Theorems.Thm_GlobalTheory_TwistZero_mem_nonzeroLocus_iff
import Theorems.Thm_GlobalTheory_TwistZero_sval_eq_zero
import Theorems.Thm_GlobalTheory_TwistZero_ptSecT_translPt
import Theorems.Thm_GlobalTheory_TwistZero_exists_untwist
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionDivision_exists_div


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
theorem _root_.solution : Out.MulNSt → Out.SquareSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (b : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → (k : K) ≠ 0 → ∀ s : (lbPow P.L (N * d)).Sec, (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = b ∧ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (c : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → 1 ≤ d → (k : K) ≠ 0 → ∀ s : LB.Sec (Out.twistLB P.A P.L (N * d) c), (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) := by
  intro hmul hsq hZ K _ _ P N d k c hg hN hd hk s hs
  have hq : 2 ≤ N * d := le_trans (by omega) (Nat.mul_le_mul hN hd)
  obtain ⟨b, rfl⟩ := SectionDivision.exists_div hmul P c (N * d) (by omega)
  obtain ⟨s', hs'⟩ := TwistZero.exists_untwist hsq P (N * d) hq b s
  have hs0 : ∃ j, s'.f j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, hj⟩ := hs
    refine hj (sec_ext_val P.isLB (s := s) (s' := secZero _) (fun y J hJ => ?_) j)
    obtain ⟨u, hu⟩ := hs' _ (𝟙 _) y J hJ
    exact ((Units.mul_left_eq_zero u).1 (hu.symm.trans (TwistZero.sval_eq_zero s' hcon _ y hJ))).trans
      (TwistZero.sval_eq_zero (secZero _) (fun _ => rfl) _ y hJ).symm
  have loc : ∀ x : baseOver (Sp K) ⟶ P.A,
      (ptSecT P.A x).left ⁻¹ᵁ nonzeroLocus s = (b * x).left ⁻¹ᵁ nonzeroLocus s' := by
    intro x
    ext z
    choose J hJ using fun ψ : (baseOver (Sp K)).left ⟶ P.A.left => exists_chart P.isLB (ψ z)
    obtain ⟨u, hu⟩ := hs' _ (ptSecT P.A x).left z J hJ
    rw [← Over.comp_left, TwistZero.ptSecT_translPt] at hu
    exact (TwistZero.mem_nonzeroLocus_iff s _ z hJ).trans
      ((Units.isUnit_mul_units _ u).symm.trans
        ((congrArg IsUnit hu).symm.to_iff.trans (TwistZero.mem_nonzeroLocus_iff s' _ z hJ).symm))
  refine le_of_eq_of_le (Nat.card_congr ((Equiv.mulLeft b).subtypeEquiv fun x => ?_))
    (hZ K P N d k (b ^ k) hg hN hk s' hs0)
  rw [Equiv.coe_mulLeft, loc x, mul_pow, mul_eq_left]
end GlobalTheory
