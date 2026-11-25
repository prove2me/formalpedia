-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.toNat_neg_untopD_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:19.257165+00:00
-- url     : https://prove2.me/submissions/fd717fd4-f9b6-4024-bafb-8adbbe26208f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_meromorphicOrderAt_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) (c : ℂ) :
    (-(meromorphicOrderAt (fun w ↦ f w - c) z).untopD 0).toNat =
      (-(meromorphicOrderAt f z).untopD 0).toNat := by
  have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
  have e : (fun w ↦ f w - c) = f + fun _ ↦ -c := by
    funext w; simp [sub_eq_add_neg]
  have hc0 : 0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicOrderAt_nonneg
  rw [e]
  by_cases hneg : meromorphicOrderAt f z < 0
  · rw [meromorphicOrderAt_add_eq_left_of_lt hc (hneg.trans_le hc0)]
  · push Not at hneg
    have h1 : 0 ≤ meromorphicOrderAt (f + fun _ ↦ -c) z :=
      le_trans (le_min hneg hc0) (meromorphicOrderAt_add hf hc)
    have key : ∀ o : WithTop ℤ, 0 ≤ o → (-(o.untopD 0)).toNat = 0 := by
      intro o ho
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (0 : ℤ) ≤ n := by exact_mod_cast ho
        omega
    rw [key _ h1, key _ hneg]
end GroundTheory.Global.Elliptic
