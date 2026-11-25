-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_logDeriv_eq_untopD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:38.178842+00:00
-- url     : https://prove2.me/submissions/45b9af1b-452d-47c0-9d70-0394af2c7cec

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_congr
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_zero_of_analyticAt
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_logDeriv


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
theorem _root_.solution {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    residue (logDeriv f) z = (((meromorphicOrderAt f z).untopD 0 : ℤ) : ℂ) := by
  by_cases htop : meromorphicOrderAt f z = ⊤
  · rw [htop, WithTop.untopD_top, Int.cast_zero]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hmer : MeromorphicAt (logDeriv f) z := by
      have : logDeriv f = fun w ↦ deriv f w / f w := rfl
      rw [this]
      exact hf.deriv.div hf
    have h0 : logDeriv f =ᶠ[𝓝[≠] z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [htop] with w hw
      simp [logDeriv_apply, hw]
    rw [residue_congr hmer h0]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hn, WithTop.untopD_coe]
    exact residue_logDeriv hf hn.symm
end GroundTheory.Global.Elliptic
