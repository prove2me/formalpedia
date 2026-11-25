-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.rowEigSmall_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:45.776193+00:00
-- url     : https://prove2.me/submissions/7e9ebd2c-6ccc-4f37-88da-22c384d49dc3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_SmallRowEigenvalues
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmallBlockEigenvalues_one_lt_normV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
theorem _root_.solution {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N)
    (h : ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
      ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
        ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)) :
    RowEigSmall N A := by
  intro i σ hσ w hw hu α hα
  have hrt : R.r < R.t := by have := R.rank_add_five_le; unfold Ranks.r; omega
  refine lt_of_le_of_lt (h i σ hσ w hw hu α hα) ?_
  have h1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have h2 : (R.r : ℝ) < (R.t : ℝ) := by exact_mod_cast hrt
  exact Real.rpow_lt_rpow_of_exponent_lt h1 (by linarith)
end GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
