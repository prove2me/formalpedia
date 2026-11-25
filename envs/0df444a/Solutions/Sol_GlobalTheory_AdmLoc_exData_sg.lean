-- Prove2me | solution 1 for GlobalTheory.AdmLoc.exData_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:31.633833+00:00
-- url     : https://prove2.me/submissions/0244994d-2886-43a4-894a-05e5072e1fe5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
namespace GlobalTheory.AdmLoc
theorem _root_.solution (i : ZMod 2) : exData.sg 41 i = 1 := by
  have h : ∑' j : ℕ, ((60 : ℕ) : ℝ) / ((41 : ℕ) : ℝ) ^ (j + 1) = 3 / 2 := by
    have h1 : ∀ j : ℕ, ((60 : ℕ) : ℝ) / ((41 : ℕ) : ℝ) ^ (j + 1) = (60 / 41) * (1 / 41 : ℝ) ^ j := by
      intro j; push_cast; rw [one_div, inv_pow]; field_simp; ring
    simp_rw [h1]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  change ⌊∑' j : ℕ, ((60 : ℕ) : ℝ) / ((41 : ℕ) : ℝ) ^ (j + 1)⌋₊ = 1
  rw [h, Nat.floor_eq_iff (by norm_num)]
  norm_num
end GlobalTheory.AdmLoc
