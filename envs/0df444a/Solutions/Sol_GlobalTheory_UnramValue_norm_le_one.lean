-- Prove2me | solution 1 for GlobalTheory.UnramValue.norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:31.67472+00:00
-- url     : https://prove2.me/submissions/2d60ee5f-b07e-4b26-949e-ffc4b662f962

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_norm_algebraMap_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {m : ℕ} (hm : 0 < m) {y : Om l} (hy : y ∈ rootRing l m) : ‖y‖ ≤ 1 := by
  unfold rootRing at hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    have hx' : x ^ m = 1 := hx
    have h1 : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx', norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h1)
  | algebraMap r => rw [norm_algebraMap_int]; exact PadicInt.norm_le_one r
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy
end GlobalTheory.UnramValue
