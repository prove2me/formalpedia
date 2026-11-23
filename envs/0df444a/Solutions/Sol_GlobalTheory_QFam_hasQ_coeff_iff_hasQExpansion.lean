-- Prove2me | solution 1 for GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:21.636337+00:00
-- url     : https://prove2.me/submissions/064d79ab-3fe8-4e22-9c33-0688bd4256b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Theorems.Thm_GlobalTheory_QFam_hasQ_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
namespace GlobalTheory.QFam
namespace _root_.GlobalTheory.QFam
theorem _root_.solution (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) :
    _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n φ) ↔
      _root_.GlobalTheory.HasQExpansion (N : ℝ) f φ := by
  rw [_root_.GlobalTheory.QFam.hasQ_iff]
  unfold _root_.GlobalTheory.HasQExpansion
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast]
end _root_.GlobalTheory.QFam
end GlobalTheory.QFam
