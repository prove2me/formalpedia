-- Prove2me | solution 1 for GlobalTheory.TorsExists.exists_mul_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:58.296693+00:00
-- url     : https://prove2.me/submissions/3380e327-53f1-42e3-947f-d48adb3d0cf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsExists
theorem _root_.solution {K : Type} [Field K] (D : Matrix Ix Ix K) : ∃ G : Matrix Ix Ix K, D * G * D = D := by
  set f := Matrix.toLin' D with hf
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := LinearMap.exists_extend s
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', ← hf]
  refine LinearMap.ext fun v => ?_
  have h1 : g (f v) = s (f.rangeRestrict v) := by rw [← hg]; rfl
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict v))
  simp only [LinearMap.comp_apply, h1]
  exact h2
end GlobalTheory.TorsExists
