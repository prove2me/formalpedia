-- Prove2me | solution 1 for GlobalTheory.OppRad.matrix_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:16.5819+00:00
-- url     : https://prove2.me/submissions/feaa5157-aa97-46d3-8ef8-ad899d5f6926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_un_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.OppRad.un_val

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R V : Type} [Ring R] [Finite R] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ Rˣ V}
namespace GlobalTheory.OppRad
theorem _root_.solution {F n : Type} [Field F] [Fintype n] [DecidableEq n] (x : Matrix n n F) :
    ∃ y, x * y * x = x := by
  let f := Matrix.toLinAlgEquiv' x
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨r, hr⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨Matrix.toLinAlgEquiv'.symm (s ∘ₗ r), Matrix.toLinAlgEquiv'.injective ?_⟩
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  refine LinearMap.ext fun w => ?_
  have h1 : r (f w) = f.rangeRestrict w := LinearMap.congr_fun hr (f.rangeRestrict w)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict w))
  change f (s (r (f w))) = f w
  rw [h1]
  exact h2
end GlobalTheory.OppRad
