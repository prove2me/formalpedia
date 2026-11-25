-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.prod_bottomRows_eq_prodFrom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:14:03.645019+00:00
-- url     : https://prove2.me/submissions/61c05c25-93b1-46a1-9eb5-430d7b7a0ee7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bottomRows_injective
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_bottomRows_eq
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (t : Fin n → Fˣ) (k : Fin n) :
    ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) = prodFrom t (n - (k.val + 1)) := by
  classical
  unfold prodFrom
  rw [← Finset.prod_image (s := Finset.univ) (g := bottomRows k)
    (fun x _ y _ h => bottomRows_injective k h) (f := fun x => (t x : F))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨a, rfl⟩
    simp [bottomRows]
  · intro hx
    exact exists_bottomRows_eq (a := ⟨0, Nat.succ_pos _⟩) (by rw [Fin.le_def]; simp only [bottomRows]; omega)
end GroundTheory.Automorphic.Whittaker
