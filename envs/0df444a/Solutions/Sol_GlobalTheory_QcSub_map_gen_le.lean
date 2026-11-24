-- Prove2me | solution 1 for GlobalTheory.QcSub.map_gen_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:44:59.547968+00:00
-- url     : https://prove2.me/submissions/c30e4b7e-636c-4526-a9ca-21ab659d9c6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Theorems.Thm_GlobalTheory_QcSub_res_mem_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite
open GlobalTheory GlobalTheory.QcSub
variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
namespace GlobalTheory.QcSub
theorem _root_.solution {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V))) :
    (gen F α h T).map (F.map (homOfLE h').op).hom ≤ gen F α (h'.trans h) T := by
  rw [gen, RingHom.map_closure, Subring.closure_le]
  rintro _ ⟨y, (⟨r, rfl⟩ | ⟨t, ht, rfl⟩), rfl⟩
  · have := congr($(α.naturality (homOfLE h').op).hom r)
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    exact algebraMap_mem_gen F α _ T _
  · rw [← CommRingCat.comp_apply, ← F.map_comp]
    exact res_mem_gen F α _ T ht
end GlobalTheory.QcSub
