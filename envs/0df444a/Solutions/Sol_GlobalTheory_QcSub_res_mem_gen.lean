-- Prove2me | solution 1 for GlobalTheory.QcSub.res_mem_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:09.516004+00:00
-- url     : https://prove2.me/submissions/ee313b84-d7b1-4397-863d-c3c6fd58a93e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl

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
theorem _root_.solution {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) {t : F.obj (op V)}
    (ht : t ∈ T) : (F.map (homOfLE h).op).hom t ∈ gen F α h T :=
  Subring.subset_closure (Or.inr ⟨t, ht, rfl⟩)
end GlobalTheory.QcSub
