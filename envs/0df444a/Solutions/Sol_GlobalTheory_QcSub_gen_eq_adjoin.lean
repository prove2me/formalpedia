-- Prove2me | solution 1 for GlobalTheory.QcSub.gen_eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:23.557802+00:00
-- url     : https://prove2.me/submissions/f5f1ac86-7eab-4f5d-acfc-0648d42a660a

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
theorem _root_.solution {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) :
    letI := (α.app (op W)).hom.toAlgebra
    gen F α h T = (Algebra.adjoin Γ(X, W) ((F.map (homOfLE h).op).hom '' T)).toSubring := by
  letI := (α.app (op W)).hom.toAlgebra
  rw [Algebra.adjoin_eq_ring_closure]
  rfl
end GlobalTheory.QcSub
