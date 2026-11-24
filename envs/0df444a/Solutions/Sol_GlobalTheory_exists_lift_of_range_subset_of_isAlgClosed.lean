-- Prove2me | solution 1 for GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:45.90794+00:00
-- url     : https://prove2.me/submissions/c1f2cb36-fbae-4a08-a4ff-46f29410fb48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftAlgebraicallyClosedPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f]
      (k : Type) [Field k] [IsAlgClosed k]
      (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
      ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by
  intro X Y f _ k _ _ y hr
  obtain ⟨x₀, hx₀⟩ := hr ⟨IsLocalRing.closedPoint k, rfl⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := y) x₀
    (IsLocalRing.closedPoint k) hx₀
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd f y)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (X := (Limits.pullback f y : Scheme))
    (Z := Set.univ) ⟨z, trivial⟩ isClosed_univ.isLocallyClosed
  have hc' : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd f y) c hc' ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]
end GlobalTheory
