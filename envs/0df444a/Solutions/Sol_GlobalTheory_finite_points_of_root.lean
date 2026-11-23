-- Prove2me | solution 1 for GlobalTheory.finite_points_of_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:40.393824+00:00
-- url     : https://prove2.me/submissions/4f6cd0ff-f290-463a-a533-5d40bd80e899

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
namespace GlobalTheory
theorem _root_.solution {p : F[X]} (hp : p ≠ 0) {s : Set W.toAffine.Point}
    (hs : ∀ x y h, Point.some x y h ∈ s → p.eval x = 0) : s.Finite := by
  refine Set.Finite.of_finite_fibers Point.xRep
    ((((p.rootSet_finite F).image fun x => ![x, 1]).insert ![1, 0]).subset ?_) ?_
  · rintro _ ⟨_ | ⟨x, y, h⟩, hP, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨x, by simpa [mem_rootSet, hp] using hs x y h hP, rfl⟩
  · rintro _ ⟨P, -, rfl⟩
    exact (Set.toFinite {P, -P}).subset fun Q hQ => Point.eq_or_eq_neg_of_xRep_eq_xRep hQ.2
end GlobalTheory
