-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.eq_zero_of_rationalPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:51.836694+00:00
-- url     : https://prove2.me/submissions/8ec9d637-4894-492e-af60-54205681f4c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
namespace GlobalTheory.SS.WtRat
theorem _root_.solution {k : Type} [Field k] [IsAlgClosed k] {P : Over (Sp k)}
    [Smooth P.hom] {W : P.left.Opens} (d : Γ(P.left, W))
    (h : ∀ (z : 𝟙_ (Over (Sp k)) ⟶ P) (x : (𝟙_ (Over (Sp k))).left),
      z.left x ∉ P.left.basicOpen d) : d = 0 := by
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced (S := Spec (.of k)) P.hom
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec (.of k)) P.hom
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  have hne' : ((P.left.basicOpen d : P.left.Opens) : Set P.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h' => hne (TopologicalSpace.Opens.ext h')
  obtain ⟨x, hxd, hx⟩ := nonempty_inter_closedPoints hne' (P.left.basicOpen d).isOpen.isLocallyClosed
  refine h (Over.homMk (pointOfClosedPoint (K := k) P.hom x hx)
    (pointOfClosedPoint_comp (K := k) P.hom x hx)) (IsLocalRing.closedPoint k) ?_
  have e := pointOfClosedPoint_apply (K := k) P.hom x hx (IsLocalRing.closedPoint k)
  exact e.symm ▸ hxd
end GlobalTheory.SS.WtRat
