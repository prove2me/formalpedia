-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:13.457018+00:00
-- url     : https://prove2.me/submissions/3763e34c-60c2-4abd-87dd-11cf160f0701

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres

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
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
namespace GlobalTheory.FibreLinInd
theorem _root_.solution {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) (w : W) (t : Sp K) (hw : q w = x t) :
    ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
end GlobalTheory.FibreLinInd
