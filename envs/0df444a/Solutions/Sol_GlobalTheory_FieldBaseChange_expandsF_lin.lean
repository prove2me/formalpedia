-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.expandsF_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:07.024228+00:00
-- url     : https://prove2.me/submissions/91d87439-dee8-457b-98ac-5fb9367c1060

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_lin
import Theorems.Thm_GlobalTheory_FieldBaseChange_expandsG_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {k : ℕ} {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (c : F) {t t' : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F))}
    {s s' : Fam D.toPre F k} (h : U.ExpandsF F k w t s) (h' : U.ExpandsF F k w t' s') :
    U.ExpandsF F k w (c • t + t' : SecOver (abelianBase A F) _) (c • s + s') := by
  obtain ⟨v, a, b⟩ := h
  obtain ⟨v', a', b'⟩ := h'
  have hπ : (U.genF F).left ≫ abelianBase A F = groupBase G F :=
    congrArg (fun q => q.left) (lift_fst _ _ : U.genF F ≫ fst _ _ = _)
  exact ⟨_, isoRelM_lin hπ c a a', expandsG_lin U F k c b b'⟩
end GlobalTheory.FieldBaseChange
