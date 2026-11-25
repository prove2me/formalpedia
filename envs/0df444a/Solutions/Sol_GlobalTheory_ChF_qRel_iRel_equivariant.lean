-- Prove2me | solution 1 for GlobalTheory.ChF.qRel_iRel_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:54:09.528409+00:00
-- url     : https://prove2.me/submissions/5042fceb-e09b-4f42-98e9-0acf81ab535d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AppTopCharUnitOfTorusEndOf
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem appTop_charUnit_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : Out.TorusEndOf X h t) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, ht χ]
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (k : ℕ) (a : OE) (S : Type) [CommRing S] [Algebra R S], (∀ z y, QRel (U.gt k) S z y → QRel (U.gt k) S (z ≫ io.act a) (y ≫ oD.onB.act a)) ∧ ∀ χ χ' z, (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → IRel (U.gt k) S χ z → IRel (U.gt k) S χ' (z ≫ io.act a) := by
  intro R _ _ I D A G _ _ U OE _ _ _ io oD oA hl k a S _ _
  have hG : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (Out.fstG I k G).left =
      (Out.fstG I k G).left ≫ (io.act a).left :=
    GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (io.act a)
  refine ⟨?_, ?_⟩
  · rintro z y ⟨w, h1, h2⟩
    refine ⟨w ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left, ?_, ?_⟩
    · rw [Over.comp_left, ← h1]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hG).trans (Category.assoc _ _ _).symm)
    · have hB : ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left ≫
          (D.toPre.prBe I k).left = (D.toPre.prBe I k).left ≫ (oD.onB.act a).left :=
        GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (oD.onB.act a)
      have hq : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).q.left =
          (U.gt k).q.left ≫ ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left :=
        congrArg (·.left) (hl.q_lin k a)
      have hp : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).pG.left =
          (U.gt k).pG.left ≫ (oD.onB.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.toPre.prBe I k).left) hq).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).q.left ≫ ·) hB).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left (g := oD.onB.act a), ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)
  · rintro χ χ' z hχ ⟨w, h1, h2⟩
    obtain ⟨t, ht, hi⟩ := hl.i_lin k a
    refine ⟨w ≫ t.left, fun x => ?_, ?_⟩
    · rw [hχ, ← h1, ← appTop_charUnit_of_torusEndOf ht x, Scheme.Hom.comp_appTop]
      rfl
    · have hi' : (U.gt k).i.left ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left =
          t.left ≫ (U.gt k).i.left := congrArg (·.left) hi
      have hp : t.left ≫ (U.gt k).i.left ≫ (Out.fstG I k G).left =
          ((U.gt k).i.left ≫ (Out.fstG I k G).left) ≫ (io.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hi'.symm).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).i.left ≫ ·) hG).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left, ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)
end GlobalTheory.ChF
