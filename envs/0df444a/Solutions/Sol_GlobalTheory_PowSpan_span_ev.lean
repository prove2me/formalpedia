-- Prove2me | solution 1 for GlobalTheory.PowSpan.span_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:42.810878+00:00
-- url     : https://prove2.me/submissions/b1fe2d91-4c5c-4348-aed7-dce8a75bc4dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsSpanExternalPowersOfBoxSpan
import Theorems.Thm_GlobalTheory_PowSpan_gs_cst
import Theorems.Thm_GlobalTheory_PowSpan_sum_mul_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.PowSpan
variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
namespace GlobalTheory.PowSpan
theorem _root_.solution (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (hL : L.IsLB)
    (hb : ∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))),
      ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart L (K := Fin 0) (fun c => (Out.powPr A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    have hF : FormEq (K := Fin (n + 1)) (K' := Fin n ⊕ PUnit) (fun c => (Out.powPr A c).left) (fun _ => t)
        (Sum.elim (fun k => (snd A (Out.powObj A n)).left ≫ (Out.powPr A k).left)
          (fun _ => (fst A (Out.powObj A n)).left))
        (Sum.elim (fun _ => t) (fun _ => t)) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type, mul_comm]
      exact congrArg₂ (· * ·) rfl (Fintype.prod_unique
        (fun _ : PUnit => h (fst A (Out.powObj A n)).left ^ t)).symm
    obtain ⟨v, hv⟩ := exists_sec hL hF s
    obtain ⟨a, ha⟩ := hb (Out.powObj A n) (Fin n) (fun c => (Out.powPr A c).left) (fun _ => t) v
    choose q hq using fun i => ih (a i)
    refine ⟨fun I => q (I 0) (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₂ : (r ≫ (snd A (Out.powObj A n)).left) ≫ (Out.powObj A n).hom =
        r ≫ (Out.powObj A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd A (Out.powObj A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hq i Z _ z J hJ) rfl).trans ?_
    exact sum_mul_cons (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr A d).left) z (L.U (J (r ≫ (Out.powPr A d).left)))
          ((b j).f (J (r ≫ (Out.powPr A d).left)))) q
end GlobalTheory.PowSpan
