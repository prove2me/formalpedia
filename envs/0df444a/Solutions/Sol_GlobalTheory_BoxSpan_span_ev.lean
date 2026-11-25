-- Prove2me | solution 1 for GlobalTheory.BoxSpan.span_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:07:28.913267+00:00
-- url     : https://prove2.me/submissions/d5594f59-d7fb-41fa-8bfe-a2536a475de1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsBasisSpanPowObjSections
import Theorems.Thm_GlobalTheory_BoxSpan_gs_cst
import Theorems.Thm_GlobalTheory_BoxSpan_isProper_powObj
import Theorems.Thm_GlobalTheory_BoxSpan_exists_coords
import Theorems.Thm_GlobalTheory_BoxSpan_sum_mul_sum_cons
import Theorems.Thm_GlobalTheory_T_section_lin_comb_fiber_product_separated
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
open GlobalTheory GlobalTheory.BoxSpan
variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
namespace GlobalTheory.BoxSpan
theorem _root_.solution (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m) (hb : IsBasis x b) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))),
      ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj x.P.A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart x.P.L (K := Fin 0) (fun c => (Out.powPr x.P.A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj x.P.A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp K)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj x.P.A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    haveI := x.P.isAb.proper
    haveI := isProper_powObj x.P.A x.P.isAb n
    have hF : FormEq (K := Fin (n + 1)) (K' := PUnit ⊕ Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))
        (Sum.elim (fun _ => (fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left)
          (fun k => (snd x.P.A (Out.powObj x.P.A n)).left ≫ (Out.powPr x.P.A k).left))
        (Sum.elim (fun _ => (m : ℤ)) (fun _ => (m : ℤ))) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type]
      exact congrArg₂ (· * ·) (Fintype.prod_unique
        (fun _ : PUnit => h ((fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left) ^ (m : ℤ))).symm rfl
    obtain ⟨v, hv⟩ := exists_sec x.P.isLB hF s
    obtain ⟨k, a₁, a₂, ha⟩ := (GlobalTheory.T.section_lin_comb_fiber_product_separated K x.P.A.left x.P.L x.P.isLB x.P.A (Out.powObj x.P.A n) PUnit (Fin n)
      (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))).1 v
    choose c hc using fun i => exists_coords x b hb (a₁ i)
    choose q hq using fun i => ih (a₂ i)
    refine ⟨fun I => ∑ i, c i (I 0) * q i (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₁ : (r ≫ (fst x.P.A (Out.powObj x.P.A n)).left) ≫ x.P.A.hom = r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (fst x.P.A (Out.powObj x.P.A n))))
    have e₂ : (r ≫ (snd x.P.A (Out.powObj x.P.A n)).left) ≫ (Out.powObj x.P.A n).hom =
        r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd x.P.A (Out.powObj x.P.A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hc i Z _ z J hJ) (hq i Z _ z J hJ)).trans ?_
    exact sum_mul_sum_cons (congrArg (ev · z) e₁) (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr x.P.A d).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A d).left)))
          ((b j).f (J (r ≫ (Out.powPr x.P.A d).left)))) c q
end GlobalTheory.BoxSpan
