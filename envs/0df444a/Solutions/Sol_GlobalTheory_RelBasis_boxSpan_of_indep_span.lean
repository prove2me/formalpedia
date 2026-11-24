-- Prove2me | solution 1 for GlobalTheory.RelBasis.boxSpan_of_indep_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:55:14.712712+00:00
-- url     : https://prove2.me/submissions/f7d56310-174a-4855-8446-368d76e61d44

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsSpanTwistedOfIndepSpan
import Theorems.Thm_GlobalTheory_RelBasis_comb_comp
import Theorems.Thm_GlobalTheory_RelBasis_gs_comp
import Theorems.Thm_GlobalTheory_RelBasis_gs_eq_gsHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.RelBasis
namespace GlobalTheory.RelBasis
theorem _root_.solution (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t))
    (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (hL : L.IsLB) (H : ∀ W : T.Opens, IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W) :
    BoxSpan b p₁ p₂ := by
  intro K _ φ ε s
  have mem : ∀ (j : K → L.ι) (i : L.ι) (y : Y), p₁ y ∈ LB.wchart L φ j → p₂ y ∈ L.U i →
      y ∈ LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)) := by
    intro j i y h₁ h₂
    refine Set.mem_iInter.2 ?_
    rintro (k | k)
    exacts [Set.mem_iInter.1 h₁ k, h₂]
  have tr : ∀ (j j' : K → L.ι) (i i' : L.ι) (y : Y), p₁ y ∈ LB.wchart L φ j → p₂ y ∈ L.U i →
      p₁ y ∈ LB.wchart L φ j' → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)))
          (s.f (Sum.elim j (fun _ => i))) =
        (trF φ ε p₁ y j j').val * (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val *
        gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j' (fun _ => i')))
          (s.f (Sum.elim j' (fun _ => i'))) := by
    intro j j' i i' y h₁ h₂ h₁' h₂'
    rw [sec_trans s (𝟙 Y) y (mem j i y h₁ h₂) (mem j' i' y h₁' h₂'), trF, Fintype.prod_sum_type, Units.val_mul,
      @Fintype.prod_unique _ PUnit]
    simp only [trF, Category.id_comp, Sum.elim_inl, Sum.elim_inr]
    rfl
  have hc : ∀ j : K → L.ι, ∃ c : Fin N → Γ(T, LB.wchart L φ j), ∀ (y : Y) (i : L.ι), p₁ y ∈ LB.wchart L φ j →
      p₂ y ∈ L.U i →
      gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)))
          (s.f (Sum.elim j (fun _ => i))) = comb b p₁ p₂ _ c y i := by
    intro j
    have le : ∀ i, p₁ ⁻¹ᵁ LB.wchart L φ j ⊓ p₂ ⁻¹ᵁ L.U i ≤
        LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)) :=
      fun i y hy => mem j i y hy.1 hy.2
    obtain ⟨c, hc⟩ := (H (LB.wchart L φ j)).2
      (fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (Sum.elim j (fun _ => i)))) (by
        intro y i i' h₁ h₂ h₂'
        have e := tr j j i i' y h₁ h₂ h₁ h₂'
        rw [mul_eq_left.1 (trF_trans hL φ ε p₁ y h₁ h₁ h₁), Units.val_one, _root_.one_mul] at e
        exact (gs_res (𝟙 Y) y (le i) ⟨h₁, h₂⟩ _).trans
          (e.trans (congrArg _ (gs_res (𝟙 Y) y (le i') ⟨h₁, h₂'⟩ _).symm)))
    exact ⟨c, fun y i h₁ h₂ => (gs_res (𝟙 Y) y (le i) ⟨h₁, h₂⟩ _).symm.trans (hc y i h₁ h₂)⟩
  choose c hc using hc
  have compat : ∀ j j' : K → L.ι, ∀ k,
      (T.presheaf.map (homOfLE (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j k) =
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (T.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j' k) := by
    intro j j' k
    refine sub_eq_zero.1 (congrFun ((H (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 (fun k =>
      (T.presheaf.map (homOfLE (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j k) -
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (T.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j' k)) ?_) k)
    intro y i h₁ h₂
    have e := tr j j' i i y h₁.1 h₂ h₁.2 h₂
    rw [hc j y i h₁.1 h₂, hc j' y i h₁.2 h₂, gm_self hL p₂ y h₂, one_zpow, Units.val_one, _root_.mul_one, comb, comb,
      Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    refine (Finset.sum_congr rfl fun k _ => ?_).trans e
    have u : gs p₁ y (LB.wchart L φ j ⊓ LB.wchart L φ j')
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
        (trF φ ε p₁ y j j').val :=
      (gs_unit p₁ y _ h₁ _).trans (congrArg Units.val (gm_linComb L φ ε p₁ y j j' h₁.1 h₁.2))
    rw [gs_eq_gsHom p₁ y _ h₁, map_sub, ← gs_eq_gsHom, ← gs_eq_gsHom, gs_mul p₁ y _ h₁, u,
      gs_res p₁ y _ h₁, gs_res p₁ y _ h₁, sub_mul, _root_.mul_assoc]
  refine ⟨fun k => ⟨fun j => c j k, fun j j' => compat j j' k⟩, fun Z r z J hJ => ?_⟩
  have h₁ : p₁ (r z) ∈ LB.wchart L φ (fun k => J (r ≫ p₁ ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ p₁ ≫ φ k)
  have h₂ : p₂ (r z) ∈ L.U (J (r ≫ p₂)) := hJ (r ≫ p₂)
  have e := (gs_comp r (𝟙 Y) z _ (mem _ _ _ h₁ h₂) _).trans ((congrArg (r.stalkMap z).hom (hc _ (r z) _ h₁ h₂)).trans
    (comb_comp b r p₁ p₂ _ _ z _ h₁ h₂).symm)
  rw [Category.comp_id] at e
  rw [sval_of s r z J (Sum.elim (fun k => J (r ≫ p₁ ≫ φ k)) (fun _ => J (r ≫ p₂))) (by rintro (k | k) <;> rfl)]
  refine e.trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [sval_of _ (r ≫ p₁) z J (fun k => J (r ≫ p₁ ≫ φ k)) (fun k => by rw [Category.assoc])]
end GlobalTheory.RelBasis
