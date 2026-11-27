-- Prove2me | solution 1 for GlobalTheory.SS.exists_quadraticForm_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:05:31.087509+00:00
-- url     : https://prove2.me/submissions/894a8cba-c2af-4cfb-9a37-62e5e811a9c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Theorems.Thm_GlobalTheory_SS_HtForm_gen_reindex
import Theorems.Thm_GlobalTheory_SS_HtForm_gen_field
import Theorems.Thm_GlobalTheory_SS_HtForm_comp_psum
import Theorems.Thm_GlobalTheory_SS_HtForm_sum_subsets_fin_three_expand
import Theorems.Thm_GlobalTheory_SS_HtForm_factor_of_const
import Theorems.Thm_GlobalTheory_SS_HtForm_exists_generic
import Theorems.Thm_GlobalTheory_T_exists_lineBundle_height_properScheme
import Theorems.Thm_GlobalTheory_T_exists_productFormula_places_of_fg_field
import Theorems.Thm_GlobalTheory_forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb


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
open GlobalTheory GlobalTheory.SS
open HtForm
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∃ Q : (B ⟶ B) → ℤ, (∀ f g, Q (f * g) + Q (f * g⁻¹) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ (∀ f, IsMonHom f → Q f = 0 → f = 1) ∧ ∀ (F : B ⟶ B) (q : ℤ), PullPow F.left L q → ∀ f, Q (f ≫ F) = q * Q f := by
  intro k _ _ B _ hB L ⟨hL, hΘ, hsym, N, hN, hamp⟩
  have := hB.comm
  have := hB.smooth
  have hpr := hB.proper
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  obtain ⟨K, _, _, hK, P, hP⟩ := exists_generic B
  obtain ⟨Pl, hPl⟩ := GlobalTheory.T.exists_productFormula_places_of_fg_field k K hK
  obtain ⟨h, hrel, hpos⟩ := GlobalTheory.T.exists_lineBundle_height_properScheme k K Pl B hpr L hL
  have hrel' : ∀ (Z : Over (Sp k)), IsProper Z.hom → ∀ (I : Type) [Fintype I] (φ : I → (Z ⟶ B)) (ε : I → ℤ),
      (∃ t : LB.Gen (LB.LinComb L (fun i => (φ i).left) ε), t.IsGen) →
      ∀ z : Over.mk (spMap (algebraMap k K)) ⟶ Z, ∑ i, ε i * h (z ≫ φ i) = 0 := by
    intro Z hZ I _ φ ε ht z
    have := hrel Z hZ _ (fun i => φ ((Fintype.equivFin I).symm i)) (fun i => ε ((Fintype.equivFin I).symm i))
      (gen_reindex L (Fintype.equivFin I).symm (fun i => (φ i).left) ε ht) z
    rwa [(Fintype.equivFin I).symm.sum_comp fun i => ε i * h (z ≫ φ i)] at this
  have h1 : h 1 = 0 := by
    have := hrel (𝟙_ _) (by show IsProper (𝟙 _); infer_instance) 1 (fun _ => η[B]) (fun _ => 1)
      (gen_field (k := k) _ (LB.isLB_linComb hL _ _)) (toUnit _)
    rw [Fin.sum_univ_one, _root_.one_mul] at this
    exact this
  have hpull : ∀ (F : B ⟶ B) (q : ℤ), PullPow F.left L q → ∀ x, h (x ≫ F) = q * h x := by
    intro F q hF x
    have e : (fun i => ((![F, 𝟙 B] : Fin 2 → (B ⟶ B)) i).left) = ![F.left, 𝟙 B.left] := by
      funext i; fin_cases i <;> rfl
    have := hrel B hpr 2 ![F, 𝟙 B] ![1, -q] (by rw [e]; exact hF) x
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at this
    linarith
  have hinv : ∀ x, h x⁻¹ = h x := fun x => by
    have := hpull ι[B] 1 hsym x
    rw [_root_.one_mul] at this
    exact this
  have hpar : ∀ x y, h (x * y) + h (x * y⁻¹) = 2 * h x + 2 * h y := by
    intro x y
    have hp3 : IsProper (G3 B).hom := by
      have : IsProper (B ⊗ B).hom := by show IsProper (pullback.fst _ _ ≫ B.hom); infer_instance
      show IsProper (pullback.fst _ _ ≫ B.hom); infer_instance
    have := hrel' (G3 B) hp3 (ULift.{0} (Finset (Fin 3))) (fun I => psum B (x3 B) I.down)
      (fun I => (-1) ^ (3 - I.down.card)) hΘ (lift x (lift y y⁻¹))
    rw [sum_subsets_fin_three_expand fun I => (-1) ^ (3 - I.card) * h (lift x (lift y y⁻¹) ≫ psum B (x3 B) I)] at this
    have e0 : lift x (lift y y⁻¹) ≫ x3 B 0 = x := by simp [x3]
    have e1 : lift x (lift y y⁻¹) ≫ x3 B 1 = y := by simp [x3]
    have e2 : lift x (lift y y⁻¹) ≫ x3 B 2 = y⁻¹ := by simp [x3]
    have l0 : (List.finRange 3).filter (· ∈ (∅ : Finset (Fin 3))) = [] := by decide
    have l1 : (List.finRange 3).filter (· ∈ ({0} : Finset (Fin 3))) = [0] := by decide
    have l2 : (List.finRange 3).filter (· ∈ ({1} : Finset (Fin 3))) = [1] := by decide
    have l3 : (List.finRange 3).filter (· ∈ ({2} : Finset (Fin 3))) = [2] := by decide
    have l4 : (List.finRange 3).filter (· ∈ ({0, 1} : Finset (Fin 3))) = [0, 1] := by decide
    have l5 : (List.finRange 3).filter (· ∈ ({0, 2} : Finset (Fin 3))) = [0, 2] := by decide
    have l6 : (List.finRange 3).filter (· ∈ ({1, 2} : Finset (Fin 3))) = [1, 2] := by decide
    have l7 : (List.finRange 3).filter (· ∈ ({0, 1, 2} : Finset (Fin 3))) = [0, 1, 2] := by decide
    have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
    have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
    have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
    simp only [comp_psum] at this
    rw [l0, l1, l2, l3, l4, l5, l6, l7, c4, c5, c6, c7] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e0, e1, e2, _root_.mul_one,
      mul_inv_cancel, h1, hinv, Finset.card_singleton, Finset.card_empty] at this
    norm_num at this
    linarith
  have hchart : ∀ x : Over.mk (spMap (algebraMap k K)) ⟶ B, ∃ s : LB.Sec (GlobalTheory.AbLaw.pw L N),
      Set.range x.left ⊆ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
    intro x
    obtain ⟨s, hs, ha⟩ := hamp (x.left (IsLocalRing.closedPoint K))
    refine ⟨s, ?_, ha⟩
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]
    exact hs
  refine ⟨fun f => h (P ≫ f), fun f g => ?_, fun f => ?_, fun f hf h0 => ?_, fun F q hF f => ?_⟩
  · simp only [MonObj.comp_mul, GrpObj.comp_inv]
    exact hpar _ _
  · obtain ⟨s, hs, -⟩ := hchart (P ≫ f)
    exact (hpos N s _ hN hs).1
  · obtain ⟨s, hs, ha⟩ := hchart (P ≫ f)
    obtain ⟨c, hc⟩ := factor_of_const B (P ≫ f) ha Pl.O hPl hs ((hpos N s _ hN hs).2 h0)
    have hf' : f = toUnit B ≫ c := by
      refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.hom
        ((Over.w f).trans (Over.w _).symm) P.left ?_)
      rw [← Over.comp_left, ← Over.comp_left, hc, ← Category.assoc, toUnit_unique (P ≫ toUnit B) (toUnit _)]
    have hc' : c = η[B] := by
      have := IsMonHom.one_hom f
      rw [hf', ← Category.assoc, toUnit_unique (η[B] ≫ toUnit B) (𝟙 _), Category.id_comp] at this
      exact this
    rw [hf', hc']
    rfl
  · show h (P ≫ f ≫ F) = q * h (P ≫ f)
    rw [← Category.assoc]
    exact hpull F q hF _
end GlobalTheory.SS
