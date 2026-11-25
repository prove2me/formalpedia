-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.exists_ratio_of_weight_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:39.426361+00:00
-- url     : https://prove2.me/submissions/8397616f-1696-486b-bc11-2d9397237475

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightedRelationOfMinimalSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSums
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_mul
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_one
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_add
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_zero
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_comp
import Theorems.Thm_GlobalTheory_SS_WtRat_exists_rel
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_congr
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_res
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_spMap
import Theorems.Thm_GlobalTheory_T_exists_generic_functionField_point
import Theorems.Thm_GlobalTheory_T_exists_weighted_relation_of_minimal_support
import Theorems.Thm_GlobalTheory_T_splitTorusWeight_test_genericPoint_rationalPoints
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_of_geometricallyConnected


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
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∀ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → ∃ (U' : G.left.Opens) (h : U' ≤ U) (n : ℕ) (a b : Fin n → Γ(G.left, U')) (χ : Fin n → X), (U' : Set G.left).Nonempty ∧ (∀ j, Wt i U' (a j) (χ j) ∧ Wt i U' (b j) (χ j) ∧ (a j = 0 ∨ IsUnit (a j)) ∧ (b j = 0 ∨ IsUnit (b j))) ∧ IsUnit (∑ j, b j) ∧ (G.left.presheaf.map (homOfLE h).op).hom f * ∑ j, b j = ∑ j, a j := by
  intro k _ _ G _ hG X _ _ _ i hi U f hU
  obtain ⟨hc, hs, -, -, hgc⟩ := hG
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  obtain ⟨F, _, g₀, hg, hinj, hσ, hsec⟩ := GlobalTheory.T.exists_generic_functionField_point G.left
  let s : Sp F ⟶ Sp k := g₀ ≫ G.hom
  let g : Over.mk s ⟶ G := Over.homMk g₀ rfl
  let pt (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) : Over.mk s ⟶ splitTorus (Sp k) X := toUnit _ ≫ t
  have pt_mul (t t') : pt (t * t') = pt t * pt t' := MonObj.comp_mul _ _ _
  have pt_one : pt 1 = 1 := MonObj.comp_one _
  have hτ (t) : g₀ ≫ (transl (t ≫ i)).hom.left = ((pt t ≫ i) * g).left := by
    have : g ≫ (transl (t ≫ i)).hom = (pt t ≫ i) * g := by
      show g ≫ ((toUnit G ≫ t ≫ i) * 𝟙 G) = _
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, ← Category.assoc]
    exact congrArg CommaMorphism.left this
  choose σ hσ' using fun t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X =>
    hσ ((Over.forget _).mapIso (transl (t ≫ i)))
  replace hσ' (t) : spMap (σ t) ≫ g₀ = ((pt t ≫ i) * g).left := (hσ' t).trans (hτ t)
  have hσs (t) : spMap (σ t) ≫ s = s := by
    show spMap (σ t) ≫ g₀ ≫ G.hom = s
    rw [← Category.assoc, hσ']
    exact Over.w _
  have hσpt (t t') : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ pt t' = pt t' := by
    show _ ≫ toUnit _ ≫ t' = _
    rw [← Category.assoc, comp_toUnit]
  have hσg (t t') : spMap (σ t) ≫ ((pt t' ≫ i) * g).left = ((pt (t' * t) ≫ i) * g).left := by
    have h1 : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ g = (pt t ≫ i) * g :=
      Over.OverMorphism.ext (hσ' t)
    have : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ ((pt t' ≫ i) * g) =
        (pt (t' * t) ≫ i) * g := by
      rw [MonObj.comp_mul, ← Category.assoc, hσpt, h1, pt_mul, MonObj.mul_comp, _root_.mul_assoc]
    exact congrArg CommaMorphism.left this
  have hgt (t) (V : G.left.Opens) (hV : (V : Set G.left).Nonempty) : ⊤ ≤ ((pt t ≫ i) * g).left ⁻¹ᵁ V := by
    rw [← hτ]
    obtain ⟨x, hx⟩ := hV
    obtain ⟨y, rfl⟩ := ((Over.forget _).mapIso (transl (t ≫ i))).hom.surjective x
    exact hg ((transl (t ≫ i)).hom.left ⁻¹ᵁ V) ⟨y, hx⟩
  have hone : ((pt 1 ≫ i) * g).left = g₀ := by
    rw [pt_one, MonObj.one_comp, _root_.one_mul]; rfl
  obtain ⟨S, p, q, hp, hrel⟩ := exists_rel i g U f (pt_one ▸ hgt 1 U hU)
  obtain ⟨χ₀, p', q', hp', hφ, hw⟩ := GlobalTheory.T.exists_weighted_relation_of_minimal_support F _ X (fun t χ => chr (pt t) χ) σ
    (fun t => ev (R := F) ((pt t ≫ i) * g).left U (hgt t U hU) f) S p q
    (fun t t' χ => by rw [pt_mul, chr_mul]) (fun χ => by rw [pt_one, chr_one])
    (fun t t' χ => by rw [← chr_comp (σ t) (hσs t), hσpt])
    (fun t t' => (ev_spMap (σ t) _ U _ (hσg t t' ▸ hgt (t' * t) U hU) f).symm.trans
      (ev_congr (hσg t t') U _ _ f))
    (fun t => hrel (pt t) _) hp
  let ε := S.equivFin.symm
  have hε (r : X → F) : ∑ j, r (ε j) = ∑ χ ∈ S, r χ := by
    rw [← Finset.sum_coe_sort S r]
    exact Equiv.sum_comp ε fun x : S => r x
  obtain ⟨U', hU', u, hle, hu⟩ := hsec U hU (Option (Fin S.card ⊕ Fin S.card))
    (fun o => o.elim (∑ χ ∈ S, p' χ) (Sum.elim (fun j => q' (ε j)) fun j => p' (ε j)))
  have hwt (v : Γ(G.left, U')) (χ : X) (r : F) (hv : ev g₀ U' (hg U' hU') v = r)
      (hr : ∀ t, σ t r * chr (pt t) χ₀ = chr (pt t) χ * r) : Wt i U' v (χ - χ₀) := by
    refine GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints k G hs X i F s g hg U' v _ fun t h₁ h₂ => ?_
    have h3 : ev (R := F) ((pt t ≫ i) * g).left U' h₁ v = σ t r :=
      (ev_congr (hσ' t).symm U' h₁ (hσ' t ▸ h₁) v).trans
        ((ev_spMap (σ t) g₀ U' (hg U' hU') _ v).trans (congrArg (σ t) hv))
    have h4 : chr (pt t) χ₀ * chr (pt t) (-χ₀) = 1 := by rw [← chr_add, add_neg_cancel, chr_zero]
    refine h3.trans (Eq.trans ?_ (congrArg (chr (pt t) (χ - χ₀) * ·) hv.symm))
    rw [sub_eq_add_neg, chr_add]
    linear_combination chr (pt t) (-χ₀) * hr t - σ t r * h4
  have hun (o) : u o = 0 ∨ IsUnit (u o) := by
    refine (eq_or_ne _ 0).imp (fun h => hinj U' hU' ?_) (hu o).2
    rw [(hu o).1, h, map_zero]
  have hb : ev g₀ U' (hg U' hU') (∑ j, u (some (Sum.inr j))) = ∑ χ ∈ S, p' χ := by
    rw [map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu _).1
  refine ⟨U', hle, S.card, fun j => u (some (Sum.inl j)), fun j => u (some (Sum.inr j)), fun j => ε j - χ₀, hU',
    fun j => ⟨hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).2, hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).1,
      hun _, hun _⟩, ?_, hinj U' hU' ?_⟩
  · rw [hinj U' hU' (hb.trans (hu none).1.symm)]
    exact (hu none).2 hp'
  · rw [map_mul, hb, ev_res g₀ hle _ (hg U hU), ← ev_congr hone U (hgt 1 U hU), hφ, map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu (some (Sum.inl j))).1.symm
end GlobalTheory.SS.WtRat
