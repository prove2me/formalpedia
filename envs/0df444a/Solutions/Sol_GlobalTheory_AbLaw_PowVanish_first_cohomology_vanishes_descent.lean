-- Prove2me | solution 1 for GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:31.278512+00:00
-- url     : https://prove2.me/submissions/5b890132-4e46-425d-8c81-0803628f07d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pre_inf
import Theorems.Thm_P2M_GlobalTheory_AbLaw_PowVanish_pre_inf__f58b070a9db0
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_rs_pb
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_rs
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_pb
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_congr
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_app_eq_pb
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_rs_pull_g

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.PowVanish
theorem _root_.solution (f : Y ⟶ X) (M : LB X) (G : Type) [Group G] [Fintype G] (τ : G → (Y ⟶ Y))
    (hτ : ∀ y, τ y ≫ f = f) (hmul : ∀ y z, τ y ≫ τ z = τ (y * z))
    (hu : IsUnit ((Fintype.card G : ℕ) : Γ(X, ⊤)))
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
    (H : FirstCohomologyVanishes (M.pull f)) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  have inv : ∀ y (U : X.Opens), f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U) := fun y U => by
    rw [← Scheme.Hom.comp_preimage, hτ]
  have pinv : ∀ y {U : X.Opens} {W W' : Y.Opens} (e : W ≤ f ⁻¹ᵁ U) (e' : W' ≤ τ y ⁻¹ᵁ W)
      (e'' : W' ≤ f ⁻¹ᵁ U) (x : Γ(X, U)), pb (τ y) e' (pb f e x) = pb f e'' x := fun y U W W' e e' e'' x => by
    rw [pb_pb, pb_congr (hτ y)]
  have inj : ∀ (U : X.Opens) (a b : Γ(X, U)), pb f le_rfl a = pb f le_rfl b → a = b := fun U a b hab =>
    (hgal U (pb f le_rfl a) (fun y e => pinv y _ _ _ a)).unique (app_eq_pb f U a)
      ((app_eq_pb f U b).trans hab.symm)
  obtain ⟨ψ, hψ⟩ := H I (fun a => f ⁻¹ᵁ V a) (fun a _ => c a) (fun a => le_pull M f (hV a))
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl)
    (fun a b => pb f (pre_inf f (V a) (V b)) (φ a b)) (fun a b d => by
      have h := congrArg (pb f (U := V a ⊓ V b ⊓ V d) (W := f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ⊓ f ⁻¹ᵁ V d)
        ((inf_le_inf_right _ (pre_inf f _ _)).trans (pre_inf f _ _))) (hφ a b d)
      simp only [map_add, map_mul, pb_rs] at h
      simp only [rs_pb, rs_pull_g]
      exact h)
  have hχ : ∀ a, ∃ χ : Γ(X, V a), pb f le_rfl χ = ∑ y, pb (τ y) (inv y (V a)) (ψ a) := fun a => by
    obtain ⟨χ, h, -⟩ := hgal (V a) (∑ y, pb (τ y) (inv y (V a)) (ψ a)) (fun z e => by
      rw [map_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun y => ?_
      rw [pb_pb, pb_congr (hmul z y)]
      rfl)
    exact ⟨χ, (app_eq_pb f _ χ).symm.trans h⟩
  choose χ hχ using hχ
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  refine ⟨fun a => rs X le_top u * χ a, fun a b => ?_⟩
  have key : ((Fintype.card G : ℕ) : Γ(X, V a ⊓ V b)) * φ a b = rs X inf_le_left (χ a) -
      rs X (inf_le_inf (hV a) (hV b) : V a ⊓ V b ≤ M.U (c a) ⊓ M.U (c b)) (M.g (c a) (c b)).val *
        rs X inf_le_right (χ b) := by
    apply inj
    have la : f ⁻¹ᵁ (V a ⊓ V b) ≤ f ⁻¹ᵁ V a := pre_mono f inf_le_left
    have lb : f ⁻¹ᵁ (V a ⊓ V b) ≤ f ⁻¹ᵁ V b := pre_mono f inf_le_right
    have ha := congrArg (rs Y la) (hχ a)
    have hb := congrArg (rs Y lb) (hχ b)
    simp only [map_sum, rs_pb] at ha hb
    simp only [map_sub, map_mul, map_natCast, pb_rs]
    rw [ha, hb, Finset.mul_sum, ← Finset.sum_sub_distrib, ← nsmul_eq_mul, ← Finset.card_univ,
      ← Finset.sum_const]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h := congrArg (pb (τ y) (U := f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b) (W := f ⁻¹ᵁ (V a ⊓ V b))
      ((inv y (V a ⊓ V b)).trans (pre_mono _ (pre_inf' f _ _)))) (hψ a b)
    simp only [map_sub, map_mul, pb_rs, rs_pull_g] at h
    rw [pinv y _ _ le_rfl, pinv y _ _ (pre_mono f (inf_le_inf (hV a) (hV b)))] at h
    exact h
  have hu' := congrArg (rs X (le_top : V a ⊓ V b ≤ ⊤)) hu
  simp only [map_mul, map_natCast, map_one] at hu'
  simp only [map_mul, rs_rs]
  linear_combination (rs X (le_top : V a ⊓ V b ≤ ⊤) u) * key - φ a b * hu'
end GlobalTheory.AbLaw.PowVanish
