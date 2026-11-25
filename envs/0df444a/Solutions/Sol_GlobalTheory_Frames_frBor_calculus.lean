-- Prove2me | solution 1 for GlobalTheory.Frames.frBor_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:26:46.937972+00:00
-- url     : https://prove2.me/submissions/99e8c407-6f73-4089-b874-0141df3e66ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueFrameChangeByMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeExistsUniqueOfSamePointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeByMatricesReflAndCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LowerTriangularMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LowerTriIsUnitDet
import Theorems.Thm_GlobalTheory_Frames_lowerTri_mul
import Theorems.Thm_GlobalTheory_Frames_lowerTri_mul_diag
import Theorems.Thm_GlobalTheory_Frames_lowerTri_isUnit_det
import Theorems.Thm_GlobalTheory_Frames_lowerTri_inv
import Theorems.Thm_GlobalTheory_Frames_frBor_iff_frChg
import Theorems.Thm_GlobalTheory_T_existsUnique_frameChangeByMatrices
import Theorems.Thm_GlobalTheory_T_frameChangeByMatrices_refl_and_comp
import Theorems.Thm_GlobalTheory_T_frameChange_exists_unique_of_same_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), (∀ t : Ix Dw → Sˣ, FrBor t y y' ↔ ∃ g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S), (∀ τ i j, i < j → g τ i j = 0) ∧ (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ FrChg g (t none : S) y y') ∧ (y'.x = y.x → (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → S, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt y.x (y.u τ) cf (y'.u τ i)) → ∃ t : Ix Dw → Sˣ, FrBor t y y') ∧ (∀ t t' : Ix Dw → Sˣ, FrBor t y y' → FrBor t' y' y'' → FrBor (t' * t) y y'') ∧ (∀ t : Ix Dw → Sˣ, FrBor t y y' → FrBor t⁻¹ y' y) := by
  intro E _ _ _ H Dw l Xo c S _ _ y y' y''
  refine ⟨frBor_iff_frChg y y', fun hx hu => ?_, fun t t' h h' => ?_, fun t h => ?_⟩
  · obtain ⟨g₀, a, -, -, -, hs⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S y y').1 hx
    choose cf hd hz hc using hu
    refine ⟨fun k => match k with
      | none => a
      | some ⟨τ, i⟩ => (hd τ i).unit, (frBor_iff_frChg y y' _).2
        ⟨fun τ => Matrix.of (cf τ), fun τ i j h => hz τ i j h, fun τ i => ?_, hx, hc, hs⟩⟩
    exact (hd τ i).unit_spec.symm
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    obtain ⟨g', hz', hd', hc'⟩ := (frBor_iff_frChg y' y'' t').1 h'
    refine (frBor_iff_frChg y y'' _).2 ⟨fun τ => g' τ * g τ,
      fun τ => lowerTri_mul _ _ (hz' τ) (hz τ), fun τ i => ?_, ?_⟩
    · show (g' τ * g τ) i i = _
      rw [lowerTri_mul_diag _ _ (hz' τ) (hz τ), hd, hd', Pi.mul_apply, Units.val_mul]
    · rw [Pi.mul_apply, Units.val_mul]
      exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' _ _ hc hc'
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
      lowerTri_isUnit_det _ (hz τ) fun i => by rw [hd]; exact Units.isUnit _
    have hinv : ∀ τ, (g τ)⁻¹ * g τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
    have hzi : ∀ τ i j, i < j → (g τ)⁻¹ i j = 0 := fun τ => lowerTri_inv _ (hz τ) (hdet τ)
    obtain ⟨z, hzc, -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y' (fun τ => (g τ)⁻¹) (t none)⁻¹
      fun τ => Matrix.isUnit_nonsing_inv_det _ (hdet τ)
    have h1 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y' z).2 g _ _ _ hc hzc
    simp only [hinv, Units.inv_mul] at h1
    have h0 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y y).1
    have hzy : z = y := (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y (fun _ => 1) 1 (fun τ => by simp)).unique h1 h0
    subst hzy
    refine (frBor_iff_frChg y' z _).2 ⟨fun τ => (g τ)⁻¹, hzi, fun τ i => ?_, hzc⟩
    have h2 := lowerTri_mul_diag _ _ (hzi τ) (hz τ) i
    rw [hinv, Matrix.one_apply_eq, hd] at h2
    rw [Pi.inv_apply]
    exact Units.eq_inv_of_mul_eq_one_right h2.symm
end GlobalTheory.Frames
