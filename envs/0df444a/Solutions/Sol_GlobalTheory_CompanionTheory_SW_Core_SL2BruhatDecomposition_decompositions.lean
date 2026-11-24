-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:16.937786+00:00
-- url     : https://prove2.me/submissions/c79fd9a2-9e5f-408f-b8c5-a2cbc766192c

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SL2BruhatDecompositionIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
namespace GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
private theorem coe_n {R : Type} [CommRing R] (b : R) :
    ((nMat b : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl
private theorem coe_m {R : Type} [CommRing R] (a : Rˣ) :
    ((mMat a : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)] := rfl
private theorem coe_w {R : Type} [CommRing R] :
    ((wMat : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 0] := rfl
private theorem SL2_eq_of_entries_eq_matrix {R : Type} [CommRing R] {g : SL(2, R)} {p q r s : R}
    {h : SL(2, R)} (hh : (h : Matrix (Fin 2) (Fin 2) R) = !![p, q; r, s])
    (h0 : g 0 0 = p) (h1 : g 0 1 = q) (h2 : g 1 0 = r) (h3 : g 1 1 = s) : g = h := by
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) R) = (h : Matrix (Fin 2) (Fin 2) R)
  rw [hh, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) R), h0, h1, h2, h3]
end GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
end

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
namespace GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
theorem _root_.solution : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  intro R _ g
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have hw : (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (((wMat * (wMat * wMat * wMat) : SL(2, R))) : Matrix (Fin 2) (Fin 2) R) = ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_w,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  refine ⟨?_, ?_, ?_, hw⟩
  · intro c hc
    have hu : (c : R) * ((c⁻¹ : Rˣ) : R) = 1 := by simp
    have hinv : ((-c⁻¹ : Rˣ) : R) = -((c⁻¹ : Rˣ) : R) := by simp
    have hinv2 : (((-c⁻¹ : Rˣ)⁻¹ : Rˣ) : R) = -(c : R) := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two, hinv, hinv2]
    generalize ((c⁻¹ : Rˣ) : R) = u at hu
    rw [hc] at hdet ⊢
    congr
    · linear_combination (g 0 0) * hu
    · linear_combination (g 0 0 * g 1 1 * u + g 0 1) * hu + u * hdet
    · ring
    · linear_combination (g 1 1) * hu
  · intro a ha
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    rw [hw]
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · linear_combination (g 1 0) * hu
    · linear_combination (g 1 0 * g 0 1 * u + g 1 1) * hu - u * hdet
  · intro a ha hc
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha, hc] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · ring
    · linear_combination (g 1 1) * hu - u * hdet
end GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
