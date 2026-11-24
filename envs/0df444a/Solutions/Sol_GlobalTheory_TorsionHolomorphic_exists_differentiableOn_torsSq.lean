-- Prove2me | solution 1 for GlobalTheory.TorsionHolomorphic.exists_differentiableOn_torsSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:33.370373+00:00
-- url     : https://prove2.me/submissions/3882f98e-7bb3-44fd-8ab2-b3484968d6cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDifferentiableOnTorsSq
import Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_det
import Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_matrix_mul
import Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_matrix_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.KeyKa
namespace GlobalTheory.TorsionHolomorphic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem degree_part_homotopy_of_anticommutator_eq_one {Ix : Type} [Fintype Ix] [DecidableEq Ix]
    (deg : Ix → ℕ) (D h : Matrix Ix Ix ℂ) (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0)
    (hh : D * h + h * D = 1) :
    D * Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) +
      Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) * D = 1 := by
  ext p q
  have h1 : ∀ r, D p r * (if deg r = deg q + 1 then h r q else 0) =
      if deg p = deg q then D p r * h r q else 0 := by
    intro r
    by_cases hr : deg r = deg p + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, mul_zero]
    · rw [hD p r hr, zero_mul, zero_mul, ite_self]
  have h2 : ∀ r, (if deg p = deg r + 1 then h p r else 0) * D r q =
      if deg p = deg q then h p r * D r q else 0 := by
    intro r
    by_cases hr : deg q = deg r + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, zero_mul]
    · rw [hD r q hr, mul_zero, mul_zero, ite_self]
  have hpq' := congrFun (congrFun hh p) q
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply] at hpq' ⊢
  simp only [h1, h2]
  by_cases hpq : deg p = deg q
  · simp only [if_pos hpq]
    exact hpq'
  · simp only [if_neg hpq, Finset.sum_const_zero, add_zero]
    have hne : p ≠ q := fun h => hpq (h ▸ rfl)
    rw [Matrix.one_apply_ne hne]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem contracting_homotopy_of_det_anticommutator_ne_zero {Ix : Type} [Fintype Ix]
    [DecidableEq Ix] (D h : Matrix Ix Ix ℂ) (hDD : D * D = 0)
    (hdet : (D * h + h * D).det ≠ 0) :
    D * (h * (D * h + h * D)⁻¹) + h * (D * h + h * D)⁻¹ * D = 1 := by
  set A := D * h + h * D with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hcomm : D * A = A * D := by
    rw [hA, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hDD, Matrix.zero_mul, zero_add,
      Matrix.mul_assoc h D D, hDD, Matrix.mul_zero, add_zero, Matrix.mul_assoc]
  have hinv : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = A⁻¹ * (D * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hcomm]
      _ = D * A⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hu, Matrix.one_mul]
  calc D * (h * A⁻¹) + h * A⁻¹ * D = D * h * A⁻¹ + h * D * A⁻¹ := by
        rw [Matrix.mul_assoc h, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = A * A⁻¹ := by rw [hA, Matrix.add_mul]
    _ = 1 := Matrix.mul_nonsing_inv A hu
end GlobalTheory.TorsionHolomorphic
end

set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionHolomorphic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.TorsionHolomorphic
namespace _root_.GlobalTheory.TorsionHolomorphic
theorem _root_.solution :
    ∀ (E Ix : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : E → Matrix Ix Ix ℂ) (W : Set E) (e₀ : E) (t₀ : ℂ), IsOpen W → e₀ ∈ W → (∀ p q, DifferentiableOn ℂ (fun e => D e p q) W) → (∀ e ∈ W, _root_.GlobalTheory.KeyKa.IsCx deg (D e)) → _root_.GlobalTheory.KeyKa.TorsSq deg (D e₀) t₀ → ∃ (W' : Set E) (t : E → ℂ), IsOpen W' ∧ e₀ ∈ W' ∧ W' ⊆ W ∧ DifferentiableOn ℂ t W' ∧ ∀ e ∈ W', _root_.GlobalTheory.KeyKa.TorsSq deg (D e) (t e) := by
  intro E Ix _ _ _ _ deg D W e₀ t₀ hW he₀ hD hcx htor
  obtain ⟨h₀, -, hcontr₀, σ, -⟩ := htor
  set A : E → Matrix Ix Ix ℂ := fun e => D e * h₀ + h₀ * D e with hAdef
  have hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W := by
    intro p q
    simp only [hAdef, Matrix.add_apply]
    exact (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul D (fun _ => h₀) W hD (fun _ _ => differentiableOn_const _)
      p q).add (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) D W
        (fun _ _ => differentiableOn_const _) hD p q)
  have hAdet := _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA
  set W' := W ∩ (fun e => (A e).det) ⁻¹' {(0 : ℂ)}ᶜ with hW'
  have hW'open : IsOpen W' := hAdet.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hsub : W' ⊆ W := Set.inter_subset_left
  have hdetW' : ∀ e ∈ W', (A e).det ≠ 0 := fun e he => he.2
  have hAe₀ : A e₀ = 1 := hcontr₀
  have he₀' : e₀ ∈ W' := ⟨he₀, by simp [hAe₀]⟩
  set hh : E → Matrix Ix Ix ℂ := fun e =>
    Matrix.of (fun p q => if deg p = deg q + 1 then (h₀ * (A e)⁻¹) p q else 0) with hhdef
  have hhdiff : ∀ p q, DifferentiableOn ℂ (fun e => hh e p q) W' := by
    intro p q
    simp only [hhdef, Matrix.of_apply]
    by_cases hpq : deg p = deg q + 1
    · simp only [if_pos hpq]
      exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) (fun e => (A e)⁻¹) W'
        (fun _ _ => differentiableOn_const _)
        (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv A W' (fun i j => (hA i j).mono hsub) hdetW') p q
    · simp only [if_neg hpq]
      exact differentiableOn_const _
  refine ⟨W', fun e => ((D e + hh e).submatrix (fun p : {p // Even (deg p)} => (p : Ix))
    (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))).det ^ 2,
    hW'open, he₀', hsub, ?_, ?_⟩
  · refine DifferentiableOn.pow ?_ 2
    refine _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (D e + hh e).submatrix
      (fun p : {p // Even (deg p)} => (p : Ix))
      (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))) W' (fun i j => ?_)
    simp only [Matrix.submatrix_apply, Matrix.add_apply]
    exact ((hD _ _).mono hsub).add (hhdiff _ _)
  · intro e he
    refine ⟨hh e, ?_, ?_, σ, rfl⟩
    · intro p q hpq
      simp only [hhdef, Matrix.of_apply, if_neg hpq]
    · exact degree_part_homotopy_of_anticommutator_eq_one deg (D e) (h₀ * (A e)⁻¹) (hcx e (hsub he)).1
        (contracting_homotopy_of_det_anticommutator_ne_zero (D e) h₀ (hcx e (hsub he)).2 (hdetW' e he))
end _root_.GlobalTheory.TorsionHolomorphic
end GlobalTheory.TorsionHolomorphic
