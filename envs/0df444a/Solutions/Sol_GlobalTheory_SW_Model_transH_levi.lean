-- Prove2me | solution 1 for GlobalTheory.SW.Model.transH_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:58.816519+00:00
-- url     : https://prove2.me/submissions/d8c53ad9-09a8-43cb-b6e2-a080ddb4c308

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Theorems.Thm_GlobalTheory_SW_Base_ccT_map
import Theorems.Thm_GlobalTheory_SW_Base_expo_eq_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) {n N : ℕ} {A D : Matrix (Fin N) (Fin N) E}
    (h : ccT D * A = 1) (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    TransH Ψ (Matrix.fromBlocks A 0 0 D) φ
      (fun x => (∏ τ : Ψ, τ.1 D.det ^ n) * φ (x * A)) := by
  intro Z _ z z'
  have h' : A * ccT D = 1 := mul_eq_one_comm.1 h
  have e : ∀ τ : Ψ, (D.map τ.1)ᴴ * A.map τ.1 = 1 := fun τ => by
    rw [← Base.ccT_map, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have e' : ∀ τ : Ψ, (A.map τ.1)ᴴ * D.map τ.1 = 1 := fun τ => by
    simpa using congrArg Matrix.conjTranspose (e τ)
  have d1 : ∀ τ, hDen Ψ (Matrix.fromBlocks A 0 0 D) Z τ = D.map τ.1 := fun τ => by simp [hDen]
  have d2 : ∀ τ, hDen' Ψ (Matrix.fromBlocks A 0 0 D) Z τ = (D.map τ.1)ᴴ := fun τ => by
    simp [hDen']
  have i1 : ∀ τ : Ψ, (D.map τ.1)⁻¹ = (A.map τ.1)ᴴ := fun τ => Matrix.inv_eq_left_inv (e' τ)
  have i2 : ∀ τ : Ψ, ((D.map τ.1)ᴴ)⁻¹ = A.map τ.1 := fun τ => Matrix.inv_eq_right_inv (e τ)
  have a : hAct Ψ (Matrix.fromBlocks A 0 0 D) Z = fun τ => A.map τ.1 * Z τ * (A.map τ.1)ᴴ := by
    funext τ; simp [hAct, d1, i1]
  have f : hFac Ψ (Matrix.fromBlocks A 0 0 D) Z z z' = ∏ τ : Ψ, τ.1 D.det ^ n := by
    unfold hFac
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [d1, RingHom.map_det]
    simp
  have e1 : (fun τ => Matrix.of fun k => (hDen' Ψ (Matrix.fromBlocks A 0 0 D) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => z τ * (A.map τ.1)ᵀ := by
    funext τ; ext k i; simp [d2, i2, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  have e2 : (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ (Matrix.fromBlocks A 0 0 D) Z τ)⁻¹) =
      fun τ => z' τ * (A.map τ.1)ᴴ := by
    funext τ; ext k i; rw [d1, i1]; rfl
  rw [a, f, e1, e2]
  let σ : Matrix (Fin n) (Fin N) E ≃ Matrix (Fin n) (Fin N) E :=
    ⟨fun x => x * A, fun x => x * ccT D,
      fun x => by simp only [Matrix.mul_assoc, h', Matrix.mul_one],
      fun x => by simp only [Matrix.mul_assoc, h, Matrix.mul_one]⟩
  unfold thH
  rw [← σ.tsum_eq (fun x => φ x * cexp (2 * Real.pi * I * expo Ψ x Z z z')), ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  change _ = _ * (φ (x * A) * cexp (_ * expo Ψ (x * A) Z z z'))
  rw [mul_assoc]
  congr 4
  rw [Base.expo_eq_trace, Base.expo_eq_trace]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.map_mul, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]
end GlobalTheory.SW.Model
