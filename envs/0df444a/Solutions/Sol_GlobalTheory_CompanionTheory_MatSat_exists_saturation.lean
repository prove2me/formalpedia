-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatSat.exists_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:20.62659+00:00
-- url     : https://prove2.me/submissions/bcb978eb-7c38-4f07-9b8d-54adc27918cd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsBasisCols
import Theorems.Thm_GlobalTheory_CompanionTheory_MatSat_exists_basis_cols
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_refl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatSat
namespace GlobalTheory.CompanionTheory.MatSat
theorem _root_.solution {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (C : Matrix (β ⊕ γ) β K)
    (hC : ∃ L : Matrix β (β ⊕ γ) K, L * C = 1) :
    ∃ (t : GL β K) (C₀ : Matrix (β ⊕ γ) β O) (D : Matrix (β ⊕ γ) γ O),
      C * (t : Matrix β β K) = C₀.map (algebraMap O K) ∧
        IsUnit (Matrix.fromCols C₀ D).det := by
  classical
  obtain ⟨L, hL⟩ := hC
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : (β ⊕ γ) × β => C p.1 p.2)
  have hb' : ∀ p : (β ⊕ γ) × β, ∃ x : O,
      algebraMap O K x = algebraMap O K (b : O) * C p.1 p.2 := by
    intro p
    obtain ⟨x, hx⟩ := RingHom.mem_rangeS.1 (hb p)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hbne : algebraMap O K (b : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Matrix (β ⊕ γ) β O,
      C₁.map (algebraMap O K) = algebraMap O K (b : O) • C :=
    ⟨Matrix.of fun i j => c (i, j), by ext i j; simp [hc]⟩
  have hinj : Function.Injective C₁.mulVecLin := by
    intro v w hvw
    have h1 : C₁ *ᵥ v = C₁ *ᵥ w := hvw
    have h2 : ∀ x : β → O, (algebraMap O K) ∘ (C₁ *ᵥ x) =
        algebraMap O K (b : O) • (C *ᵥ ((algebraMap O K) ∘ x)) := by
      intro x
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hC₁]
      first
      | rw [Matrix.smul_mulVec]
      | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have e1 := h2 v
    have e2 := h2 w
    rw [h1] at e1
    have h3 : C *ᵥ ((algebraMap O K) ∘ v) = C *ᵥ ((algebraMap O K) ∘ w) :=
      smul_right_injective (β ⊕ γ → K) hbne (e1.symm.trans e2)
    have h4 : (algebraMap O K) ∘ v = (algebraMap O K) ∘ w := by
      have := congrArg (fun z => L *ᵥ z) h3
      simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using this
    funext i
    exact IsFractionRing.injective O K (congrFun h4 i)
  obtain ⟨P, a, s, u, hP, -, -, hu⟩ := exists_basis_cols C₁ hinj
  have hCw : C = (P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) := by
    have e1 : algebraMap O K (b : O) • C = (P.toCols₁.map (algebraMap O K)) * (u.map (algebraMap O K)) := by
      rw [← hC₁, hu, Matrix.map_mul]
    rw [Matrix.mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hbne, one_smul]
  have hLw : (L * P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) = 1 := by
    rw [Matrix.mul_assoc, ← hCw, hL]
  have hwL : ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) *
      (L * P.toCols₁.map (algebraMap O K)) = 1 := by
    first
    | exact mul_eq_one_comm.1 hLw
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 hLw
  refine ⟨⟨L * P.toCols₁.map (algebraMap O K),
    (algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K), hLw, hwL⟩, P.toCols₁, P.toCols₂, ?_, ?_⟩
  · show C * (L * P.toCols₁.map (algebraMap O K)) = P.toCols₁.map (algebraMap O K)
    rw [hCw, Matrix.mul_assoc, hwL, Matrix.mul_one]
  · rw [Matrix.fromCols_toCols]
    exact hP
end GlobalTheory.CompanionTheory.MatSat
