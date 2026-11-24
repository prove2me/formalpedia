-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.sum_invFourierSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:18:24.410874+00:00
-- url     : https://prove2.me/submissions/5129bc78-4fbd-4a59-8121-a6cfe0e169c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
import Theorems.Thm_GlobalTheory_SplitFlip_Model_sum_psi
import Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_apply
import Theorems.Thm_GlobalTheory_SplitFlip_liftRes_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) (Ψ : Matrix A D k → ℂ) (X : Matrix A D k) (S₀ : A → P → Res k e) :
    ∑ T : A → P → Res k e, invFourierSum ψ ϖ e P Ψ (setCols P X (liftRes T)) *
      (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      (Fintype.card (Res k e) : ℂ) ^ (Fintype.card A * P.card) * Ψ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) := by
  classical
  have h1 : ∀ T S, setCols P (setCols P X T) S = setCols P X S := fun T S => by
    ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
  have h2 : ∀ T : A → P → Res k e, ∀ i, ∀ j ∈ P, setCols P X (liftRes T) i j ∈ 𝒪[k] := fun T i j h => by
    simpa [setCols, h] using liftRes_mem T i ⟨j, h⟩
  simp only [invFourierSum_apply, if_pos (h2 _), h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h3 : ∀ S T : A → P → Res k e,
      (ψ (-pairCols P (setCols P X (liftRes T)) ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) *
        (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) := fun S T => by
    have hp : ∀ {ι : Type _} (s : Finset ι) (f : ι → k), (ψ (∑ i ∈ s, f i) : ℂ) = ∏ i ∈ s, (ψ (f i) : ℂ) :=
      fun s f => by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul,
            Circle.coe_mul, ih]
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← Finset.prod_product', ← hp, Finset.sum_product]
    congr 2
    simp only [pairCols, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [setCols, liftRes, Units.smul_def]
    ring
  have h4 : ∀ S : A → P → Res k e, ∑ T : A → P → Res k e,
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
      if S₀ = S then (Fintype.card (Res k e) : ℂ) ^ (Fintype.card A * P.card) else 0 := fun S => by
    rw [← Fintype.prod_sum (fun i (t : P → Res k e) => ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
    have h5 : ∀ i, ∑ t : P → Res k e, ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
        ∏ j, if S₀ i j = S i j then (Fintype.card (Res k e) : ℂ) else 0 := fun i => by
      rw [← Fintype.prod_sum (fun (j : P) (t : Res k e) => (ψ (((Quotient.out t : 𝒪[k]) : k) *
        ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
      exact Finset.prod_congr rfl fun j _ => by convert sum_psi hϖ hψ e (S₀ i j) (S i j)
    rw [Finset.prod_congr rfl fun i _ => h5 i]
    split_ifs with h
    · subst h; simp [← pow_mul, mul_comm]
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hi
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  simp only [mul_assoc, h3, ← Finset.mul_sum, h4]
  simp [mul_comm]
end GlobalTheory.SplitFlip.Model
