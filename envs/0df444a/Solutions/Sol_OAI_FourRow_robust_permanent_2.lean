-- Prove2me | solution 2 for OAI.FourRow.robust_permanent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:00:26.994928+00:00
-- url     : https://prove2.me/submissions/bf2fe984-f96f-42ae-9471-cff0d341e41e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Permanent/Main.lean:L99-L111
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.FourRow.robust_permanent.
-- The statement is the platform stub (Theorems.Thm_OAI_FourRow_robust_permanent) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability
import Definitions.Def_OAI_Combinatorics_Permanent_Main
import Theorems.Thm_OAI_FourRow_normalized_perturbation
import Theorems.Thm_OAI_FourRow_normalized_product_norm_lower
import Theorems.Thm_OAI_FourRow_normalized_uniform_stability

-- ---- inline helpers from OAI.Combinatorics.Permanent.Stability ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Quantitative exponent-two stability estimates. -/
theorem rowSq_nonneg (a : Site → ℝ) : 0 ≤ rowSq a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rowDist_nonneg (a : Site → ℝ) : 0 ≤ rowDist a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem totalDist_nonneg (f : Functions) : 0 ≤ totalDist f :=
  Finset.sum_nonneg fun i _ => rowDist_nonneg (f i)

end FourRow
end

end OAI

-- ---- inline helpers from OAI.Combinatorics.Permanent.Norm ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Below-two control by the tangent bound for the exponential. -/
theorem lpNorm_nonneg (p : ℝ) (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j) :
    0 ≤ lpNorm p a :=
  Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg
    (ha j) _) (by norm_num)) _

end FourRow
end

end OAI

-- ---- inline helpers from OAI.Combinatorics.Permanent.Main ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

theorem normalized_robust_permanent (ν : Law) (hp : IsProbability ν)
    (hm : UniformMarginals ν) (htv : totalVariation ν < robustRadius)
    (f : Functions) (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation ν f ≤ ∏ i, lpNorm strictExponent (f i) := by
  have h1 := normalized_uniform_stability f hf hn
  have h2 := normalized_perturbation ν hp hm f hf hn
  have h3 := normalized_product_norm_lower strictExponent (by norm_num [strictExponent])
    (by norm_num [strictExponent]) f hf hn
  have hd := totalDist_nonneg f
  have ht := mul_le_mul_of_nonneg_right (le_of_lt htv) hd
  dsimp [robustRadius] at ht
  dsimp [strictExponent] at h3 ⊢
  linarith

/- Homogeneity extends the bound to unrestricted nonnegative rows. -/
theorem lpNorm_scale (p : ℝ) (hp : p ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j) :
    lpNorm p (fun j => c * a j) = c * lpNorm p a := by
  unfold lpNorm
  simp_rw [Real.mul_rpow hc (ha _)]
  rw [← Finset.mul_sum, mul_div_assoc]
  rw [Real.mul_rpow (Real.rpow_nonneg hc p)
    (div_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (ha j) p)) (by norm_num))]
  rw [← Real.rpow_mul hc, one_div, mul_inv_cancel₀ hp, Real.rpow_one]

theorem expectation_scale (ν : Law) (c : Site → ℝ) (f : Functions) :
    permanentExpectation ν (fun i j => c i * f i j) =
      (∏ i, c i) * permanentExpectation ν f := by
  unfold permanentExpectation
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  ring

theorem rowSq_zero_entries (a : Site → ℝ) (h : rowSq a = 0) : ∀ j, a j = 0 := by
  intro j
  have hs : a j ^ 2 ≤ rowSq a :=
    Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ j)
  rw [h] at hs
  nlinarith [sq_nonneg (a j)]

theorem robust_permanent_explicit (ν : Law) (hp : IsProbability ν)
    (htv : totalVariation ν < robustRadius) (hm : UniformMarginals ν)
    (f : Functions) (hf : ∀ i j, 0 ≤ f i j) :
    permanentExpectation ν f ≤ ∏ i, lpNorm strictExponent (f i) := by
  by_cases hz : ∃ i, rowSq (f i) = 0
  · obtain ⟨i, hi⟩ := hz
    have hf0 := rowSq_zero_entries (f i) hi
    have hprod (π : Perm) : ∏ k, f k (π k) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hf0 (π i))
    have hexp : permanentExpectation ν f = 0 := by
      simp only [permanentExpectation, hprod, mul_zero, Finset.sum_const_zero]
    rw [hexp]
    exact Finset.prod_nonneg (fun k _ => lpNorm_nonneg _ _ (hf k))
  · have hspos (i : Site) : 0 < rowSq (f i) := by
      have := rowSq_nonneg (f i)
      have : rowSq (f i) ≠ 0 := fun hi => hz ⟨i, hi⟩
      positivity
    let c : Site → ℝ := fun i => Real.sqrt (rowSq (f i) / 4)
    have hcpos (i : Site) : 0 < c i := Real.sqrt_pos.2 (div_pos (hspos i) (by norm_num))
    have hc0 (i : Site) : 0 ≤ c i := le_of_lt (hcpos i)
    have hcne (i : Site) : c i ≠ 0 := ne_of_gt (hcpos i)
    have hcsq (i : Site) : c i ^ 2 = rowSq (f i) / 4 :=
      Real.sq_sqrt (div_nonneg (le_of_lt (hspos i)) (by norm_num))
    let g : Functions := fun i j => f i j / c i
    have hg0 (i j : Site) : 0 ≤ g i j := div_nonneg (hf i j) (hc0 i)
    have hgn (i : Site) : rowSq (g i) = 4 := by
      dsimp [rowSq, g]
      simp_rw [div_pow, ← Finset.sum_div]
      change rowSq (f i) / c i ^ 2 = 4
      rw [hcsq]
      field_simp [ne_of_gt (hspos i)]
    have heq : f = fun i j => c i * g i j := by
      funext i j
      dsimp [g]
      field_simp [hcne i]
    have h := normalized_robust_permanent ν hp hm htv g hg0 hgn
    have hcprod : 0 ≤ ∏ i, c i := Finset.prod_nonneg (fun i _ => hc0 i)
    have hscaled := mul_le_mul_of_nonneg_left h hcprod
    rw [heq, expectation_scale]
    simp_rw [lpNorm_scale strictExponent (by norm_num [strictExponent]) _ (hc0 _) _ (hg0 _)]
    rw [Finset.prod_mul_distrib]
    exact hscaled

end FourRow
end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.FourRow
open scoped BigOperators

theorem solution :
  ∃ p₀ : ℝ, 4 / 3 < p₀ ∧ p₀ < 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Law,
      IsProbability ν → totalVariation ν < ε → UniformMarginals ν →
      ∀ f : Functions, (∀ i j, 0 ≤ f i j) →
        permanentExpectation ν f ≤ ∏ i, lpNorm p₀ (f i) := by
  refine ⟨strictExponent, ?_, ?_, robustRadius, ?_, ?_⟩
  · norm_num [strictExponent]
  · norm_num [strictExponent]
  · norm_num [robustRadius]
  · intro ν hp htv hm f hf
    exact robust_permanent_explicit ν hp htv hm f hf
