-- Prove2me | solution 1 for IAFTRL.lemma_C_3_cstar_bound
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:08:38.682214+00:00
-- url     : https://prove2.me/submissions/aa511bc3-6668-492e-b5cc-4718fafb4aa5

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsUniqueMin
import Theorems.Thm_IAFTRL_lemma_J_3_finite

open Matrix IAFTRL

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀)
    (hΔ : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) :
    BanditAlgorithm.linearBanditAllocationValue arms (-θ) ≤ 2 * (d : ℝ) / Δ₀ := by
  classical
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- the loss gaps `Δ(a_j)`, and the gap function of the rewards convention at `-θ`
  set gap : Fin K → ℝ := fun j => (arms j - arms jstar) ⬝ᵥ θ with hgapdef
  have hsup : (⨆ j', arms j' ⬝ᵥ -θ) = arms jstar ⬝ᵥ -θ := by
    have : Nonempty (Fin K) := ⟨jstar⟩
    apply le_antisymm
    · apply ciSup_le
      intro j'
      by_cases h : j' = jstar
      · rw [h]
      · have := hu j' h
        simp only [dotProduct_neg]
        linarith
    · exact le_ciSup (f := fun j' => arms j' ⬝ᵥ -θ) (Set.finite_range _).bddAbove jstar
  have hgap : ∀ j, BanditAlgorithm.linearArmGap arms (-θ) j = gap j := by
    intro j
    simp only [BanditAlgorithm.linearArmGap]
    rw [hsup]
    simp only [gap, dotProduct_neg, sub_dotProduct]
    ring
  have hgap_star : gap jstar = 0 := by simp [gap]
  have hgap_nonneg : ∀ j, 0 ≤ gap j := by
    intro j
    by_cases h : j = jstar
    · rw [h, hgap_star]
    · exact hΔ₀.le.trans (hΔ j h)
  -- rescale each action by its gap (by `Δ₀` for `a*`)
  set s : Fin K → ℝ := fun j => if j = jstar then Δ₀ else gap j with hsdef
  have hspos : ∀ j, 0 < s j := by
    intro j
    by_cases h : j = jstar
    · simp [s, h, hΔ₀]
    · simp only [s, h, if_false]
      exact lt_of_lt_of_le hΔ₀ (hΔ j h)
  have hs_gap : ∀ j, j ≠ jstar → s j = gap j := fun j h => by simp [s, h]
  set b : Fin K → Fin d → ℝ := fun j => (s j)⁻¹ • arms j with hbdef
  have hab : ∀ j, arms j = s j • b j := by
    intro j
    simp [b, smul_smul, (hspos j).ne']
  have hspanb : Submodule.span ℝ (Set.range b) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hA.2.2]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [hab j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- a G-optimal law for the rescaled actions
  obtain ⟨π, hπ0, hπ1, hπPD, hπG⟩ := lemma_J_3_finite hd b hspanb
  set V := BanditAlgorithm.linearAllocationMatrix b π with hVdef
  -- the allocation `n_j = 2d π_j / s_j²`
  set n : Fin K → ℝ := fun j => 2 * d * π j / (s j) ^ 2 with hndef
  have hn0 : ∀ j, 0 ≤ n j := fun j => by
    have := hπ0 j
    positivity
  have hH : BanditAlgorithm.linearAllocationMatrix arms n = (2 * (d : ℝ)) • V := by
    simp only [BanditAlgorithm.linearAllocationMatrix, V, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hab j, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul]
    congr 1
    have := (hspos j).ne'
    simp only [n]
    field_simp
  have hVunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hπPD.det_pos.ne'
  have hHinv : (BanditAlgorithm.linearAllocationMatrix arms n)⁻¹ = (2 * (d : ℝ))⁻¹ • V⁻¹ := by
    rw [hH]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul V hVunit, smul_smul,
      inv_mul_cancel₀ (by positivity), one_smul]
  -- `n` is feasible for the program defining `c*`
  have hfeas : n ∈ {α : Fin K → ℝ | (∀ j, 0 ≤ α j) ∧
      (BanditAlgorithm.linearAllocationMatrix arms α).PosDef ∧
      ∀ j, 0 < BanditAlgorithm.linearArmGap arms (-θ) j →
        arms j ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms α)⁻¹ *ᵥ arms j ≤
          BanditAlgorithm.linearArmGap arms (-θ) j ^ 2 / 2} := by
    refine ⟨hn0, ?_, ?_⟩
    · rw [hH]
      exact hπPD.smul (by positivity)
    · intro j hj
      rw [hgap j] at hj ⊢
      have hjs : j ≠ jstar := by
        rintro rfl
        rw [hgap_star] at hj
        exact lt_irrefl _ hj
      have hq := hπG j
      rw [hHinv, hab j, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← hs_gap j hjs]
      calc s j * ((2 * (d : ℝ))⁻¹ * (s j * (b j ⬝ᵥ V⁻¹ *ᵥ b j)))
          = s j ^ 2 / (2 * d) * (b j ⬝ᵥ V⁻¹ *ᵥ b j) := by ring
        _ ≤ s j ^ 2 / (2 * d) * d := mul_le_mul_of_nonneg_left hq (by positivity)
        _ = s j ^ 2 / 2 := by field_simp
  -- its cost is at most `2d/Δ₀`
  have hcost : ∑ j, n j * BanditAlgorithm.linearArmGap arms (-θ) j ≤ 2 * (d : ℝ) / Δ₀ := by
    calc ∑ j, n j * BanditAlgorithm.linearArmGap arms (-θ) j
        ≤ ∑ j, 2 * (d : ℝ) / Δ₀ * π j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hgap j]
          by_cases hjs : j = jstar
          · rw [hjs, hgap_star, mul_zero]
            have := hπ0 jstar
            positivity
          · have hsj := hspos j
            have hsg := hs_gap j hjs
            calc n j * gap j = 2 * d * π j / s j := by
                  rw [← hsg]; simp only [n]; field_simp
              _ ≤ 2 * d * π j / Δ₀ := by
                  apply div_le_div_of_nonneg_left (by have := hπ0 j; positivity) hΔ₀
                  rw [hsg]; exact hΔ j hjs
              _ = 2 * (d : ℝ) / Δ₀ * π j := by ring
      _ = 2 * (d : ℝ) / Δ₀ := by rw [← Finset.mul_sum, hπ1, mul_one]
  -- `c*` is an infimum of nonnegative costs, attained-or-not, below the cost of `n`
  refine le_trans (csInf_le ?_ ⟨n, hfeas, rfl⟩) hcost
  refine ⟨0, ?_⟩
  rintro _ ⟨α, ⟨hα0, -, -⟩, rfl⟩
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hα0 j) (by rw [hgap j]; exact hgap_nonneg j)
