-- Prove2me | solution 1 for LimitedPriceChanges.AlgorithmI.eq_25
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:56:34.459598+00:00
-- url     : https://prove2.me/submissions/00691df8-571a-4db2-acb7-875f9f8dce21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm
import Theorems.Thm_LimitedPriceChanges_AlgorithmI_stage_estimation_regret

namespace LPC25Aux

open LimitedPriceChanges.AlgorithmI

variable {S : Model} (A : Alg S)

theorem stageStart_mono (T : ℕ) {a b : ℕ} (hab : a ≤ b) : A.stageStart T a ≤ A.stageStart T b := by
  unfold Alg.stageStart
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hab)

theorem stageStart_succ (T i : ℕ) (hi : 1 ≤ i) :
    A.stageStart T (i + 1) = A.stageStart T i + A.stageLen T i := by
  unfold Alg.stageStart
  rw [Finset.sum_Ico_succ_top hi]

theorem stageOf_le (T s : ℕ) : A.stageOf T s ≤ A.m + 1 := by
  unfold Alg.stageOf
  have := Finset.card_filter_le (Finset.Icc 1 A.m) (fun j => A.stageStart T (j + 1) ≤ s)
  simp at this
  omega

theorem one_le_stageOf (T s : ℕ) : 1 ≤ A.stageOf T s := by
  unfold Alg.stageOf; omega

/-- A period of stage `i ≥ 2` lies in `[tᵢ, tᵢ + Iᵢ)`, provided `t_{m+1} ≤ T` and `s < T`. -/
theorem mem_stage (T s i : ℕ) (hs : s < T) (hT : A.stageStart T (A.m + 1) ≤ T)
    (hi2 : 2 ≤ i) (hsi : A.stageOf T s = i) :
    A.stageStart T i ≤ s ∧ s < A.stageStart T i + A.stageLen T i := by
  have him : i ≤ A.m + 1 := hsi ▸ stageOf_le A T s
  set F := (Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ s) with hF
  have hcard : F.card = i - 1 := by
    unfold Alg.stageOf at hsi; rw [← hF] at hsi; omega
  constructor
  · by_contra hlt
    push Not at hlt
    have hsub : F ⊆ Finset.Icc 1 (i - 2) := by
      intro j hj
      rw [hF, Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]
      refine ⟨hj.1.1, ?_⟩
      by_contra hji
      have : A.stageStart T i ≤ A.stageStart T (j + 1) := stageStart_mono A T (by omega)
      omega
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_cases hile : i ≤ A.m
    · rw [← stageStart_succ A T i (by omega)]
      by_contra hge
      push Not at hge
      have hsub : Finset.Icc 1 i ⊆ F := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [hF, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hj.1, by omega⟩, ?_⟩
        exact (stageStart_mono A T (by omega)).trans hge
      have := Finset.card_le_card hsub
      simp at this
      omega
    · have hieq : i = A.m + 1 := by omega
      subst hieq
      have hlen : A.stageLen T (A.m + 1) = T - ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
        unfold Alg.stageLen; simp
      have hstart : A.stageStart T (A.m + 1) = ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
        unfold Alg.stageStart
        apply Finset.sum_congr (by ext j; simp [Finset.mem_Ico, Finset.mem_Icc])
        intro j hj
        simp [Finset.mem_Icc] at hj
        unfold Alg.stageLen
        rw [if_pos hj.2]
      rw [hlen]
      rw [hstart] at hT ⊢
      omega

/-- The number of periods of stage `i ≥ 2` is at most `Iᵢ`. -/
theorem card_stage (T i : ℕ) (hT : A.stageStart T (A.m + 1) ≤ T) (hi2 : 2 ≤ i) :
    ((Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card ≤
      A.stageLen T i := by
  have := Finset.card_le_card_of_injOn (fun s : Fin T => (s : ℕ))
    (s := (Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i))
    (t := Finset.Ico (A.stageStart T i) (A.stageStart T i + A.stageLen T i))
    (fun s hs => by
      have hs' : A.stageOf T (s : ℕ) = i := by simpa using hs
      have := mem_stage A T s i s.isLt hT hi2 hs'
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact this)
    (fun a _ b _ h => Fin.ext h)
  simpa using this


theorem stageStart_last (T : ℕ) :
    A.stageStart T (A.m + 1) = ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
  unfold Alg.stageStart
  apply Finset.sum_congr (by ext j; simp [Finset.mem_Ico, Finset.mem_Icc])
  intro j hj
  simp [Finset.mem_Icc] at hj
  unfold Alg.stageLen
  rw [if_pos hj.2]

/-- `T^{j/(m+1)} = u^j` with `u = T^{1/(m+1)}`. -/
theorem rpow_eq_pow (T : ℕ) (m j : ℕ) :
    (T : ℝ) ^ ((j : ℝ) / ((m : ℝ) + 1)) = ((T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

theorem u_pow_succ (T m : ℕ) :
    ((T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ (m + 1) = T := by
  rw [← rpow_eq_pow]
  have : ((m + 1 : ℕ) : ℝ) / ((m : ℝ) + 1) = 1 := by push_cast; field_simp
  rw [this, Real.rpow_one]

theorem u_ge (T m : ℕ) (hT : (2 * m) ^ (m + 1) ≤ T) :
    (2 * m : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  have h1 : ((2 * m : ℝ) ^ (m + 1)) ^ ((((m + 1 : ℕ) : ℝ))⁻¹) = 2 * m :=
    Real.pow_rpow_inv_natCast (by positivity) (by omega)
  have h2 : ((m + 1 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / ((m : ℝ) + 1) := by push_cast; ring
  rw [h2] at h1
  rw [← h1]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast hT

/-- For `u ≥ 2m`, the first `m` stages fit in the horizon. -/
theorem stages_fit (T : ℕ) (hm : 1 ≤ A.m) (hT : (2 * A.m) ^ (A.m + 1) ≤ T) :
    A.stageStart T (A.m + 1) ≤ T := by
  rw [stageStart_last]
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu2 : (2 * A.m : ℝ) ≤ u := u_ge T A.m hT
  have hm1 : (1 : ℝ) ≤ A.m := by exact_mod_cast hm
  have hu1 : 1 ≤ u := by linarith
  have hsum : (∑ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ)) ≤ A.m * (u ^ A.m + 1) := by
    have : ∀ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ) ≤ u ^ A.m + 1 := by
      intro j hj
      have hj := Finset.mem_Icc.mp hj
      unfold Alg.ceilLen
      rw [rpow_eq_pow, ← hu]
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u ^ j)
      have h2 : u ^ j ≤ u ^ A.m := pow_le_pow_right₀ hu1 hj.2
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    simp; ring_nf; exact le_refl _
  have hpow : (1 : ℝ) ≤ u ^ A.m := one_le_pow₀ hu1
  have hT' : (T : ℝ) = u * u ^ A.m := by rw [hu, ← pow_succ', u_pow_succ]
  have : (∑ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ)) ≤ T := by
    rw [hT']
    refine hsum.trans ?_
    nlinarith
  exact_mod_cast this

/-- `Iᵢ ≤ 2 T^{1/(m+1)} Iᵢ₋₁` and `Iᵢ₋₁ > 0` for `2 ≤ i ≤ m + 1`. -/
theorem ratio (T : ℕ) (hT1 : 1 ≤ T) (i : ℕ) (hi : i ∈ Finset.Icc 2 (A.m + 1)) :
    0 < (A.stageLen T (i - 1) : ℝ) ∧
    (A.stageLen T i : ℝ) ≤ 2 * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) * A.stageLen T (i - 1) := by
  have hi := Finset.mem_Icc.mp hi
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hT1) (by positivity)
  have hprev : u ^ (i - 1) ≤ (A.stageLen T (i - 1) : ℝ) := by
    unfold Alg.stageLen
    rw [if_pos (by omega)]
    unfold Alg.ceilLen
    rw [rpow_eq_pow, ← hu]
    exact Nat.le_ceil _
  have hpos : 0 < u ^ (i - 1) := by positivity
  refine ⟨lt_of_lt_of_le hpos hprev, ?_⟩
  have hcur : (A.stageLen T i : ℝ) ≤ 2 * u ^ i := by
    by_cases him : i ≤ A.m
    · unfold Alg.stageLen
      rw [if_pos him]
      unfold Alg.ceilLen
      rw [rpow_eq_pow, ← hu]
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u ^ i)
      have h2 : 1 ≤ u ^ i := one_le_pow₀ hu1
      linarith
    · have hieq : i = A.m + 1 := by omega
      have h1 : A.stageLen T i ≤ T := by
        unfold Alg.stageLen; rw [if_neg him]; omega
      have h2 : (T : ℝ) = u ^ i := by rw [hieq, hu, u_pow_succ]
      have h3 : (A.stageLen T i : ℝ) ≤ T := by exact_mod_cast h1
      have h4 : 0 ≤ u ^ i := by positivity
      linarith
  have hui : u ^ i = u * u ^ (i - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc (A.stageLen T i : ℝ) ≤ 2 * u ^ i := hcur
    _ = 2 * u * u ^ (i - 1) := by rw [hui]; ring
    _ ≤ 2 * u * A.stageLen T (i - 1) :=
      mul_le_mul_of_nonneg_left hprev (by positivity)

theorem expect_sum (z : ℝ) (T : ℕ) (F : Fin T → (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => ∑ s : Fin T, F s d) = ∑ s : Fin T, A.expect z T (F s) := by
  unfold Alg.expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

end LPC25Aux

open LimitedPriceChanges.AlgorithmI in
theorem solution (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) :
    ∃ K₃₃ : ℝ, 0 < K₃₃ ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      A.expect z T (fun d => ∑ s : Fin T,
          if 2 ≤ A.stageOf T s then
            ENNReal.ofReal (S.Gstar A.pstar z -
              S.G (A.phat T (A.stageOf T s) d) (A.yhat T (A.stageOf T s) d) z)
          else 0) ≤
        ENNReal.ofReal (K₃₃ * (A.m : ℝ) * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1))) := by
  obtain ⟨K₁₇, hK₁₇, T₀, hT₀⟩ := stage_estimation_regret S A z hS hA
  refine ⟨2 * K₁₇, by positivity, max T₀ ((2 * A.m) ^ (A.m + 1) + 1), fun T hT => ?_⟩
  have hTT₀ : T ≥ T₀ := le_of_max_le_left hT
  have hTbig : (2 * A.m) ^ (A.m + 1) ≤ T := by
    have := le_of_max_le_right hT; omega
  have hT1 : 1 ≤ T := by have := le_of_max_le_right hT; omega
  have hfit := LPC25Aux.stages_fit A T hA.one_le_m hTbig
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  rw [LPC25Aux.expect_sum]
  -- per-period bound
  let a : Fin T → ℝ := fun s =>
    if 2 ≤ A.stageOf T s then K₁₇ / (A.stageLen T (A.stageOf T s - 1) : ℝ) else 0
  have ha0 : ∀ s, 0 ≤ a s := by
    intro s; simp only [a]; split_ifs <;> positivity
  have hper : ∀ s : Fin T, A.expect z T (fun d =>
        if 2 ≤ A.stageOf T s then
          ENNReal.ofReal (S.Gstar A.pstar z -
            S.G (A.phat T (A.stageOf T s) d) (A.yhat T (A.stageOf T s) d) z)
        else 0) ≤ ENNReal.ofReal (a s) := by
    intro s
    simp only [a]
    split_ifs with h2
    · exact hT₀ T hTT₀ _ (Finset.mem_Icc.mpr ⟨h2, LPC25Aux.stageOf_le A T s⟩)
    · simp [Alg.expect]
  refine (Finset.sum_le_sum (fun s _ => hper s)).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => ha0 s)]
  apply ENNReal.ofReal_le_ofReal
  -- regroup by stage
  have hregroup : ∀ s : Fin T, a s = ∑ i ∈ Finset.Icc 2 (A.m + 1),
      (if A.stageOf T s = i then K₁₇ / (A.stageLen T (i - 1) : ℝ) else 0) := by
    intro s
    rw [Finset.sum_ite_eq]
    simp only [a, Finset.mem_Icc]
    have := LPC25Aux.stageOf_le A T s
    by_cases h2 : 2 ≤ A.stageOf T s
    · rw [if_pos h2, if_pos ⟨h2, this⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.1)]
  rw [Finset.sum_congr rfl (fun s _ => hregroup s), Finset.sum_comm]
  have hstage : ∀ i ∈ Finset.Icc 2 (A.m + 1),
      ∑ s : Fin T, (if A.stageOf T s = i then K₁₇ / (A.stageLen T (i - 1) : ℝ) else 0) ≤
        2 * K₁₇ * u := by
    intro i hi
    obtain ⟨hpos, hrat⟩ := LPC25Aux.ratio A T hT1 i hi
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard := LPC25Aux.card_stage A T i hfit (Finset.mem_Icc.mp hi).1
    have hcard' : (((Finset.univ : Finset (Fin T)).filter
        (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card : ℝ) ≤ A.stageLen T i := by
      exact_mod_cast hcard
    calc (((Finset.univ : Finset (Fin T)).filter
          (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card : ℝ) *
          (K₁₇ / (A.stageLen T (i - 1) : ℝ))
        ≤ (A.stageLen T i : ℝ) * (K₁₇ / (A.stageLen T (i - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ ≤ 2 * u * A.stageLen T (i - 1) * (K₁₇ / (A.stageLen T (i - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hrat (by positivity)
      _ = 2 * K₁₇ * u := by field_simp
  refine (Finset.sum_le_sum hstage).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : ((A.m + 1 + 1 - 2 : ℕ) : ℝ) = A.m := by
    rw [show A.m + 1 + 1 - 2 = A.m by omega]
  rw [this]
  ring_nf
  exact le_refl _
