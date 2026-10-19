-- Prove2me | solution 1 for GilesMLMC.Complexity.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T22:00:13.97244+00:00
-- url     : https://prove2.me/submissions/fbe2ad8a-f246-41be-99e6-f3eaf10fa116

-- Licensed under Apache 2.0. Complete multilevel Monte Carlo complexity theorem.
import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup


open GilesMLMC.Complexity

namespace MLMCProof

noncomputable def levelSum (M : ℕ) (T β : ℝ) (L : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (L + 1), (h M T l) ^ ((β - 1) / 2)

noncomputable def roundingSum (M : ℕ) (T : ℝ) (L : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹

end MLMCProof


open GilesMLMC.Complexity
open scoped BigOperators

namespace MLMCProof

theorem refinement_pos {M : ℕ} (hM : 2 ≤ M) : (0 : ℝ) < M := by
  exact_mod_cast (show 0 < M by omega)

theorem refinement_one_lt {M : ℕ} (hM : 2 ≤ M) : (1 : ℝ) < M := by
  exact_mod_cast (show 1 < M by omega)

theorem timestep_pos {M : ℕ} (hM : 2 ≤ M) {T : ℝ} (hT : 0 < T) (l : ℕ) :
    0 < h M T l := div_pos hT (pow_pos (refinement_pos hM) _)

theorem timestep_succ (M : ℕ) (T : ℝ) (l : ℕ) :
    h M T (l+1) = h M T l / M := by
  simp only [h, pow_succ, div_div]

theorem timestep_power {M : ℕ} (hM : 2 ≤ M) {T : ℝ} (hT : 0 < T)
    (l : ℕ) (a : ℝ) :
    (h M T l) ^ a = T ^ a * ((M : ℝ) ^ (-a)) ^ l := by
  rw [h, Real.div_rpow hT.le (pow_nonneg (refinement_pos hM).le _),
    ← Real.rpow_pow_comm (refinement_pos hM).le,
    Real.rpow_neg (refinement_pos hM).le, inv_pow, div_eq_mul_inv]

theorem timestep_log {M : ℕ} (hM : 2 ≤ M) {T : ℝ} (hT : 0 < T) (l : ℕ) :
    Real.log (h M T l) = Real.log T - (l : ℝ) * Real.log M := by
  rw [h, Real.log_div hT.ne' (pow_ne_zero _ (refinement_pos hM).ne'), Real.log_pow]

theorem ratio_between {M : ℕ} (hM : 2 ≤ M) {a : ℝ} (ha : 0 < a) :
    0 < (M : ℝ) ^ (-a) ∧ (M : ℝ) ^ (-a) < 1 :=
  ⟨Real.rpow_pos_of_pos (refinement_pos hM) _,
    Real.rpow_lt_one_of_one_lt_of_neg (refinement_one_lt hM) (neg_neg_of_pos ha)⟩

theorem finite_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    (∑ l ∈ Finset.range (L+1), r ^ l) ≤ (1-r)⁻¹ := by
  have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := L+1) hr0 hr1
  simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using hh

theorem positive_power_sum_le {M : ℕ} (hM : 2 ≤ M) {T : ℝ} (hT : 0 < T)
    {a : ℝ} (ha : 0 < a) (L : ℕ) :
    (∑ l ∈ Finset.range (L+1), (h M T l)^a) ≤
      T^a * (1-(M : ℝ)^(-a))⁻¹ := by
  simp_rw [timestep_power hM hT]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (finite_geom_le (ratio_between hM ha).1.le (ratio_between hM ha).2 L)
    (Real.rpow_nonneg hT.le _)

end MLMCProof


open GilesMLMC.Complexity

namespace MLMCProof

theorem epsilon_log_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    1 < -Real.log ε := by
  have hh := Real.log_lt_log hε hε1
  rw [Real.log_exp] at hh
  linarith

theorem finest_level_bounds {M : ℕ} (hM : 2 ≤ M) {T α c₁ : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hc₁ : 0 < c₁) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ L : ℕ, c₁ * (h M T L)^α ≤ ε/2 ∧
        (h M T L)⁻¹ ≤ A * ε^(-1/α) ∧
        ((L : ℝ)+1) ≤ B * (-Real.log ε) := by
  let K := |Real.log (2*c₁) + α * Real.log T|
  let d := α * Real.log (M : ℝ)
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (refinement_one_lt hM)
  have hd : 0 < d := mul_pos hα hlog
  have hK : 0 ≤ K := abs_nonneg _
  let A := Real.exp (K/α + Real.log M - Real.log T)
  let B := (K+1)/d+2
  have hA : 0 < A := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro ε hε hε1
  have he := epsilon_log_bound hε hε1
  let x := (Real.log (2*c₁)+α*Real.log T-Real.log ε)/d
  let y := (K-Real.log ε)/d
  let L := ⌈x⌉₊
  have hxy : x ≤ y := by
    apply div_le_div_of_nonneg_right _ hd.le
    dsimp [K]
    linarith [le_abs_self (Real.log (2*c₁)+α*Real.log T)]
  have hy : 0 ≤ y := div_nonneg (by linarith) hd.le
  have hlower : x ≤ (L : ℝ) := Nat.le_ceil x
  have hupper : (L : ℝ) < y+1 :=
    (Nat.cast_le.mpr (Nat.ceil_mono hxy)).trans_lt (Nat.ceil_lt_add_one hy)
  have hlo : Real.log (2*c₁)+α*Real.log T-Real.log ε ≤ (L : ℝ)*d :=
    (div_le_iff₀ hd).mp hlower
  have hup : (L : ℝ)*d < K-Real.log ε+d := by
    have hh := (lt_div_iff₀ hd).mp (show (L : ℝ)-1 < (K-Real.log ε)/d by
      dsimp [y] at hupper; linarith)
    nlinarith
  refine ⟨L, ?_, ?_, ?_⟩
  · have hh : 2*c₁*(h M T L)^α ≤ ε := by
      apply (Real.log_le_log_iff (mul_pos (mul_pos (by norm_num) hc₁)
        (Real.rpow_pos_of_pos (timestep_pos hM hT L) α)) hε).mp
      rw [Real.log_mul (by positivity : (2*c₁ : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos (timestep_pos hM hT L) α).ne',
        Real.log_rpow (timestep_pos hM hT L), timestep_log hM hT]
      dsimp [d] at hlo
      nlinarith
    linarith
  · apply (Real.log_le_log_iff (inv_pos.mpr (timestep_pos hM hT L))
      (mul_pos hA (Real.rpow_pos_of_pos hε _))).mp
    rw [Real.log_inv, timestep_log hM hT,
      Real.log_mul hA.ne' (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε]
    have hla : Real.log A = K/α+Real.log M-Real.log T := Real.log_exp _
    rw [hla]
    have hh : (L : ℝ)*Real.log M ≤ K/α-Real.log ε/α+Real.log M := by
      apply (mul_le_mul_iff_right₀ hα).mp
      dsimp [d] at hup
      field_simp
      nlinarith [hup.le]
    calc
      -(Real.log T-(L : ℝ)*Real.log M) ≤
        -Real.log T+(K/α-Real.log ε/α+Real.log M) := by linarith
      _ = K/α+Real.log M-Real.log T+(-1/α)*Real.log ε := by ring
  · have hh : (L : ℝ)+1 ≤ (K-Real.log ε)/d+2 := by
      dsimp [y] at hupper
      linarith
    apply hh.trans
    dsimp [B]
    have hKmul : K ≤ K*(-Real.log ε) := le_mul_of_one_le_right hK he.le
    have hdiv : (K-Real.log ε)/d ≤ ((K+1)/d)*(-Real.log ε) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hd.le
      nlinarith
    nlinarith

end MLMCProof


open GilesMLMC.Complexity
open scoped BigOperators

namespace MLMCProof

theorem timestep_reverse {M : ℕ} (hM : 2 ≤ M) (T : ℝ) {L l : ℕ} (hl : l ≤ L) :
    h M T (L-l) = h M T L * (M : ℝ)^l := by
  rw [h, h, pow_sub₀ _ (refinement_pos hM).ne' hl]
  field_simp

theorem negative_power_sum_le {M : ℕ} (hM : 2 ≤ M) {T : ℝ} (hT : 0 < T)
    {a : ℝ} (ha : 0 < a) (L : ℕ) :
    (∑ l ∈ Finset.range (L+1), (h M T l)^(-a)) ≤
      (h M T L)^(-a) * (1-(M : ℝ)^(-a))⁻¹ := by
  rw [← Finset.sum_range_reflect (fun l => (h M T l)^(-a)) (L+1)]
  have he : (∑ l ∈ Finset.range (L+1), (h M T (L+1-1-l))^(-a)) =
      (h M T L)^(-a) * ∑ l ∈ Finset.range (L+1), ((M : ℝ)^(-a))^l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Nat.add_sub_cancel]
    rw [timestep_reverse hM T (by have := Finset.mem_range.mp hl; omega),
      Real.mul_rpow (timestep_pos hM hT L).le (pow_nonneg (refinement_pos hM).le _),
      ← Real.rpow_pow_comm (refinement_pos hM).le]
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (finite_geom_le (ratio_between hM ha).1.le (ratio_between hM ha).2 L)
    (Real.rpow_nonneg (timestep_pos hM hT L).le _)

theorem rounding_sum_le {M : ℕ} (hM : 2 ≤ M) {T : ℝ} (hT : 0 < T) (L : ℕ) :
    roundingSum M T L ≤ (h M T L)⁻¹ * (1-(M : ℝ)⁻¹)⁻¹ := by
  simpa only [roundingSum, Real.rpow_neg_one] using
    negative_power_sum_le hM hT (a := 1) (by norm_num) L

theorem level_sum_supercritical {M : ℕ} (hM : 2 ≤ M) {T β : ℝ}
    (hT : 0 < T) (hβ : 1 < β) (L : ℕ) :
    levelSum M T β L ≤ T^((β-1)/2) * (1-(M : ℝ)^(-((β-1)/2)))⁻¹ :=
  positive_power_sum_le hM hT (by linarith) L

theorem level_sum_critical (M : ℕ) (T : ℝ) (L : ℕ) :
    levelSum M T 1 L = (L : ℝ)+1 := by
  simp [levelSum]

theorem level_sum_subcritical {M : ℕ} (hM : 2 ≤ M) {T β : ℝ}
    (hT : 0 < T) (hβ : β < 1) (L : ℕ) :
    levelSum M T β L ≤ (h M T L)^(-((1-β)/2)) *
      (1-(M : ℝ)^(-((1-β)/2)))⁻¹ := by
  have he : (β-1)/2 = -((1-β)/2) := by ring
  simpa only [levelSum, he] using negative_power_sum_le hM hT (by linarith : 0 < (1-β)/2) L

end MLMCProof


open GilesMLMC.Complexity
open scoped BigOperators

namespace MLMCProof

theorem epsilon_lt_one {ε : ℝ} (hε1 : ε < Real.exp (-1)) : ε < 1 :=
  hε1.trans (by rw [Real.exp_lt_one_iff]; norm_num)

theorem rounding_rate {M : ℕ} (hM : 2 ≤ M) {T α A ε : ℝ}
    (hT : 0 < T) (hα : 1/2 ≤ α) (hA : 0 < A) (hε : 0 < ε)
    (hε1 : ε < Real.exp (-1)) (L : ℕ)
    (hinv : (h M T L)⁻¹ ≤ A*ε^(-1/α)) :
    roundingSum M T L ≤ (A*(1-(M : ℝ)⁻¹)⁻¹)*ε^(-2 : ℝ) := by
  have hα0 : 0 < α := by linarith
  have hc : 0 ≤ (1-(M : ℝ)⁻¹)⁻¹ := by
    apply inv_nonneg.mpr
    have hh : (M : ℝ)⁻¹ < 1 := (inv_lt_one₀ (refinement_pos hM)).mpr (refinement_one_lt hM)
    linarith
  have hp : ε^(-1/α) ≤ ε^(-2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_ge hε (epsilon_lt_one hε1).le
    apply (le_div_iff₀ hα0).mpr
    linarith
  calc
    roundingSum M T L ≤ (h M T L)⁻¹*(1-(M : ℝ)⁻¹)⁻¹ := rounding_sum_le hM hT L
    _ ≤ (A*ε^(-1/α))*(1-(M : ℝ)⁻¹)⁻¹ := mul_le_mul_of_nonneg_right hinv hc
    _ ≤ (A*ε^(-2 : ℝ))*(1-(M : ℝ)⁻¹)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA.le) hc
    _ = _ := by ring

theorem level_sum_nonneg {M : ℕ} (hM : 2 ≤ M) {T : ℝ} (hT : 0 < T)
    (β : ℝ) (L : ℕ) : 0 ≤ levelSum M T β L := by
  apply Finset.sum_nonneg
  intro l _
  exact Real.rpow_nonneg (timestep_pos hM hT l).le _

theorem negative_power_sq_bound {x A ε α a : ℝ} (hx : 0 < x) (hA : 0 < A)
    (hε : 0 < ε) (ha : 0 ≤ a) (hinv : x⁻¹ ≤ A*ε^(-1/α)) :
    (x^(-a))^2 ≤ A^(2*a)*ε^(-2*a/α) := by
  have hh := Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hinv (by positivity : 0 ≤ 2*a)
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hε.le _),
    ← Real.rpow_mul hε.le] at hh
  have hl : (x^(-a))^2 = (x⁻¹)^(2*a) := by
    rw [Real.rpow_neg_eq_inv_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hx.le)]
    congr 1
    ring
  rw [hl]
  convert hh using 1
  congr 2
  ring

theorem subcritical_square_rate {M : ℕ} (hM : 2 ≤ M) {T β A ε α : ℝ}
    (hT : 0 < T) (hβ : β < 1) (hA : 0 < A) (hε : 0 < ε) (L : ℕ)
    (hinv : (h M T L)⁻¹ ≤ A*ε^(-1/α)) :
    (levelSum M T β L)^2 ≤
      (A^(1-β)*(((1-(M : ℝ)^(-((1-β)/2)))⁻¹)^2)) * ε^(-(1-β)/α) := by
  let a := (1-β)/2
  have ha : 0 < a := by dsimp [a]; linarith
  let D := (1-(M : ℝ)^(-a))⁻¹
  have hD : 0 ≤ D := inv_nonneg.mpr (sub_nonneg.mpr (ratio_between hM ha).2.le)
  have hsum : levelSum M T β L ≤ (h M T L)^(-a)*D := level_sum_subcritical hM hT hβ L
  have hsq := (sq_le_sq₀ (level_sum_nonneg hM hT β L)
    (mul_nonneg (Real.rpow_nonneg (timestep_pos hM hT L).le _) hD)).mpr hsum
  have hp := negative_power_sq_bound (timestep_pos hM hT L) hA hε ha.le hinv
  rw [mul_pow] at hsq
  have hh := hsq.trans (mul_le_mul_of_nonneg_right hp (sq_nonneg D))
  have he : 2*a = 1-β := by dsimp [a]; ring
  have he' : -2*a/α = -(1-β)/α := by rw [show -2*a = -(2*a) by ring, he]
  rw [he, he'] at hh
  dsimp [D, a] at hh
  nlinarith [hh]

end MLMCProof


open GilesMLMC.Complexity

namespace MLMCProof

private theorem cost_lift {C k R S V H D W : ℝ} (hk : 0 ≤ k) (hR : 0 ≤ R)
    (hH : 0 ≤ H) (hW : 1 ≤ W)
    (hcost : C ≤ k*R*S+V) (hs : S ≤ D*W) (hv : V ≤ H*R) :
    C ≤ (k*D+H+1)*R*W := by
  have hmain := mul_le_mul_of_nonneg_left hs (mul_nonneg hk hR)
  have hround : H*R ≤ H*R*W := le_mul_of_one_le_right (mul_nonneg hH hR) hW
  have hpos : 0 ≤ R*W := mul_nonneg hR (by linarith)
  nlinarith

theorem cost_rates {M : ℕ} (hM : 2 ≤ M) {T α β c₂ c₃ A B : ℝ}
    (hT : 0 < T) (hα : 1/2 ≤ α) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hA : 0 < A) (hB : 0 < B) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∀ L : ℕ, (h M T L)⁻¹ ≤ A*ε^(-1/α) →
      ((L : ℝ)+1) ≤ B*(-Real.log ε) → ∀ C : ℝ,
      C ≤ 4*c₂*c₃*ε^(-2 : ℝ)*(levelSum M T β L)^2+c₃*roundingSum M T L →
      (1 < β → C ≤ c₄*ε^(-2 : ℝ)) ∧
      (β = 1 → C ≤ c₄*ε^(-2 : ℝ)*(Real.log ε)^2) ∧
      (β < 1 → C ≤ c₄*ε^(-2-(1-β)/α)) := by
  let H := A*(1-(M : ℝ)⁻¹)⁻¹
  have hH : 0 < H := by
    apply mul_pos hA
    apply inv_pos.mpr
    exact sub_pos.mpr ((inv_lt_one₀ (refinement_pos hM)).mpr (refinement_one_lt hM))
  let k := 4*c₂*c₃
  have hk : 0 < k := by dsimp [k]; positivity
  have hr (ε : ℝ) (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) (L : ℕ)
      (hinv : (h M T L)⁻¹ ≤ A*ε^(-1/α)) :
      c₃*roundingSum M T L ≤ (c₃*H)*ε^(-2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (rounding_rate hM hT hα hA hε hε1 L hinv) hc₃.le
    dsimp [H]
    nlinarith [hh]
  rcases lt_trichotomy β 1 with hβ | hβ | hβ
  · let D := A^(1-β)*(((1-(M : ℝ)^(-((1-β)/2)))⁻¹)^2)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨k*D+c₃*H+1, by positivity, ?_⟩
    intro ε hε hε1 L hinv _ C hcost
    refine ⟨fun hh => False.elim (by linarith), fun hh => False.elim (by linarith), fun _ => ?_⟩
    have hW : 1 ≤ ε^(-(1-β)/α) := by
      have hα0 : 0 < α := by linarith
      have hh := Real.rpow_le_rpow_of_exponent_ge hε (epsilon_lt_one hε1).le
        (show -(1-β)/α ≤ (0 : ℝ) from
          div_nonpos_of_nonpos_of_nonneg (by linarith) hα0.le)
      simpa only [Real.rpow_zero] using hh
    have hs := subcritical_square_rate hM hT hβ hA hε L hinv
    have hh := cost_lift hk.le (Real.rpow_nonneg hε.le (-2))
      (mul_nonneg hc₃.le hH.le) hW hcost hs (hr ε hε hε1 L hinv)
    dsimp [k, D] at hh ⊢
    rw [mul_assoc, ← Real.rpow_add hε] at hh
    convert hh using 1
    congr 2
    ring
  · subst β
    refine ⟨k*B^2+c₃*H+1, by positivity, ?_⟩
    intro ε hε hε1 L hinv hlev C hcost
    refine ⟨fun hh => False.elim (by linarith), fun _ => ?_, fun hh => False.elim (by linarith)⟩
    have he := epsilon_log_bound hε hε1
    have hW : 1 ≤ (Real.log ε)^2 := by nlinarith
    have hs : (levelSum M T 1 L)^2 ≤ B^2*(Real.log ε)^2 := by
      rw [level_sum_critical]
      have hh := (sq_le_sq₀ (by positivity : 0 ≤ (L : ℝ)+1)
        (mul_nonneg hB.le (by linarith))).mpr hlev
      nlinarith [hh]
    exact cost_lift hk.le (Real.rpow_nonneg hε.le (-2))
      (mul_nonneg hc₃.le hH.le) hW hcost hs (hr ε hε hε1 L hinv)
  · let U := T^((β-1)/2)*(1-(M : ℝ)^(-((β-1)/2)))⁻¹
    have hU : 0 ≤ U := by
      apply mul_nonneg (Real.rpow_nonneg hT.le _)
      exact inv_nonneg.mpr (sub_nonneg.mpr (ratio_between hM (by linarith : 0 < (β-1)/2)).2.le)
    refine ⟨k*U^2+c₃*H+1, by positivity, ?_⟩
    intro ε hε hε1 L hinv _ C hcost
    refine ⟨fun _ => ?_, fun hh => False.elim (by linarith), fun hh => False.elim (by linarith)⟩
    have hs : (levelSum M T β L)^2 ≤ U^2*1 := by
      simpa only [mul_one] using (sq_le_sq₀ (level_sum_nonneg hM hT β L) hU).mpr
        (level_sum_supercritical hM hT hβ L)
    simpa only [mul_one] using cost_lift hk.le (Real.rpow_nonneg hε.le (-2))
      (mul_nonneg hc₃.le hH.le) (le_refl (1 : ℝ)) hcost hs (hr ε hε hε1 L hinv)

end MLMCProof


open MeasureTheory ProbabilityTheory GilesMLMC.Complexity

namespace MLMCProof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma estimator_memLp (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ → ℕ) (L : ℕ)
    (hY : ∀ l, MemLp (Y l (N l)) 2 μ) : MemLp (estimator Y N L) 2 μ :=
  memLp_finsetSum _ (fun l _ => hY l)

lemma estimator_expectation [IsFiniteMeasure μ] (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ → ℕ)
    (Phat : ℕ → Ω → ℝ)
    (hY : ∀ l, MemLp (Y l (N l)) 2 μ)
    (hPhat : ∀ l, Integrable (Phat l) μ)
    (he : ∀ l, ∫ ω, Y l (N l) ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else
        ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ) (L : ℕ) :
    ∫ ω, estimator Y N L ω ∂μ = ∫ ω, Phat L ω ∂μ := by
  have hs : ∀ K, (∑ l ∈ Finset.range (K + 1), ∫ ω, Y l (N l) ω ∂μ) =
      ∫ ω, Phat K ω ∂μ := by
    intro K
    induction K with
    | zero => simpa using he 0
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, he (K + 1)]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, integral_sub (hPhat (K + 1)) (hPhat K)]
      ring
  change (∫ ω, ∑ l ∈ Finset.range (L + 1), Y l (N l) ω ∂μ) = _
  rw [integral_finsetSum _ (fun l _ => (hY l).integrable one_le_two)]
  exact hs L

lemma estimator_variance (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ → ℕ) (L : ℕ)
    (hY : ∀ l, MemLp (Y l (N l)) 2 μ)
    (hi : iIndepFun (fun l => Y l (N l)) μ) :
    variance (estimator Y N L) μ =
      ∑ l ∈ Finset.range (L + 1), variance (Y l (N l)) μ := by
  have hh := IndepFun.variance_sum (s := Finset.range (L + 1))
    (fun l _ => hY l) (fun _ _ _ _ hne => hi.indepFun hne)
  have heq : estimator Y N L = ∑ l ∈ Finset.range (L + 1), Y l (N l) := by
    ext ω
    simp only [GilesMLMC.Complexity.estimator, Finset.sum_apply]
  rw [heq]
  exact hh

lemma mse_decomposition [IsProbabilityMeasure μ] {X P : Ω → ℝ}
    (hX : MemLp X 2 μ) :
    mse μ X P = variance X μ + (∫ ω, X ω ∂μ - ∫ ω, P ω ∂μ) ^ 2 := by
  have hx := hX.sub (memLp_const (∫ ω, P ω ∂μ))
  have hv := variance_eq_sub hx
  change variance (fun ω => X ω - ∫ ω', P ω' ∂μ) μ =
    mse μ X P - (∫ ω, X ω - (∫ ω', P ω' ∂μ) ∂μ) ^ 2 at hv
  rw [variance_sub_const hX.aestronglyMeasurable] at hv
  have he : (∫ ω, X ω - (∫ ω', P ω' ∂μ) ∂μ) =
      (∫ ω, X ω ∂μ) - ∫ ω, P ω ∂μ := by
    rw [integral_sub (hX.integrable one_le_two) (integrable_const _)]
    simp
  change variance X μ = mse μ X P - (∫ ω, X ω - (∫ ω', P ω' ∂μ) ∂μ) ^ 2 at hv
  rw [he] at hv
  linarith

end MLMCProof


open GilesMLMC.Complexity

namespace MLMCProof

noncomputable def sampleSize (M : ℕ) (T β c ε : ℝ) (L l : ℕ) : ℕ :=
  ⌈4 * c * ε ^ (-2 : ℝ) * levelSum M T β L *
    h M T l ^ ((β + 1) / 2)⌉₊

lemma levelSum_pos {M : ℕ} {T β : ℝ} (hM : 0 < M) (hT : 0 < T) (L : ℕ) :
    0 < levelSum M T β L := by
  apply Finset.sum_pos
  · intro l _
    exact Real.rpow_pos_of_pos (div_pos hT (pow_pos (by exact_mod_cast hM) l)) _
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

lemma sampleSize_pos {M : ℕ} {T β c ε : ℝ} (hM : 0 < M) (hT : 0 < T)
    (hc : 0 < c) (hε : 0 < ε) (L l : ℕ) : 1 ≤ sampleSize M T β c ε L l := by
  apply Nat.one_le_ceil_iff.mpr
  have hh : 0 < h M T l := div_pos hT (pow_pos (by exact_mod_cast hM) l)
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hc)
    (Real.rpow_pos_of_pos hε _)) (levelSum_pos hM hT L))
    (Real.rpow_pos_of_pos hh _)

lemma allocation_scalar {u c ε S β : ℝ} (hu : 0 < u) (hc : 0 < c)
    (hε : 0 < ε) (hS : 0 < S) {N : ℕ}
    (hN : 4 * c * ε ^ (-2 : ℝ) * S * u ^ ((β + 1) / 2) ≤ N) :
    c * (N : ℝ)⁻¹ * u ^ β ≤ ε ^ 2 / (4 * S) * u ^ ((β - 1) / 2) := by
  have he : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_two]
  have hp := Real.rpow_pos_of_pos hu ((β + 1) / 2)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le
    (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hc)
      (Real.rpow_pos_of_pos hε _)) hS) hp) hN
  have hid : u ^ ((β + 1) / 2) * u ^ ((β - 1) / 2) = u ^ β := by
    rw [← Real.rpow_add hu]; congr 1; ring
  rw [he] at hN
  have hmul := mul_le_mul_of_nonneg_right hN
    (le_of_lt (Real.rpow_pos_of_pos hu ((β - 1) / 2)))
  rw [mul_assoc (4 * c * (ε ^ 2)⁻¹ * S), hid] at hmul
  rw [show c * (N : ℝ)⁻¹ * u ^ β = (c * u ^ β) / N by ring]
  apply (div_le_iff₀ hNpos).mpr
  calc
    c * u ^ β = (4 * c * (ε ^ 2)⁻¹ * S * u ^ β) * (ε ^ 2 / (4 * S)) := by
      field_simp [ne_of_gt hε, ne_of_gt hS]
    _ ≤ ((N : ℝ) * u ^ ((β - 1) / 2)) * (ε ^ 2 / (4 * S)) :=
      mul_le_mul_of_nonneg_right hmul (by positivity)
    _ = ε ^ 2 / (4 * S) * u ^ ((β - 1) / 2) * N := by ring


end MLMCProof


open GilesMLMC.Complexity

namespace MLMCProof

lemma allocation_variance_bound {M : ℕ} {T β c ε : ℝ}
    (hM : 0 < M) (hT : 0 < T) (hc : 0 < c) (hε : 0 < ε) (L : ℕ) :
    (∑ l ∈ Finset.range (L + 1),
      c * (sampleSize M T β c ε L l : ℝ)⁻¹ * h M T l ^ β) ≤ ε ^ 2 / 4 := by
  have hs := levelSum_pos (β := β) hM hT L
  calc
    _ ≤ ∑ l ∈ Finset.range (L + 1),
        ε ^ 2 / (4 * levelSum M T β L) * h M T l ^ ((β - 1) / 2) := by
      apply Finset.sum_le_sum
      intro l _
      exact allocation_scalar (div_pos hT (pow_pos (by exact_mod_cast hM) l)) hc hε hs
        (Nat.le_ceil _)
    _ = ε ^ 2 / 4 := by
      rw [← Finset.mul_sum]
      change ε ^ 2 / (4 * levelSum M T β L) * levelSum M T β L = _
      field_simp

lemma allocation_cost_bound {M : ℕ} {T β c ε d : ℝ}
    (hM : 0 < M) (hT : 0 < T) (hc : 0 < c) (hε : 0 < ε)
    (hd : 0 < d) (L : ℕ) :
    (∑ l ∈ Finset.range (L + 1),
      d * (sampleSize M T β c ε L l : ℝ) * (h M T l)⁻¹) ≤
      4 * c * d * ε ^ (-2 : ℝ) * levelSum M T β L ^ 2 +
        d * roundingSum M T L := by
  have hs := levelSum_pos (β := β) hM hT L
  have hterm (l : ℕ) :
      d * (sampleSize M T β c ε L l : ℝ) * (h M T l)⁻¹ ≤
      (4 * c * d * ε ^ (-2 : ℝ) * levelSum M T β L) *
        h M T l ^ ((β - 1) / 2) + d * (h M T l)⁻¹ := by
    have hh : 0 < h M T l := div_pos hT (pow_pos (by exact_mod_cast hM) l)
    have ha : 0 ≤ 4 * c * ε ^ (-2 : ℝ) * levelSum M T β L *
        h M T l ^ ((β + 1) / 2) := by positivity
    have hn := (Nat.ceil_lt_add_one ha).le
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hd.le)
      (inv_nonneg.mpr hh.le)
    have hid : h M T l ^ ((β + 1) / 2) * (h M T l)⁻¹ =
        h M T l ^ ((β - 1) / 2) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hh]
      congr 1; ring
    change d * (sampleSize M T β c ε L l : ℝ) * (h M T l)⁻¹ ≤ _ at hmul
    calc
      _ ≤ d * (4 * c * ε ^ (-2 : ℝ) * levelSum M T β L *
          h M T l ^ ((β + 1) / 2) + 1) * (h M T l)⁻¹ := hmul
      _ = _ := by
        calc
          _ = (4 * c * d * ε ^ (-2 : ℝ) * levelSum M T β L) *
              (h M T l ^ ((β + 1) / 2) * (h M T l)⁻¹) + d * (h M T l)⁻¹ := by ring
          _ = _ := by rw [hid]
  calc
    _ ≤ ∑ l ∈ Finset.range (L + 1),
        ((4 * c * d * ε ^ (-2 : ℝ) * levelSum M T β L) *
          h M T l ^ ((β - 1) / 2) + d * (h M T l)⁻¹) :=
      Finset.sum_le_sum (fun l _ => hterm l)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change (4 * c * d * ε ^ (-2 : ℝ) * levelSum M T β L) * levelSum M T β L +
        d * roundingSum M T L = _
      ring

end MLMCProof


open MeasureTheory ProbabilityTheory GilesMLMC.Complexity

namespace MLMCProof

lemma estimator_mse_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ → ℕ)
    (Phat : ℕ → Ω → ℝ) (P : Ω → ℝ) (L : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hY : ∀ l, MemLp (Y l (N l)) 2 μ) (hP : Integrable P μ)
    (hPhat : ∀ l, Integrable (Phat l) μ)
    (he : ∀ l, ∫ ω, Y l (N l) ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else
        ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ)
    (hi : iIndepFun (fun l => Y l (N l)) μ)
    (hb : |∫ ω, Phat L ω - P ω ∂μ| ≤ ε / 2)
    (hv : (∑ l ∈ Finset.range (L + 1), variance (Y l (N l)) μ) ≤ ε ^ 2 / 4) :
    mse μ (estimator Y N L) P < ε ^ 2 := by
  rw [mse_decomposition (estimator_memLp Y N L hY),
    estimator_expectation Y N Phat hY hPhat he L, estimator_variance Y N L hY hi]
  rw [integral_sub (hPhat L) hP] at hb
  have hsq := sq_le_sq₀ (abs_nonneg ((∫ ω, Phat L ω ∂μ) - ∫ ω, P ω ∂μ))
    (by positivity : 0 ≤ ε / 2)
  have hh := hsq.mpr hb
  rw [sq_abs] at hh
  nlinarith [sq_pos_of_pos hε]

lemma chosen_estimators {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {M : ℕ} {T α β c₁ c₂ c₃ ε : ℝ} (hM : 0 < M) (hT : 0 < T)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hε : 0 < ε)
    (P : Ω → ℝ) (Phat : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (cost : ℕ → ℕ → ℝ)
    (hP : Integrable P μ) (hPhat : ∀ l, Integrable (Phat l) μ)
    (hY : ∀ l N, 1 ≤ N → MemLp (Y l N) 2 μ)
    (h_i : ∀ l, |∫ ω, Phat l ω - P ω ∂μ| ≤ c₁ * h M T l ^ α)
    (h_ii : ∀ l N, 1 ≤ N → ∫ ω, Y l N ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else ∫ ω, Phat l ω - Phat (l - 1) ω ∂μ)
    (h_iii : ∀ l N, 1 ≤ N → variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) → iIndepFun (fun l => Y l (N l)) μ)
    (L : ℕ) (hb : c₁ * h M T L ^ α ≤ ε / 2) :
    ∃ N : ℕ → ℕ, (∀ l, 1 ≤ N l) ∧ mse μ (estimator Y N L) P < ε ^ 2 ∧
      totalCost cost N L ≤ 4 * c₂ * c₃ * ε ^ (-2 : ℝ) * levelSum M T β L ^ 2 +
        c₃ * roundingSum M T L := by
  let N := sampleSize M T β c₂ ε L
  have hn : ∀ l, 1 ≤ N l := fun l => sampleSize_pos hM hT hc₂ hε L l
  refine ⟨N, hn, ?_, ?_⟩
  · apply estimator_mse_bound Y N Phat P L hε (fun l => hY l _ (hn l)) hP hPhat
      (fun l => h_ii l _ (hn l)) (h_indep N hn) ((h_i L).trans hb)
    exact (Finset.sum_le_sum (fun l _ => h_iii l _ (hn l))).trans
      (allocation_variance_bound hM hT hc₂ hε L)
  · exact (Finset.sum_le_sum (fun l _ => h_iv l _ (hn l))).trans
      (allocation_cost_bound hM hT hc₂ hε hc₃ L)

end MLMCProof


namespace GilesMLMC.Complexity

/-- **Theorem 3.1** (Giles 2008, Multilevel Monte Carlo path simulation, Operations Research
56(3), §3, p. 609, PDF 3, left column).

Formalization Note. `P` and `Phat l` (= P̂_l) are arbitrary real random variables on a
probability space; in the paper they come from an SDE and its discretisation with timestep
`h_l = M^{-l} T`, which the theorem uses only through (i)–(iv), so the statement is more
general, not weaker. `Y l n` is the level-`l` estimator Ŷ_l built from `n` samples and
`cost l n` its computational complexity C_l; since the theorem chooses the sample sizes,
(ii)–(iv), square integrability and independence are assumed for every sample size `n ≥ 1`.
Hypothesis (i) carries an absolute value: the page prints `E[P̂_l − P] ≤ c₁ h_l^α`, which
would make the theorem false (take `E[P̂_l − P] = −1`); the proof uses the two-sided bound.
`P`, `P̂_l` are integrable and every `Ŷ_l` is in L² (otherwise `∫` and `variance` take
junk value 0). `M ≥ 2` is the paper's standing "integer M ⩾ 2" (§1, p. 607); `T > 0`; `ε > 0`
is implicit in "ε < e⁻¹". The computational complexity `C` of Ŷ is `Σ_{l=0}^L C_l`. Since `β` is
fixed by the hypotheses, one `c₄` serves; the three implications are the three cases of the
paper's display. Real powers are `Real.rpow`. -/
theorem theorem_3_1_proved
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α β c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (_hβ : 0 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (P : Ω → ℝ) (Phat : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (cost : ℕ → ℕ → ℝ)
    (hP : MeasureTheory.Integrable P μ)
    (hPhat : ∀ l, MeasureTheory.Integrable (Phat l) μ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_i : ∀ l, |∫ ω, (Phat l ω - P ω) ∂μ| ≤ c₁ * h M T l ^ α)
    (h_ii : ∀ l N, 1 ≤ N → ∫ ω, Y l N ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ l, 1 ≤ N l) ∧
        mse μ (estimator Y N L) P < ε ^ 2 ∧
        (1 < β → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ)) ∧
        (β = 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (β < 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 - (1 - β) / α)) := by
  obtain ⟨A, B, hA, hB, hfinest⟩ := MLMCProof.finest_level_bounds hM hT
    (show 0 < α by linarith) hc₁
  obtain ⟨c₄, hc₄, hcost⟩ := MLMCProof.cost_rates (β := β) hM hT hα hc₂ hc₃ hA hB
  refine ⟨c₄, hc₄, ?_⟩
  intro ε hε hε1
  obtain ⟨L, hb, hinv, hlev⟩ := hfinest ε hε hε1
  obtain ⟨N, hN, hmse, hC⟩ := MLMCProof.chosen_estimators
    (show 0 < M by omega) hT hc₂ hc₃ hε P Phat Y cost hP hPhat hY
    h_i h_ii h_iii h_iv h_indep L hb
  exact ⟨L, N, hN, hmse, hcost ε hε hε1 L hinv hlev _ hC⟩

end GilesMLMC.Complexity


open MeasureTheory

namespace GilesMLMC.Complexity

/-- **Theorem 3.1** (Giles 2008, Multilevel Monte Carlo path simulation, Operations Research
56(3), §3, p. 609, PDF 3, left column).

Formalization Note. `P` and `Phat l` (= P̂_l) are arbitrary real random variables on a
probability space; in the paper they come from an SDE and its discretisation with timestep
`h_l = M^{-l} T`, which the theorem uses only through (i)–(iv), so the statement is more
general, not weaker. `Y l n` is the level-`l` estimator Ŷ_l built from `n` samples and
`cost l n` its computational complexity C_l; since the theorem chooses the sample sizes,
(ii)–(iv), square integrability and independence are assumed for every sample size `n ≥ 1`.
Hypothesis (i) carries an absolute value: the page prints `E[P̂_l − P] ≤ c₁ h_l^α`, which
would make the theorem false (take `E[P̂_l − P] = −1`); the proof uses the two-sided bound.
`P`, `P̂_l` are integrable and every `Ŷ_l` is in L² (otherwise `∫` and `variance` take
junk value 0). `M ≥ 2` is the paper's standing "integer M ⩾ 2" (§1, p. 607); `T > 0`; `ε > 0`
is implicit in "ε < e⁻¹". The computational complexity `C` of Ŷ is `Σ_{l=0}^L C_l`. Since `β` is
fixed by the hypotheses, one `c₄` serves; the three implications are the three cases of the
paper's display. Real powers are `Real.rpow`. -/
theorem theorem_3_1
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α β c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hβ : 0 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (P : Ω → ℝ) (Phat : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (cost : ℕ → ℕ → ℝ)
    (hP : MeasureTheory.Integrable P μ)
    (hPhat : ∀ l, MeasureTheory.Integrable (Phat l) μ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_i : ∀ l, |∫ ω, (Phat l ω - P ω) ∂μ| ≤ c₁ * h M T l ^ α)
    (h_ii : ∀ l N, 1 ≤ N → ∫ ω, Y l N ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ l, 1 ≤ N l) ∧
        mse μ (estimator Y N L) P < ε ^ 2 ∧
        (1 < β → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ)) ∧
        (β = 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (β < 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 - (1 - β) / α)) := by
  exact theorem_3_1_proved μ M hM T hT α β c₁ c₂ c₃ hα hβ hc₁ hc₂ hc₃ P Phat Y cost hP hPhat hY h_i h_ii h_iii h_iv h_indep

end GilesMLMC.Complexity

open GilesMLMC.Complexity

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α β c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hβ : 0 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (P : Ω → ℝ) (Phat : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (cost : ℕ → ℕ → ℝ)
    (hP : MeasureTheory.Integrable P μ)
    (hPhat : ∀ l, MeasureTheory.Integrable (Phat l) μ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_i : ∀ l, |∫ ω, (Phat l ω - P ω) ∂μ| ≤ c₁ * h M T l ^ α)
    (h_ii : ∀ l N, 1 ≤ N → ∫ ω, Y l N ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ l, 1 ≤ N l) ∧
        mse μ (estimator Y N L) P < ε ^ 2 ∧
        (1 < β → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ)) ∧
        (β = 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (β < 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 - (1 - β) / α)) := GilesMLMC.Complexity.theorem_3_1 μ M hM T hT α β c₁ c₂ c₃ hα hβ hc₁ hc₂ hc₃ P Phat Y cost hP hPhat hY h_i h_ii h_iii h_iv h_indep
