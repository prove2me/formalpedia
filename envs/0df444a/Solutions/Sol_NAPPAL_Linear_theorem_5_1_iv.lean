-- Prove2me | solution 1 for NAPPAL.Linear.theorem_5_1_iv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:54:01.878006+00:00
-- url     : https://prove2.me/submissions/b06f497f-2784-42b2-afca-cd75d20460cc

import Mathlib
import Definitions.Def_NAPPAL_KL_Setting
import Definitions.Def_NAPPAL_Rate_Setting
import Theorems.Thm_NAPPAL_Rate_lemma_4_3

open Filter Topology
open scoped InnerProductSpace

namespace NAPPAL51Aux
open NAPPAL.KL

variable {n d m : ℕ}

lemma tnorm_nonneg' (ξ : W n d m) : 0 ≤ tnorm ξ := Real.sqrt_nonneg _

lemma tnorm_sq (ξ : W n d m) : tnorm ξ ^ 2 = ‖ξ.1‖ ^ 2 + ‖ξ.2.1‖ ^ 2 + ‖ξ.2.2‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma tnorm_add_le (x y : W n d m) : tnorm (x + y) ≤ tnorm x + tnorm y := by
  have h1 : ‖x.1 + y.1‖ ≤ ‖x.1‖ + ‖y.1‖ := norm_add_le _ _
  have h2 : ‖x.2.1 + y.2.1‖ ≤ ‖x.2.1‖ + ‖y.2.1‖ := norm_add_le _ _
  have h3 : ‖x.2.2 + y.2.2‖ ≤ ‖x.2.2‖ + ‖y.2.2‖ := norm_add_le _ _
  have hx := tnorm_sq x
  have hy := tnorm_sq y
  have hx0 := tnorm_nonneg' x
  have hy0 := tnorm_nonneg' y
  have hT : 0 ≤ tnorm x + tnorm y := by linarith
  have hxy : tnorm (x + y) = Real.sqrt (‖x.1 + y.1‖ ^ 2 + ‖x.2.1 + y.2.1‖ ^ 2 +
      ‖x.2.2 + y.2.2‖ ^ 2) := rfl
  rw [hxy, ← Real.sqrt_sq hT]
  apply Real.sqrt_le_sqrt
  set a1 := ‖x.1‖
  set a2 := ‖x.2.1‖
  set a3 := ‖x.2.2‖
  set b1 := ‖y.1‖
  set b2 := ‖y.2.1‖
  set b3 := ‖y.2.2‖
  have ha1 : 0 ≤ a1 := norm_nonneg _
  have ha2 : 0 ≤ a2 := norm_nonneg _
  have ha3 : 0 ≤ a3 := norm_nonneg _
  have hb1 : 0 ≤ b1 := norm_nonneg _
  have hb2 : 0 ≤ b2 := norm_nonneg _
  have hb3 : 0 ≤ b3 := norm_nonneg _
  have e1 : ‖x.1 + y.1‖ ^ 2 ≤ (a1 + b1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 : ‖x.2.1 + y.2.1‖ ^ 2 ≤ (a2 + b2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have e3 : ‖x.2.2 + y.2.2‖ ^ 2 ≤ (a3 + b3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  -- Cauchy–Schwarz in ℝ³
  have hcs : (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 ≤ (tnorm x * tnorm y) ^ 2 := by
    rw [mul_pow, hx, hy]
    nlinarith [sq_nonneg (a1 * b2 - a2 * b1), sq_nonneg (a1 * b3 - a3 * b1),
      sq_nonneg (a2 * b3 - a3 * b2)]
  have hcs' : a1 * b1 + a2 * b2 + a3 * b3 ≤ tnorm x * tnorm y := by
    have hp : 0 ≤ tnorm x * tnorm y := mul_nonneg hx0 hy0
    nlinarith
  nlinarith

lemma wdist_nonneg (a b : W n d m) : 0 ≤ wdist a b := tnorm_nonneg' _

lemma wdist_triangle (a b c : W n d m) : wdist a c ≤ wdist a b + wdist b c := by
  unfold wdist
  have : a - c = (a - b) + (b - c) := by abel
  rw [this]
  exact tnorm_add_le _ _

lemma wdist_comm (a b : W n d m) : wdist a b = wdist b a := by
  simp only [wdist, tnorm, Prod.fst_sub, Prod.snd_sub]
  rw [norm_sub_rev a.1, norm_sub_rev a.2.1, norm_sub_rev a.2.2]

lemma norm_le_tnorm (ξ : W n d m) : ‖ξ‖ ≤ tnorm ξ := by
  have hs := tnorm_sq ξ
  have h0 := tnorm_nonneg' ξ
  rw [Prod.norm_def, Prod.norm_def]
  have k1 : ‖ξ.1‖ ≤ tnorm ξ := by
    have := norm_nonneg ξ.1
    nlinarith [sq_nonneg ‖ξ.2.1‖, sq_nonneg ‖ξ.2.2‖]
  have k2 : ‖ξ.2.1‖ ≤ tnorm ξ := by
    have := norm_nonneg ξ.2.1
    nlinarith [sq_nonneg ‖ξ.1‖, sq_nonneg ‖ξ.2.2‖]
  have k3 : ‖ξ.2.2‖ ≤ tnorm ξ := by
    have := norm_nonneg ξ.2.2
    nlinarith [sq_nonneg ‖ξ.1‖, sq_nonneg ‖ξ.2.1‖]
  exact max_le k1 (max_le k2 k3)

lemma geom_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) (j : ℕ) :
    ∑ i ∈ Finset.range j, s ^ i ≤ 1 / (1 - s) := by
  have hsum := summable_geometric_of_lt_one hs0 hs1
  have := hsum.sum_le_tsum (Finset.range j) (fun i _ => pow_nonneg hs0 i)
  rw [tsum_geometric_of_lt_one hs0 hs1] at this
  simpa [one_div] using this

/-- The abstract core of the proof of Theorem 5.1. -/
theorem core (w : ℕ → W n d m) (wbar : W n d m) (Λ Lw : ℕ → ℝ) (Λs c3 c' κ1 η ν : ℝ)
    (hc3 : 0 < c3) (hc' : 0 ≤ c') (hκ : 0 < κ1) (hη : 0 < η) (hν : 0 < ν)
    (hdec : ∀ k, 1 ≤ k → Λ (k + 1) - Λ k ≤ -c3 * wdist (w k) (w (k + 1)) ^ 2)
    (hup : ∀ k, Λ (k + 1) ≤ Lw (k + 1) + c' * wdist (w k) (w (k + 1)) ^ 2)
    (hlow : ∀ k, Lw k ≤ Λ k)
    (hlim : Tendsto Λ atTop (𝓝 Λs))
    (hcl : ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, wdist (w k) wbar < ε)
    (hvp : ∀ k, wdist (w (k + 1)) wbar < η → Lw (k + 1) < Λs + ν →
      Lw (k + 1) - Λs ≤ κ1 * wdist (w k) (w (k + 1)) ^ 2) :
    (∃ k0 : ℕ, ∀ k ≥ k0, wdist (w k) wbar < η ∧ Lw k < Λs + ν) ∧
    Summable (fun k => wdist (w k) (w (k + 1))) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ k0 : ℕ, ∀ k ≥ k0, Λ (k + 1) - Λs ≤ α * (Λ k - Λs)) ∧
    (∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, wdist (w k) wbar ≤ C * ρ ^ k) := by
  set D : ℕ → ℝ := fun k => wdist (w k) (w (k + 1)) with hD
  have hDnn : ∀ k, 0 ≤ D k := fun k => wdist_nonneg _ _
  -- monotonicity of the potential from index 1 on
  have hanti : ∀ k j, 1 ≤ k → k ≤ j → Λ j ≤ Λ k := by
    intro k j hk hkj
    induction j, hkj using Nat.le_induction with
    | base => exact le_refl _
    | succ j hkj ih =>
      have := hdec j (le_trans hk hkj)
      have := sq_nonneg (D j)
      nlinarith
  have hge : ∀ k, 1 ≤ k → Λs ≤ Λ k := by
    intro k hk
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨k, fun j hj => hanti k j hk hj⟩)
  -- the contraction factor
  set a : ℝ := (κ1 + c') / c3 with ha_def
  have ha : 0 < a := div_pos (by linarith) hc3
  have hac : a * c3 = κ1 + c' := div_mul_cancel₀ _ hc3.ne'
  set α : ℝ := a / (1 + a) with hα_def
  have hα0 : 0 < α := div_pos ha (by linarith)
  have hα1 : α < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hqstep : ∀ k, 1 ≤ k → wdist (w (k + 1)) wbar < η → Lw (k + 1) < Λs + ν →
      Λ (k + 1) - Λs ≤ α * (Λ k - Λs) := by
    intro k hk h1 h2
    have e1 := hvp k h1 h2
    have e2 := hup k
    have e3 := hdec k hk
    have e4 : Λ (k + 1) - Λs ≤ (κ1 + c') * D k ^ 2 := by
      have : c' * D k ^ 2 ≥ 0 := mul_nonneg hc' (sq_nonneg _)
      simp only [hD]
      nlinarith
    have e5 : (κ1 + c') * D k ^ 2 ≤ a * (Λ k - Λ (k + 1)) := by
      have e6 : c3 * D k ^ 2 ≤ Λ k - Λ (k + 1) := by simp only [hD]; linarith
      have := mul_le_mul_of_nonneg_left e6 ha.le
      rw [← hac]
      nlinarith
    rw [hα_def, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  -- the square root of the factor
  set s : ℝ := Real.sqrt α with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.2 hα0
  have hs1 : s < 1 := by
    rw [hs_def, Real.sqrt_lt' one_pos]; simpa using hα1
  have hss : s ^ 2 = α := Real.sq_sqrt hα0.le
  -- choice of the starting index
  set ε1 : ℝ := min ν (c3 * ((η / 2) * (1 - s)) ^ 2) with hε1
  have hε1pos : 0 < ε1 := lt_min hν (mul_pos hc3 (by
    have : 0 < (η / 2) * (1 - s) := mul_pos (by linarith) (by linarith)
    positivity))
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε1 hε1pos
  obtain ⟨k1, hk1N, hk1d⟩ := hcl (η / 2) (by linarith) (max N 1)
  have hk1 : 1 ≤ k1 := le_trans (le_max_right _ _) hk1N
  have hk1N' : N ≤ k1 := le_trans (le_max_left _ _) hk1N
  set M : ℝ := Λ k1 - Λs with hM_def
  have hM0 : 0 ≤ M := by have := hge k1 hk1; linarith
  have hMε : M < ε1 := by
    have := hN k1 hk1N'
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hMν : M < ν := lt_of_lt_of_le hMε (min_le_left _ _)
  set B : ℝ := Real.sqrt (M / c3) with hB_def
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = M / c3 := Real.sq_sqrt (div_nonneg hM0 hc3.le)
  have hBlt : B < (η / 2) * (1 - s) := by
    have hp : 0 < (η / 2) * (1 - s) := mul_pos (by linarith) (by linarith)
    rw [hB_def, Real.sqrt_lt' hp, div_lt_iff₀ hc3]
    have := lt_of_lt_of_le hMε (min_le_right _ _)
    linarith
  have hBη : B / (1 - s) < η / 2 := by
    rw [div_lt_iff₀ (by linarith)]; exact hBlt
  -- step bound
  have hstepD : ∀ j, Λ (k1 + j) - Λs ≤ α ^ j * M → D (k1 + j) ≤ s ^ j * B := by
    intro j hj
    have e3 := hdec (k1 + j) (le_trans hk1 (Nat.le_add_right _ _))
    have e4 := hge (k1 + j + 1) (by omega)
    have hD2 : D (k1 + j) ^ 2 ≤ (s ^ j * B) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul, hss, hBsq]
      rw [← mul_div_assoc, le_div_iff₀ hc3]
      simp only [hD] at *
      nlinarith
    have hp : 0 ≤ s ^ j * B := mul_nonneg (pow_nonneg hs0.le j) hB0
    exact (pow_le_pow_iff_left₀ (hDnn _) hp (by norm_num : (2 : ℕ) ≠ 0)).1 hD2
  -- main induction
  have claim : ∀ j : ℕ, Λ (k1 + j) - Λs ≤ α ^ j * M ∧
      wdist (w (k1 + j)) wbar ≤ wdist (w k1) wbar + B * ∑ i ∈ Finset.range j, s ^ i := by
    intro j
    induction j with
    | zero => simp [hM_def]
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hDj := hstepD j ih1
      have hdist : wdist (w (k1 + (j + 1))) wbar ≤
          wdist (w k1) wbar + B * ∑ i ∈ Finset.range (j + 1), s ^ i := by
        have t1 := wdist_triangle (w (k1 + (j + 1))) (w (k1 + j)) wbar
        have t2 : wdist (w (k1 + (j + 1))) (w (k1 + j)) = D (k1 + j) := by
          simp only [hD]; rw [wdist_comm]; rfl
        rw [Finset.sum_range_succ, mul_add]
        nlinarith
      refine ⟨?_, hdist⟩
      have hlt : wdist (w (k1 + j + 1)) wbar < η := by
        have g := geom_le s hs0.le hs1 (j + 1)
        have : B * ∑ i ∈ Finset.range (j + 1), s ^ i ≤ B / (1 - s) := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left g hB0
        have : wdist (w (k1 + j + 1)) wbar ≤
            wdist (w k1) wbar + B * ∑ i ∈ Finset.range (j + 1), s ^ i := hdist
        linarith
      have hval : Lw (k1 + j + 1) < Λs + ν := by
        have := hlow (k1 + j + 1)
        have := hanti k1 (k1 + j + 1) hk1 (by omega)
        linarith
      have q := hqstep (k1 + j) (by omega) hlt hval
      have : α * (Λ (k1 + j) - Λs) ≤ α * (α ^ j * M) :=
        mul_le_mul_of_nonneg_left ih1 hα0.le
      rw [pow_succ]
      show Λ (k1 + j + 1) - Λs ≤ α ^ j * α * M
      nlinarith
  have hin : ∀ k ≥ k1, wdist (w k) wbar < η ∧ Lw k < Λs + ν := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine ⟨?_, ?_⟩
    · have g := geom_le s hs0.le hs1 j
      have : B * ∑ i ∈ Finset.range j, s ^ i ≤ B / (1 - s) := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left g hB0
      have := (claim j).2
      linarith
    · have := hlow (k1 + j)
      have := hanti k1 (k1 + j) hk1 (by omega)
      linarith
  have hDk : ∀ j, D (k1 + j) ≤ B * s ^ j := by
    intro j; rw [mul_comm]; exact hstepD j (claim j).1
  refine ⟨⟨k1, hin⟩, ?_, ⟨α, hα0, hα1, k1, fun k hk =>
    hqstep k (le_trans hk1 hk) (hin (k + 1) (by omega)).1 (hin (k + 1) (by omega)).2⟩, ?_⟩
  · -- summability
    apply (summable_nat_add_iff k1).1
    refine Summable.of_nonneg_of_le (fun j => hDnn _) (fun j => ?_)
      ((summable_geometric_of_lt_one hs0.le hs1).mul_left B)
    rw [add_comm]; exact hDk j
  · -- R-linear rate
    have htel : ∀ k i, wdist (w k) wbar ≤
        wdist (w (k + i)) wbar + ∑ t ∈ Finset.range i, D (k + t) := by
      intro k i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [Finset.sum_range_succ]
        have := wdist_triangle (w (k + i)) (w (k + i + 1)) wbar
        have h' : wdist (w (k + i)) (w (k + i + 1)) = D (k + i) := rfl
        rw [h'] at this
        have : k + (i + 1) = k + i + 1 := by omega
        rw [this]
        linarith
    have htail : ∀ j, wdist (w (k1 + j)) wbar ≤ B * s ^ j / (1 - s) := by
      intro j
      apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨N', hN'k, hN'd⟩ := hcl ε hε (k1 + j)
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hN'k
      have h1 := htel (k1 + j) i
      have h2 : ∑ t ∈ Finset.range i, D (k1 + j + t) ≤ B * s ^ j / (1 - s) := by
        calc ∑ t ∈ Finset.range i, D (k1 + j + t)
            ≤ ∑ t ∈ Finset.range i, B * s ^ j * s ^ t := by
              apply Finset.sum_le_sum
              intro t _
              have := hDk (j + t)
              rw [pow_add] at this
              rw [add_assoc]; linarith
          _ = B * s ^ j * ∑ t ∈ Finset.range i, s ^ t := by rw [Finset.mul_sum]
          _ ≤ B * s ^ j * (1 / (1 - s)) :=
              mul_le_mul_of_nonneg_left (geom_le s hs0.le hs1 i)
                (mul_nonneg hB0 (pow_nonneg hs0.le j))
          _ = B * s ^ j / (1 - s) := by ring
      linarith
    refine ⟨B / (1 - s) / s ^ k1 + ∑ k ∈ Finset.range k1, wdist (w k) wbar / s ^ k, s,
      ?_, hs0, hs1, ?_⟩
    · have : 0 ≤ ∑ k ∈ Finset.range k1, wdist (w k) wbar / s ^ k :=
        Finset.sum_nonneg (fun k _ => div_nonneg (wdist_nonneg _ _) (pow_nonneg hs0.le k))
      have : 0 ≤ B / (1 - s) / s ^ k1 :=
        div_nonneg (div_nonneg hB0 (by linarith)) (pow_nonneg hs0.le k1)
      linarith
    · intro k
      have hsum0 : 0 ≤ ∑ k ∈ Finset.range k1, wdist (w k) wbar / s ^ k :=
        Finset.sum_nonneg (fun k _ => div_nonneg (wdist_nonneg _ _) (pow_nonneg hs0.le k))
      have hfirst0 : 0 ≤ B / (1 - s) / s ^ k1 :=
        div_nonneg (div_nonneg hB0 (by linarith)) (pow_nonneg hs0.le k1)
      have hsk : 0 < s ^ k := pow_pos hs0 k
      rcases lt_or_ge k k1 with hk | hk
      · have hterm : wdist (w k) wbar / s ^ k ≤
            ∑ k ∈ Finset.range k1, wdist (w k) wbar / s ^ k :=
          Finset.single_le_sum (f := fun k => wdist (w k) wbar / s ^ k)
            (fun k _ => div_nonneg (wdist_nonneg _ _) (pow_nonneg hs0.le k))
            (Finset.mem_range.2 hk)
        have : wdist (w k) wbar = wdist (w k) wbar / s ^ k * s ^ k := by
          field_simp
        rw [this]
        apply mul_le_mul_of_nonneg_right _ hsk.le
        linarith
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
        have := htail j
        have e : B * s ^ j / (1 - s) = B / (1 - s) / s ^ k1 * s ^ (k1 + j) := by
          have : s ^ k1 ≠ 0 := (pow_pos hs0 k1).ne'
          have : 1 - s ≠ 0 := by linarith
          rw [pow_add]; field_simp
        rw [e] at this
        have : B / (1 - s) / s ^ k1 * s ^ (k1 + j) ≤
            (B / (1 - s) / s ^ k1 + ∑ k ∈ Finset.range k1, wdist (w k) wbar / s ^ k) *
              s ^ (k1 + j) :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_pos hs0 _).le
        linarith


lemma runHyp_bridge {P : Problem n d m} {LG LH L0 : ℝ} {LOmj : Fin m → ℝ} {LK : ℝ}
    {K : E n → ℝ} {β γ σ : ℝ} {δ ε : ℕ → ℝ} {u : ℕ → E n} {v : ℕ → E d} {p : ℕ → E m}
    (hrun : RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p) :
    NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p := by
  obtain ⟨h1, h2, ⟨hγ, hσ, hσ1, hk⟩, h4⟩ := hrun
  refine ⟨h1, h2, ⟨hγ, hσ, hσ1, fun k => ?_⟩, h4⟩
  obtain ⟨a, b, c, e, f, g⟩ := hk k
  exact ⟨⟨a, b, c⟩, e, f, g⟩

/-- Everything in Theorem 5.1 except the stationarity of `w̄`. -/
theorem concrete {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (LK : ℝ)
    (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p)
    (wbar : W n d m) (hcl : MapClusterPt wbar Filter.atTop (wseq u v p))
    (hΛ : Filter.Tendsto (Lam P LG LH L0 γ u v p) Filter.atTop (nhds (augLag P γ wbar)))
    (κ1 η ν : ℝ) (hvp : VPEB P γ (wseq u v p) wbar κ1 η ν) :
    (∃ k0 : ℕ, ∀ k ≥ k0,
        wdist (wseq u v p k) wbar < η ∧ augLag P γ (wseq u v p k) < augLag P γ wbar + ν) ∧
    Summable (fun k => wdist (wseq u v p k) (wseq u v p (k + 1))) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
        Lam P LG LH L0 γ u v p (k + 1) - augLag P γ wbar ≤
          α * (Lam P LG LH L0 γ u v p k - augLag P γ wbar)) ∧
    (∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, wdist (wseq u v p k) wbar ≤ C * ρ ^ k) ∧
    Filter.Tendsto (wseq u v p) Filter.atTop (nhds wbar) := by
  have hrate := runHyp_bridge hrun
  obtain ⟨hc4, hdec⟩ := NAPPAL.Rate.lemma_4_3 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrate
  obtain ⟨hA1, -, ⟨hγ, -⟩, -⟩ := hrun
  obtain ⟨-, -, -, -, -, ⟨-, hlam⟩, -⟩ := hA1
  obtain ⟨hκ, hη, hν, hvp'⟩ := hvp
  have hc3 : 0 < c3 P LG LH γ :=
    lt_min (by norm_num) (lt_min hc4 (div_pos one_pos (by linarith)))
  have hc1 : 0 ≤ c1 P LG L0 γ := div_nonneg (by positivity) (mul_pos hγ hlam).le
  have hc2 : 0 ≤ c2 P LG LH γ := div_nonneg (by positivity) (mul_pos hγ hlam).le
  have hcg : 0 ≤ 1 / (2 * γ) := div_nonneg zero_le_one (by linarith)
  set c' : ℝ := c1 P LG L0 γ + c2 P LG LH γ + 1 / (2 * γ) with hc'
  have hc'0 : 0 ≤ c' := by linarith
  have hsq : ∀ k, wdist (wseq u v p k) (wseq u v p (k + 1)) ^ 2 =
      ‖u k - u (k + 1)‖ ^ 2 + ‖v k - v (k + 1)‖ ^ 2 + ‖p k - p (k + 1)‖ ^ 2 :=
    fun k => tnorm_sq _
  have hup : ∀ k, Lam P LG LH L0 γ u v p (k + 1) ≤ augLag P γ (wseq u v p (k + 1)) +
      c' * wdist (wseq u v p k) (wseq u v p (k + 1)) ^ 2 := by
    intro k
    rw [hsq k]
    simp only [Lam, Nat.add_sub_cancel]
    have x1 := sq_nonneg ‖u k - u (k + 1)‖
    have x2 := sq_nonneg ‖v k - v (k + 1)‖
    have x3 := sq_nonneg ‖p k - p (k + 1)‖
    have := mul_nonneg hc1 (add_nonneg x2 x3)
    have := mul_nonneg hc2 (add_nonneg x1 x3)
    have := mul_nonneg hcg (add_nonneg x1 x2)
    rw [hc']
    nlinarith
  have hlow : ∀ k, augLag P γ (wseq u v p k) ≤ Lam P LG LH L0 γ u v p k := by
    intro k
    simp only [Lam]
    have := mul_nonneg hc1 (sq_nonneg ‖u (k - 1) - u k‖)
    have := mul_nonneg hc2 (sq_nonneg ‖v (k - 1) - v k‖)
    have := mul_nonneg hcg (sq_nonneg ‖p (k - 1) - p k‖)
    linarith
  have hcl' : ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, wdist (wseq u v p k) wbar < ε := by
    intro ε hε N
    have hopen : IsOpen {x : W n d m | tnorm (x - wbar) < ε} := by
      apply isOpen_lt _ continuous_const
      unfold tnorm
      fun_prop
    have hmem : {x : W n d m | tnorm (x - wbar) < ε} ∈ 𝓝 wbar := by
      apply hopen.mem_nhds
      show tnorm (wbar - wbar) < ε
      simp [tnorm, hε]
    have hfr := (mapClusterPt_iff_frequently.1 hcl) _ hmem
    exact Filter.frequently_atTop.1 hfr N
  obtain ⟨hA, hB, hC, hD⟩ := core (wseq u v p) wbar (Lam P LG LH L0 γ u v p)
    (fun k => augLag P γ (wseq u v p k)) (augLag P γ wbar) (c3 P LG LH γ) c' κ1 η ν
    hc3 hc'0 hκ hη hν (fun k hk => hdec k hk) hup hlow hΛ hcl' (fun k h1 h2 => hvp' k h1 h2)
  refine ⟨hA, hB, hC, hD, ?_⟩
  obtain ⟨C, ρ, hC0, hρ0, hρ1, hbd⟩ := hD
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul C
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun k => le_trans (norm_le_tnorm _) (hbd k)) hlim

end NAPPAL51Aux

theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (LK : ℝ)
    (K : NAPPAL.KL.E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.KL.RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p)
    (wbar : NAPPAL.KL.W n d m) (hcl : MapClusterPt wbar Filter.atTop (NAPPAL.KL.wseq u v p))
    (hΛ : Filter.Tendsto (NAPPAL.KL.Lam P LG LH L0 γ u v p) Filter.atTop (nhds (NAPPAL.KL.augLag P γ wbar)))
    (κ1 η ν : ℝ) (hvp : NAPPAL.KL.VPEB P γ (NAPPAL.KL.wseq u v p) wbar κ1 η ν) :
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
        NAPPAL.KL.Lam P LG LH L0 γ u v p (k + 1) - NAPPAL.KL.augLag P γ wbar ≤
          α * (NAPPAL.KL.Lam P LG LH L0 γ u v p k - NAPPAL.KL.augLag P γ wbar)) :=
  (NAPPAL51Aux.concrete P LG LH L0 LOmj LK K β γ σ δ ε u v p hrun wbar hcl hΛ κ1 η ν hvp).2.2.1
