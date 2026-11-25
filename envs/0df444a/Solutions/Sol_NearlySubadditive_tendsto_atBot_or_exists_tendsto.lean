-- Prove2me | solution 1 for NearlySubadditive.tendsto_atBot_or_exists_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:51.83985+00:00
-- url     : https://prove2.me/submissions/e6f237a9-ae3a-4e8f-9e58-a873c077a354

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_Fekete_Window
public import Theorems.Thm_NearlySubadditive_mono
section
@[expose] public section
noncomputable section
open Filter Set
open scoped Topology
namespace NearlySubadditive
variable {f g : ℕ → ℝ} {μ ν : ℝ} {N M : ℕ} {u v : ℕ → ℝ}
end NearlySubadditive
namespace NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}
private theorem le_add (h : NearlySubadditive 0 μ N u) {m n : ℕ} (hm : N ≤ m) (hmn : m ≤ n)
    (hn : (n : ℝ) ≤ μ * m) : u (m + n) ≤ u m + u n := by
  simpa using h hm hmn hn
private theorem div_add_le_max {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : u (m + n) ≤ u m + u n) : u (m + n) / (m + n : ℕ) ≤ max (u m / m) (u n / n) := by
  have h₁ := (div_le_iff₀' (Nat.cast_pos.2 hm)).1 (le_max_left (u m / m) (u n / n))
  have h₂ := (div_le_iff₀' (Nat.cast_pos.2 hn)).1 (le_max_right (u m / m) (u n / n))
  rw [div_le_iff₀' (Nat.cast_pos.2 (by omega)), Nat.cast_add]
  linarith
private theorem div_two_mul_le (hμ : 1 ≤ μ) (h : NearlySubadditive 0 μ N u) {n : ℕ}
    (hN : N ≤ n) : u (2 * n) / (2 * n : ℕ) ≤ u n / n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simpa [two_mul] using
    div_add_le_max hn hn (h.le_add hN le_rfl (le_mul_of_one_le_left n.cast_nonneg hμ))
private theorem div_two_mul_add_one_le (h : NearlySubadditive 0 μ N u) {n : ℕ} (hN : N ≤ n)
    (hn : 0 < n) (hμn : (n + 1 : ℝ) ≤ μ * n) :
    u (2 * n + 1) / (2 * n + 1 : ℕ) ≤ max (u n / n) (u (n + 1) / (n + 1 : ℕ)) := by
  rw [show 2 * n + 1 = n + (n + 1) by ring]
  exact div_add_le_max hn n.succ_pos (h.le_add hN n.le_succ (by exact_mod_cast hμn))
private theorem le_blockMax {n j : ℕ} (h₁ : n ≤ j) (h₂ : j ≤ 2 * n) :
    u j / j ≤ blockMax u n :=
  Finset.le_sup' (fun j ↦ u j / j) (Finset.mem_Icc.2 ⟨h₁, h₂⟩)
private theorem blockMax_succ_le (hμ : 1 ≤ μ) (h : NearlySubadditive 0 μ N u) {n : ℕ}
    (hN : N ≤ n) (hn : 0 < n) (hμn : (n + 1 : ℝ) ≤ μ * n) :
    blockMax u (n + 1) ≤ blockMax u n := by
  refine Finset.sup'_le _ _ fun j hj ↦ ?_
  obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.1 hj
  rcases le_or_gt j (2 * n) with hj | hj
  · exact le_blockMax (by omega) hj
  · rcases (show j = 2 * n + 1 ∨ j = 2 * (n + 1) by omega) with rfl | rfl
    · exact (div_two_mul_add_one_le h hN hn hμn).trans
        (max_le (le_blockMax le_rfl (by omega)) (le_blockMax (by omega) (by omega)))
    · exact (div_two_mul_le hμ h (hN.trans n.le_succ)).trans (le_blockMax (by omega) (by omega))
private theorem pow_mul_le_windowEnd (hμ : 1 ≤ μ) (n : ℕ) :
    ∀ i, 2 ^ i * n ≤ windowEnd μ n i
  | 0 => by simp [windowEnd]
  | i + 1 => by
    have ih := pow_mul_le_windowEnd hμ n i
    have : windowEnd μ n i ≤ ⌊μ * windowEnd μ n i⌋₊ :=
      Nat.le_floor (le_mul_of_one_le_left (Nat.cast_nonneg _) hμ)
    have h2 : 2 ^ (i + 1) * n = 2 * (2 ^ i * n) := by ring
    simp only [windowEnd]
    omega
private theorem windowEnd_lower (hμ : 0 < μ) (n : ℕ) :
    ∀ i, (1 + μ) ^ i * (n - 1 / μ) ≤ windowEnd μ n i - 1 / μ
  | 0 => by simp [windowEnd]
  | i + 1 => by
    have ih := mul_le_mul_of_nonneg_left (windowEnd_lower hμ n i) (by linarith : 0 ≤ 1 + μ)
    have hfl := Nat.lt_floor_add_one (μ * windowEnd μ n i)
    have h1 : (1 + μ) * (1 / μ) = 1 / μ + 1 := by field_simp
    simp only [windowEnd, Nat.cast_add, pow_succ]
    linarith
private theorem exists_add_eq (hμ : 1 < μ) {n : ℕ} (hn : (1 + μ) ≤ (μ - 1) * n) {i z : ℕ}
    (h₁ : 2 ^ (i + 1) * n ≤ z) (h₂ : z ≤ windowEnd μ n (i + 1)) :
    ∃ w y, w + y = z ∧ 2 ^ i * n ≤ w ∧ w ≤ windowEnd μ n i ∧ w ≤ y ∧ (y : ℝ) ≤ μ * w := by
  have hμ0 : (0 : ℝ) < 1 + μ := by linarith
  have hc := pow_mul_le_windowEnd hμ.le n i
  set c := windowEnd μ n i
  have h₂' : (z : ℝ) ≤ c + μ * c := by
    have : (z : ℝ) ≤ c + ⌊μ * c⌋₊ := by exact_mod_cast h₂
    linarith [Nat.floor_le (show 0 ≤ μ * c by positivity)]
  have hz2n : (2 * n : ℝ) ≤ z := by
    have h2i : 2 * n ≤ 2 ^ (i + 1) * n := by
      rw [pow_succ']
      exact Nat.mul_le_mul_right n (Nat.le_mul_of_pos_right 2 (by positivity))
    exact_mod_cast h2i.trans h₁
  set w := max (2 ^ i * n) ⌈(z : ℝ) / (1 + μ)⌉₊ with hw
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (z : ℝ) / (1 + μ) by positivity)
  have hzw : (z : ℝ) ≤ (1 + μ) * w :=
    (div_le_iff₀' hμ0).1 ((Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _))
  have hA : 2 * (2 ^ i * n) ≤ z := by rw [← mul_assoc, ← pow_succ']; exact h₁
  have hB : 2 * ⌈(z : ℝ) / (1 + μ)⌉₊ ≤ z := by
    have hz := mul_le_mul_of_nonneg_right hz2n (by linarith : (0 : ℝ) ≤ μ - 1)
    have : 2 * ((z : ℝ) / (1 + μ) + 1) ≤ z := by
      rw [div_add_one hμ0.ne', mul_div_assoc', div_le_iff₀ hμ0]
      linarith
    exact_mod_cast (show (2 : ℝ) * ⌈(z : ℝ) / (1 + μ)⌉₊ ≤ z by linarith)
  have h2w : 2 * w ≤ z := by
    rw [hw, mul_max_of_nonneg _ _ (Nat.zero_le 2)]
    exact max_le hA hB
  refine ⟨w, z - w, by omega, le_max_left _ _, max_le hc (Nat.ceil_le.2 ?_), by omega, ?_⟩
  · rw [div_le_iff₀ hμ0]
    linarith
  · rw [Nat.cast_sub (by omega)]
    linarith
private theorem propagate (hμ : 1 < μ) (h : NearlySubadditive 0 μ N u) {n : ℕ} {l ε η : ℝ}
    (hN : N ≤ n) (hn : (1 + μ) ≤ (μ - 1) * n) (hup : ∀ y, n ≤ y → u y / y ≤ l + ε)
    (hxn : u n / n = l + ε - η) (hη : 0 ≤ η) :
    ∀ i z, 2 ^ i * n ≤ z → z ≤ windowEnd μ n i → u z / z ≤ l + ε - η / (1 + μ) ^ i := by
  have hμ0 : (0 : ℝ) < 1 + μ := by linarith
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hn; linarith
  intro i
  induction i with
  | zero =>
    intro z h₁ h₂
    simp only [pow_zero, one_mul, windowEnd] at h₁ h₂
    rw [show z = n by omega, hxn, pow_zero, div_one]
  | succ i ih =>
    intro z h₁ h₂
    obtain ⟨w, y, rfl, hw₁, hw₂, hwy, hyμ⟩ := exists_add_eq hμ hn h₁ h₂
    have hwn : n ≤ w := (Nat.le_mul_of_pos_left n (by positivity)).trans hw₁
    have hwpos : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
    have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have key := h.le_add (hN.trans hwn) hwy hyμ
    have huw := (div_le_iff₀' hwpos).1 (ih w hw₁ hw₂)
    have huy := (div_le_iff₀' hypos).1 (hup y (hwn.trans hwy))
    rw [pow_succ, ← div_div, Nat.cast_add, div_le_iff₀ (add_pos hwpos hypos)]
    set η' := η / (1 + μ) ^ i
    have hη' : 0 ≤ η' := by positivity
    have : η' / (1 + μ) * (w + y) ≤ η' * w := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hμ0]
      linarith [mul_le_mul_of_nonneg_left hyμ hη']
    linarith
end NearlySubadditive
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (hμ : 1 < μ) (h : NearlySubadditive 0 μ N u) :
    Tendsto (fun n ↦ u n / n) atTop atBot ∨ ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) := by
  have hμ0 : (0 : ℝ) < 1 + μ := by linarith
  -- a threshold beyond which all the elementary steps apply
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n, M ≤ n → N ≤ n ∧ 2 ≤ n ∧ (1 + μ) ≤ (μ - 1) * n := by
    obtain ⟨M₁, hM₁⟩ := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      ((1 + μ) / (μ - 1)) |>.exists_forall_of_atTop
    refine ⟨max (max N 2) M₁, fun n hn ↦ ⟨by omega, by omega, ?_⟩⟩
    have := hM₁ n (by omega)
    rwa [div_le_iff₀ (by linarith), mul_comm] at this
  have hstep : ∀ n, M ≤ n → (n + 1 : ℝ) ≤ μ * n := fun n hn ↦ by
    linarith [(hM n hn).2.2]
  set Q : ℕ → ℝ := fun k ↦ blockMax u (k + M)
  have hQ : Antitone Q := antitone_nat_of_succ_le fun k ↦ by
    have hk := hM (k + M) (by omega)
    simpa [Q, add_right_comm] using
      blockMax_succ_le hμ.le h hk.1 (by omega) (hstep (k + M) (by omega))
  have hxQ : ∀ k, u (k + M) / (k + M : ℕ) ≤ Q k := fun k ↦ le_blockMax le_rfl (by omega)
  rcases tendsto_atTop_of_antitone hQ with hbot | ⟨l, hl⟩
  · exact Or.inl <| (tendsto_add_atTop_iff_nat M).1 (tendsto_atBot_mono hxQ hbot)
  refine Or.inr ⟨l, ?_⟩
  have hlQ : ∀ n, M ≤ n → l ≤ blockMax u n := fun n hn ↦ by
    simpa [Q, Nat.sub_add_cancel hn] using hQ.le_of_tendsto hl (n - M)
  -- upper bound
  have hupper : ∀ ε > 0, ∀ᶠ n in atTop, u n / n < l + ε := fun ε hε ↦ by
    filter_upwards [(tendsto_sub_atTop_nat M).eventually
      (hl.eventually (gt_mem_nhds (lt_add_of_pos_right l hε))), eventually_ge_atTop M]
      with n hn hnM
    simpa [Nat.sub_add_cancel hnM] using (hxQ (n - M)).trans_lt hn
  -- a fixed number of propagation steps
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 4 * 2 ^ K ≤ (1 + μ) ^ K := by
    have : Tendsto (fun K : ℕ ↦ ((1 + μ) / 2) ^ K) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by linarith)
    obtain ⟨K, hK⟩ := (this.eventually_ge_atTop 4).exists
    exact ⟨K, by rwa [div_pow, le_div_iff₀ (by positivity)] at hK⟩
  -- lower bound
  have hlower : ∀ ε > 0, ∀ᶠ n in atTop, l - ε * (1 + μ) ^ K ≤ u n / n := fun ε hε ↦ by
    obtain ⟨N₃, hN₃⟩ := ((hupper ε hε).mono fun _ h ↦ h.le).exists_forall_of_atTop
    filter_upwards [eventually_ge_atTop (max M N₃)] with n hn
    obtain ⟨hNn, h2n, hμn⟩ := hM n (by omega)
    have hup : ∀ y, n ≤ y → u y / y ≤ l + ε := fun y hy ↦ hN₃ y (by omega)
    by_cases hx : l + ε ≤ u n / n
    · have := mul_pos hε (pow_pos hμ0 K)
      linarith
    set η := l + ε - u n / n with hη_def
    have hη : 0 ≤ η := by linarith
    have hprop := propagate hμ h hNn hμn hup (by ring) hη K
    -- the interval `[2^K n, c_K]` contains the block `[2^K n, 2 * 2^K n]`
    have hcK : 2 * (2 ^ K * n) ≤ windowEnd μ n K := by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2n
      have hinv : 0 < 1 / μ ∧ 1 / μ ≤ 1 := ⟨by positivity, (div_le_one (by linarith)).2 hμ.le⟩
      have e1 := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ n / 2)
      have e2 := mul_le_mul_of_nonneg_left (by linarith : (n : ℝ) / 2 ≤ n - 1 / μ)
        (pow_pos hμ0 K).le
      have := windowEnd_lower (by linarith : (0 : ℝ) < μ) n K
      exact_mod_cast (show (2 * (2 ^ K * n) : ℝ) ≤ windowEnd μ n K by linarith)
    have hblock : blockMax u (2 ^ K * n) ≤ l + ε - η / (1 + μ) ^ K :=
      Finset.sup'_le _ _ fun j hj ↦ by
        obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.1 hj
        exact hprop j hj₁ (hj₂.trans hcK)
    have hl' := hlQ (2 ^ K * n) (le_trans (by omega) (Nat.le_mul_of_pos_left n (by positivity)))
    have : η ≤ ε * (1 + μ) ^ K :=
      (div_le_iff₀ (pow_pos hμ0 K)).1 (by linarith [hl'.trans hblock])
    linarith
  -- conclude
  have hpos := pow_pos hμ0 K
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · have hε : 0 < (l - a) / 2 / (1 + μ) ^ K := div_pos (half_pos (by linarith)) hpos
    filter_upwards [hlower _ hε] with n hn
    rw [div_mul_cancel₀ _ hpos.ne'] at hn
    linarith
  · filter_upwards [hupper (b - l) (by linarith)] with n hn
    linarith
end NearlySubadditive
