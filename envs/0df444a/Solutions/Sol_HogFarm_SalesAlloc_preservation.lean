-- Prove2me | solution 1 for HogFarm.SalesAlloc.preservation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T16:47:45.06078+00:00
-- url     : https://prove2.me/submissions/85e8d3bd-3ba6-47c6-b467-0c4d3cc211dc

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace HogPres

open HogFarm.SalesAlloc

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Expected next-period value at level `n` and total holding `Z`. -/
noncomputable def Cn (M : Model Ω) (n t : ℕ) (ω : Ω) (Z : ℝ) : ℝ :=
  ∫ ω', valueAux M n (t + 1) (M.W1 (t + 1) ω') (M.W2 (t + 1) ω' + Z) ω' ∂(M.κ t ω)

/-- The Bellman objective at level `n + 1`. -/
noncomputable def objN (M : Model Ω) (n t : ℕ) (ω : Ω) (s1 s2 y1 y2 z1 z2 : ℝ) : ℝ :=
  reward (M.price t ω) M.q M.α s1 s2 y1 y2 z1 z2 + M.β * Cn M n t ω (z1 + z2)

/-- The Bellman candidate set at level `n + 1`. -/
def SN (M : Model Ω) (n t : ℕ) (s1 s2 : ℝ) (ω : Ω) : Set ℝ :=
  {v | ∃ y1 y2 z1 z2 : ℝ, Feasible M.q s1 s2 y1 y2 z1 z2 ∧
    v = objN M n t ω s1 s2 y1 y2 z1 z2}

lemma valueAux_succ (M : Model Ω) (n t : ℕ) (s1 s2 : ℝ) (ω : Ω) :
    valueAux M (n + 1) t s1 s2 ω = sSup (SN M n t s1 s2 ω) := by
  simp only [valueAux, SN, objN, Cn, add_assoc]

/-- Growth bound, joint concavity on the quadrant, and measurability along
measurable nonnegative states. -/
def Good (M : Model Ω) (n : ℕ) : Prop :=
  (∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℕ) (s1 s2 : ℝ) (ω : Ω), 0 ≤ s1 → 0 ≤ s2 →
      |valueAux M n t s1 s2 ω| ≤ K * (1 + s1 + s2)) ∧
  (∀ (t : ℕ) (ω : Ω), ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun s : ℝ × ℝ => valueAux M n t s.1 s.2 ω)) ∧
  (∀ (t : ℕ) (a b : Ω → ℝ), Measurable a → Measurable b → (∀ ω, 0 ≤ a ω) →
      (∀ ω, 0 ≤ b ω) → Measurable (fun ω => valueAux M n t (a ω) (b ω) ω))

lemma good_zero (M : Model Ω) : Good M 0 := by
  refine ⟨⟨0, le_rfl, fun t s1 s2 ω _ _ => ?_⟩, fun t ω => ?_, fun t a b _ _ _ _ => ?_⟩
  · simp [valueAux]
  · simp only [valueAux]
    exact concaveOn_const _ ((convex_Ici 0).prod (convex_Ici 0))
  · simp only [valueAux]
    exact measurable_const

/-- Unpacked standing bounds. -/
lemma std_bounds {M : Model Ω} (hS : M.Standing) :
    0 < M.q ∧ 0 < M.α ∧ M.α < 1 ∧ 0 < M.β ∧ M.β ≤ 1 ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℕ) (ω : Ω),
      0 ≤ (M.price t ω).p1 ∧ (M.price t ω).p1 ≤ (M.price t ω).p2 ∧
      0 ≤ (M.price t ω).pC ∧ 0 ≤ (M.price t ω).cH ∧ 0 ≤ (M.price t ω).cP ∧
      0 ≤ M.W1 t ω ∧ 0 ≤ M.W2 t ω ∧
      (M.price t ω).p1 ≤ B ∧ (M.price t ω).p2 ≤ B ∧ (M.price t ω).pC ≤ B ∧
      (M.price t ω).cH ≤ B ∧ (M.price t ω).cP ≤ B ∧ M.W1 t ω ≤ B ∧ M.W2 t ω ≤ B := by
  obtain ⟨_, hq, hα0, hα1, hβ0, hβ1, ⟨B, hB0, hB⟩, _⟩ := hS
  exact ⟨hq, hα0, hα1, hβ0, hβ1, B, hB0, fun t ω => hB t ω⟩

lemma reward_abs_le (P : Prices) (q α s1 s2 y1 y2 z1 z2 B : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hB0 : 0 ≤ B)
    (hp1 : 0 ≤ P.p1) (hp12 : P.p1 ≤ P.p2) (hpC : 0 ≤ P.pC) (hcH : 0 ≤ P.cH) (hcP : 0 ≤ P.cP)
    (hp1B : P.p1 ≤ B) (hp2B : P.p2 ≤ B) (hpCB : P.pC ≤ B) (hcHB : P.cH ≤ B) (hcPB : P.cP ≤ B)
    (hF : Feasible q s1 s2 y1 y2 z1 z2) :
    |reward P q α s1 s2 y1 y2 z1 z2| ≤ B * (q + s1 + s2) := by
  obtain ⟨hy1, hy2, hz1, hz2, hyq, h1, h2⟩ := hF
  have e1 : y2 + (1 - α) * y1 ≤ q := by nlinarith
  have e1' : 0 ≤ y2 + (1 - α) * y1 := by nlinarith
  have k1 := mul_le_mul hpCB e1 e1' hB0
  have k1' := mul_nonneg hpC e1'
  have k2 := mul_le_mul_of_nonneg_right hp1B (show 0 ≤ s1 - y1 - z1 by linarith)
  have k2' := mul_nonneg hp1 (show 0 ≤ s1 - y1 - z1 by linarith)
  have k3 := mul_le_mul_of_nonneg_right hp2B (show 0 ≤ s2 - y2 - z2 by linarith)
  have k3' := mul_nonneg (hp1.trans hp12) (show 0 ≤ s2 - y2 - z2 by linarith)
  have k4 := mul_le_mul_of_nonneg_right hcHB (show 0 ≤ z1 + z2 by linarith)
  have k4' := mul_nonneg hcH (show 0 ≤ z1 + z2 by linarith)
  have k5 := mul_le_mul_of_nonneg_right hcPB (show 0 ≤ q - y1 - y2 by linarith)
  have k5' := mul_nonneg hcP (show 0 ≤ q - y1 - y2 by linarith)
  have m1 := mul_nonneg hB0 hy1
  have m2 := mul_nonneg hB0 hy2
  have m3 := mul_nonneg hB0 hz1
  have m4 := mul_nonneg hB0 hz2
  have m5 := mul_nonneg hB0 (show 0 ≤ s1 - y1 - z1 by linarith)
  have m6 := mul_nonneg hB0 (show 0 ≤ s2 - y2 - z2 by linarith)
  rw [abs_le]
  constructor <;> simp only [reward] <;> nlinarith

/-- Integrability, bound and concavity of the continuation at a good level. -/
lemma Cn_facts {M : Model Ω} (hS : M.Standing) {n : ℕ} (hG : Good M n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ (t : ℕ) (ω : Ω) (Z : ℝ), 0 ≤ Z → |Cn M n t ω Z| ≤ K * (1 + 2 * B + Z)) ∧
      (∀ (t : ℕ) (ω : Ω), ConcaveOn ℝ (Set.Ici 0) (Cn M n t ω)) ∧
      (∀ (t : ℕ) (Z : ℝ), 0 ≤ Z → Measurable (fun ω => Cn M n t ω Z)) := by
  obtain ⟨_, hq, hα0, hα1, hβ0, hβ1, ⟨B, hB0, hB⟩, hmeas⟩ := hS
  obtain ⟨⟨K, hK0, hK⟩, hconc, hm⟩ := hG
  have hW : ∀ t ω, 0 ≤ M.W1 t ω ∧ 0 ≤ M.W2 t ω ∧ M.W1 t ω ≤ B ∧ M.W2 t ω ≤ B := by
    intro t ω
    have h := hB t ω
    dsimp only at h
    exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  -- measurability of the integrand
  have hfm : ∀ t (Z : ℝ), 0 ≤ Z → Measurable (fun ω' =>
      valueAux M n (t + 1) (M.W1 (t + 1) ω') (M.W2 (t + 1) ω' + Z) ω') := by
    intro t Z hZ
    obtain ⟨_, _, _, _, _, hW1m, hW2m, _⟩ := hmeas (t + 1)
    exact hm (t + 1) _ _ hW1m (hW2m.add_const Z) (fun ω => (hW (t + 1) ω).1)
      (fun ω => add_nonneg (hW (t + 1) ω).2.1 hZ)
  have hfb : ∀ t (Z : ℝ), 0 ≤ Z → ∀ ω', ‖valueAux M n (t + 1) (M.W1 (t + 1) ω')
      (M.W2 (t + 1) ω' + Z) ω'‖ ≤ K * (1 + 2 * B + Z) := by
    intro t Z hZ ω'
    obtain ⟨h1, h2, h3, h4⟩ := hW (t + 1) ω'
    rw [Real.norm_eq_abs]
    refine (hK _ _ _ _ h1 (add_nonneg h2 hZ)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK0
    linarith
  have hint : ∀ t ω (Z : ℝ), 0 ≤ Z → Integrable (fun ω' => valueAux M n (t + 1)
      (M.W1 (t + 1) ω') (M.W2 (t + 1) ω' + Z) ω') (M.κ t ω) := by
    intro t ω Z hZ
    have : IsMarkovKernel (M.κ t) := (hmeas t).2.2.2.2.2.2.2
    exact Integrable.of_bound (hfm t Z hZ).aestronglyMeasurable _
      (Filter.Eventually.of_forall (hfb t Z hZ))
  refine ⟨K, hK0, B, hB0, ?_, ?_, ?_⟩
  · intro t ω Z hZ
    have : IsMarkovKernel (M.κ t) := (hmeas t).2.2.2.2.2.2.2
    have h := norm_integral_le_of_norm_le_const (μ := M.κ t ω)
      (Filter.Eventually.of_forall (hfb t Z hZ))
    rw [Real.norm_eq_abs] at h
    simpa [Cn] using h
  · intro t ω
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hx' : (0 : ℝ) ≤ x := hx
    have hy' : (0 : ℝ) ≤ y := hy
    have hxy : 0 ≤ a • x + b • y := by
      simp only [smul_eq_mul]; positivity
    simp only [Cn, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint t ω x hx').const_mul a) ((hint t ω y hy').const_mul b)]
    refine integral_mono (((hint t ω x hx').const_mul a).add ((hint t ω y hy').const_mul b))
      (by simpa [smul_eq_mul] using hint t ω _ hxy) (fun ω' => ?_)
    obtain ⟨h1, h2, _, _⟩ := hW (t + 1) ω'
    have hc := (hconc (t + 1) ω').2
      (show (M.W1 (t + 1) ω', M.W2 (t + 1) ω' + x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) from
        ⟨h1, add_nonneg h2 hx'⟩)
      (show (M.W1 (t + 1) ω', M.W2 (t + 1) ω' + y) ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) from
        ⟨h1, add_nonneg h2 hy'⟩) ha hb hab
    have key : (a • (M.W1 (t + 1) ω', M.W2 (t + 1) ω' + x) +
        b • (M.W1 (t + 1) ω', M.W2 (t + 1) ω' + y) : ℝ × ℝ) =
        (M.W1 (t + 1) ω', M.W2 (t + 1) ω' + (a * x + b * y)) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination M.W1 (t + 1) ω' * hab
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination M.W2 (t + 1) ω' * hab
    rw [key] at hc
    simpa [smul_eq_mul] using hc
  · intro t Z hZ
    have : IsMarkovKernel (M.κ t) := (hmeas t).2.2.2.2.2.2.2
    have hsm := ((hfm t Z hZ).comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
      (κ := M.κ t)
    exact hsm.measurable

lemma feas0 {q s1 s2 : ℝ} (hq : 0 ≤ q) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) :
    Feasible q s1 s2 0 0 0 0 :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, by linarith, by linarith, by linarith⟩

lemma sSup_comb {X Y : Set ℝ} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (h : ∀ x ∈ X, ∀ y ∈ Y, a * x + b * y ≤ c) : a * sSup X + b * sSup Y ≤ c := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, hx, hx'⟩ := exists_lt_of_lt_csSup hX (show sSup X - ε < sSup X by linarith)
  obtain ⟨y, hy, hy'⟩ := exists_lt_of_lt_csSup hY (show sSup Y - ε < sSup Y by linarith)
  have := h x hx y hy
  nlinarith [mul_le_mul_of_nonneg_left hx'.le ha, mul_le_mul_of_nonneg_left hy'.le hb]

lemma objN_bound {M : Model Ω} (hS : M.Standing) {n : ℕ} (hG : Good M n) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (t : ℕ) (ω : Ω) (s1 s2 y1 y2 z1 z2 : ℝ), 0 ≤ s1 → 0 ≤ s2 →
      Feasible M.q s1 s2 y1 y2 z1 z2 →
      |objN M n t ω s1 s2 y1 y2 z1 z2| ≤ K' * (1 + s1 + s2) := by
  obtain ⟨K, hK0, B, hB0', hCb, -, -⟩ := Cn_facts hS hG
  obtain ⟨hq, hα0, hα1, hβ0, hβ1, B', hB0, hB⟩ := std_bounds hS
  refine ⟨B' * M.q + B' + K * (1 + 2 * B) + K, by positivity, ?_⟩
  intro t ω s1 s2 y1 y2 z1 z2 hs1 hs2 hF
  obtain ⟨hp1, hp12, hpC, hcH, hcP, -, -, hp1B, hp2B, hpCB, hcHB, hcPB, -, -⟩ := hB t ω
  have hr := reward_abs_le (M.price t ω) M.q M.α s1 s2 y1 y2 z1 z2 B' hα0.le hα1.le hB0
    hp1 hp12 hpC hcH hcP hp1B hp2B hpCB hcHB hcPB hF
  obtain ⟨hy1, hy2, hz1, hz2, -, h1, h2⟩ := hF
  have hZ : 0 ≤ z1 + z2 := add_nonneg hz1 hz2
  have hc := hCb t ω (z1 + z2) hZ
  have hβc : |M.β * Cn M n t ω (z1 + z2)| ≤ K * (1 + 2 * B + (z1 + z2)) := by
    rw [abs_mul, abs_of_pos hβ0]
    calc M.β * |Cn M n t ω (z1 + z2)| ≤ 1 * |Cn M n t ω (z1 + z2)| :=
          mul_le_mul_of_nonneg_right hβ1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hc
  have hsum : |objN M n t ω s1 s2 y1 y2 z1 z2| ≤
      B' * (M.q + s1 + s2) + K * (1 + 2 * B + (z1 + z2)) := by
    unfold objN
    exact (abs_add_le _ _).trans (add_le_add hr hβc)
  refine hsum.trans ?_
  have hs : 0 ≤ s1 + s2 := add_nonneg hs1 hs2
  nlinarith [mul_nonneg hB0 hq.le, mul_nonneg (mul_nonneg hB0 hq.le) hs, mul_nonneg hK0 hs,
    mul_nonneg (mul_nonneg hK0 (by positivity : (0:ℝ) ≤ 1 + 2 * B)) hs,
    mul_le_mul_of_nonneg_left (show z1 + z2 ≤ s1 + s2 by linarith) hK0, mul_nonneg hB0 hs]

lemma SN_bdd {M : Model Ω} {n : ℕ} {K' : ℝ}
    (hK' : ∀ (t : ℕ) (ω : Ω) (s1 s2 y1 y2 z1 z2 : ℝ), 0 ≤ s1 → 0 ≤ s2 →
      Feasible M.q s1 s2 y1 y2 z1 z2 →
      |objN M n t ω s1 s2 y1 y2 z1 z2| ≤ K' * (1 + s1 + s2))
    (t : ℕ) (ω : Ω) {s1 s2 : ℝ} (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) :
    BddAbove (SN M n t s1 s2 ω) :=
  ⟨K' * (1 + s1 + s2), by
    rintro v ⟨y1, y2, z1, z2, hF, rfl⟩
    exact (le_abs_self _).trans (hK' t ω s1 s2 y1 y2 z1 z2 hs1 hs2 hF)⟩

lemma rat_near (x θ : ℝ) (hx : 0 ≤ x) (hθ : θ < 1) : ∃ r : ℚ, θ * x ≤ r ∧ (r : ℝ) ≤ x := by
  rcases hx.eq_or_lt with h | h
  · exact ⟨0, by simp [← h], by simp [← h]⟩
  · obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show θ * x < x by nlinarith)
    exact ⟨r, h1.le, h2.le⟩

lemma lin_bd (c d e : ℝ) (h : |d| ≤ e) : -(|c| * e) ≤ c * d := by
  have h1 : |c * d| ≤ |c| * e := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg c)
  linarith [neg_abs_le (c * d)]

set_option maxHeartbeats 1000000 in
lemma approx (P : Prices) (q α β s1 s2 y1 y2 z1 z2 ε : ℝ) (Cf : ℝ → ℝ)
    (hβ : 0 ≤ β) (hC : ConcaveOn ℝ (Set.Ici 0) Cf)
    (hF : Feasible q s1 s2 y1 y2 z1 z2) (hε : 0 < ε) :
    ∃ r1 r2 r3 r4 : ℚ, Feasible q s1 s2 r1 r2 r3 r4 ∧
      reward P q α s1 s2 y1 y2 z1 z2 + β * Cf (z1 + z2) - ε ≤
        reward P q α s1 s2 r1 r2 r3 r4 + β * Cf ((r3 : ℝ) + r4) := by
  obtain ⟨hy1, hy2, hz1, hz2, hyq, h1, h2⟩ := hF
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = |P.pC * (1 - α) - P.p1 + P.cP| + |P.pC - P.p2 + P.cP| +
      |P.p1 + P.cH| + |P.p2 + P.cH| := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = y1 + y2 + z1 + z2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = |Cf 0 - Cf (z1 + z2)| := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hD0 : 0 ≤ D := by rw [hD]; exact abs_nonneg _
  have hden : 0 < L * X + β * D + 1 := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (1 / 2) (ε / (L * X + β * D + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1 / 2 := by rw [hδ]; exact min_le_left _ _
  have hδε : δ * (L * X + β * D) < ε := by
    have h3 : δ ≤ ε / (L * X + β * D + 1) := by rw [hδ]; exact min_le_right _ _
    rw [le_div_iff₀ hden] at h3
    nlinarith
  obtain ⟨r1, a1, b1⟩ := rat_near y1 (1 - δ) hy1 (by linarith)
  obtain ⟨r2, a2, b2⟩ := rat_near y2 (1 - δ) hy2 (by linarith)
  obtain ⟨r3, a3, b3⟩ := rat_near z1 (1 - δ) hz1 (by linarith)
  obtain ⟨r4, a4, b4⟩ := rat_near z2 (1 - δ) hz2 (by linarith)
  have hθ0 : 0 ≤ 1 - δ := by linarith
  have c1 : (0:ℝ) ≤ r1 := (mul_nonneg hθ0 hy1).trans a1
  have c2 : (0:ℝ) ≤ r2 := (mul_nonneg hθ0 hy2).trans a2
  have c3 : (0:ℝ) ≤ r3 := (mul_nonneg hθ0 hz1).trans a3
  have c4 : (0:ℝ) ≤ r4 := (mul_nonneg hθ0 hz2).trans a4
  refine ⟨r1, r2, r3, r4, ⟨c1, c2, c3, c4, by linarith, by linarith, by linarith⟩, ?_⟩
  have hrw : reward P q α s1 s2 r1 r2 r3 r4 - reward P q α s1 s2 y1 y2 z1 z2 =
      (P.pC * (1 - α) - P.p1 + P.cP) * ((r1:ℝ) - y1) + (P.pC - P.p2 + P.cP) * ((r2:ℝ) - y2) +
      (P.p1 + P.cH) * (z1 - r3) + (P.p2 + P.cH) * (z2 - r4) := by
    simp only [reward]; ring
  have hδX := mul_nonneg hδ0.le hX0
  have x1 : δ * y1 ≤ δ * X := mul_le_mul_of_nonneg_left (by rw [hX]; linarith) hδ0.le
  have x2 : δ * y2 ≤ δ * X := mul_le_mul_of_nonneg_left (by rw [hX]; linarith) hδ0.le
  have x3 : δ * z1 ≤ δ * X := mul_le_mul_of_nonneg_left (by rw [hX]; linarith) hδ0.le
  have x4 : δ * z2 ≤ δ * X := mul_le_mul_of_nonneg_left (by rw [hX]; linarith) hδ0.le
  have e1 : |(r1:ℝ) - y1| ≤ δ * X := abs_le.mpr ⟨by linarith, by linarith⟩
  have e2 : |(r2:ℝ) - y2| ≤ δ * X := abs_le.mpr ⟨by linarith, by linarith⟩
  have e3 : |z1 - (r3:ℝ)| ≤ δ * X := abs_le.mpr ⟨by linarith, by linarith⟩
  have e4 : |z2 - (r4:ℝ)| ≤ δ * X := abs_le.mpr ⟨by linarith, by linarith⟩
  have l1 := lin_bd (P.pC * (1 - α) - P.p1 + P.cP) _ _ e1
  have l2 := lin_bd (P.pC - P.p2 + P.cP) _ _ e2
  have l3 := lin_bd (P.p1 + P.cH) _ _ e3
  have l4 := lin_bd (P.p2 + P.cH) _ _ e4
  have hLX : L * (δ * X) = |P.pC * (1 - α) - P.p1 + P.cP| * (δ * X) +
      |P.pC - P.p2 + P.cP| * (δ * X) + |P.p1 + P.cH| * (δ * X) + |P.p2 + P.cH| * (δ * X) := by
    rw [hL]; ring
  have hcw : Cf (z1 + z2) - δ * D ≤ Cf ((r3:ℝ) + r4) := by
    rcases (add_nonneg hz1 hz2).eq_or_lt with hZ | hZ
    · have hz1' : z1 = 0 := by linarith
      have hz2' : z2 = 0 := by linarith
      have h3 : (r3:ℝ) = 0 := by linarith
      have h4 : (r4:ℝ) = 0 := by linarith
      rw [h3, h4, hz1', hz2']
      linarith [mul_nonneg hδ0.le hD0]
    · have hw0 : (0:ℝ) ≤ r3 + r4 := add_nonneg c3 c4
      have hwZ : (r3:ℝ) + r4 ≤ z1 + z2 := by linarith
      have hwl : (1 - δ) * (z1 + z2) ≤ r3 + r4 := by linarith
      have hl0 : 0 ≤ ((r3:ℝ) + r4) / (z1 + z2) := div_nonneg hw0 hZ.le
      have hl1 : ((r3:ℝ) + r4) / (z1 + z2) ≤ 1 := (div_le_one hZ).mpr hwZ
      have hlδ : 1 - δ ≤ ((r3:ℝ) + r4) / (z1 + z2) := (le_div_iff₀ hZ).mpr hwl
      have hcc := hC.2 (show z1 + z2 ∈ Set.Ici (0:ℝ) from hZ.le)
        (show (0:ℝ) ∈ Set.Ici (0:ℝ) from Set.mem_Ici.mpr le_rfl) hl0 (sub_nonneg.mpr hl1) (by ring)
      simp only [smul_eq_mul, mul_zero, add_zero, div_mul_cancel₀ _ hZ.ne'] at hcc
      have hD' : Cf (z1 + z2) - Cf 0 ≤ D := by rw [hD, abs_sub_comm]; exact le_abs_self _
      linarith [mul_le_mul_of_nonneg_left hD' (sub_nonneg.mpr hl1),
        mul_le_mul_of_nonneg_right (show 1 - ((r3:ℝ) + r4) / (z1 + z2) ≤ δ by linarith) hD0]
  have hβc := mul_le_mul_of_nonneg_left hcw hβ
  have hdist : δ * (L * X + β * D) = L * (δ * X) + β * (δ * D) := by ring
  linarith [hrw, l1, l2, l3, l4, hLX, hβc, hδε, hdist]

lemma good_succ_conc {M : Model Ω} (hS : M.Standing) {n : ℕ} (hG : Good M n) (t : ℕ) (ω : Ω) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun s : ℝ × ℝ => valueAux M (n + 1) t s.1 s.2 ω) := by
  obtain ⟨K, hK0, B, hB0, hCb, hCc, hCm⟩ := Cn_facts hS hG
  obtain ⟨K', hK'0, hK'⟩ := objN_bound hS hG
  have hq := (std_bounds hS).1
  have hβ0 := (std_bounds hS).2.2.2.1
  refine ⟨(convex_Ici 0).prod (convex_Ici 0), ?_⟩
  rintro ⟨u1, u2⟩ ⟨hu1, hu2⟩ ⟨w1, w2⟩ ⟨hw1, hw2⟩ a b ha hb hab
  have hu1' : (0:ℝ) ≤ u1 := hu1
  have hu2' : (0:ℝ) ≤ u2 := hu2
  have hw1' : (0:ℝ) ≤ w1 := hw1
  have hw2' : (0:ℝ) ≤ w2 := hw2
  have hc1 : 0 ≤ a * u1 + b * w1 := add_nonneg (mul_nonneg ha hu1') (mul_nonneg hb hw1')
  have hc2 : 0 ≤ a * u2 + b * w2 := add_nonneg (mul_nonneg ha hu2') (mul_nonneg hb hw2')
  have hpt : (a • (u1, u2) + b • (w1, w2) : ℝ × ℝ) = (a * u1 + b * w1, a * u2 + b * w2) := by
    simp
  show a * valueAux M (n + 1) t u1 u2 ω + b * valueAux M (n + 1) t w1 w2 ω ≤
    valueAux M (n + 1) t (a • (u1, u2) + b • (w1, w2) : ℝ × ℝ).1
      (a • (u1, u2) + b • (w1, w2) : ℝ × ℝ).2 ω
  rw [hpt]
  dsimp only
  rw [valueAux_succ, valueAux_succ, valueAux_succ]
  refine sSup_comb ha hb hab ⟨_, 0, 0, 0, 0, feas0 hq.le hu1' hu2', rfl⟩
    ⟨_, 0, 0, 0, 0, feas0 hq.le hw1' hw2', rfl⟩ ?_
  rintro x ⟨y1, y2, z1, z2, hF, rfl⟩ y ⟨y1', y2', z1', z2', hF', rfl⟩
  have hFc : Feasible M.q (a * u1 + b * w1) (a * u2 + b * w2) (a * y1 + b * y1')
      (a * y2 + b * y2') (a * z1 + b * z1') (a * z2 + b * z2') := by
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hF
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hF'
    refine ⟨add_nonneg (mul_nonneg ha e1) (mul_nonneg hb f1),
      add_nonneg (mul_nonneg ha e2) (mul_nonneg hb f2),
      add_nonneg (mul_nonneg ha e3) (mul_nonneg hb f3),
      add_nonneg (mul_nonneg ha e4) (mul_nonneg hb f4), ?_, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left e5 ha, mul_le_mul_of_nonneg_left f5 hb]
    · nlinarith [mul_le_mul_of_nonneg_left e6 ha, mul_le_mul_of_nonneg_left f6 hb]
    · nlinarith [mul_le_mul_of_nonneg_left e7 ha, mul_le_mul_of_nonneg_left f7 hb]
  refine le_trans ?_ (le_csSup (SN_bdd hK' t ω hc1 hc2) ⟨_, _, _, _, hFc, rfl⟩)
  have hrw : reward (M.price t ω) M.q M.α (a * u1 + b * w1) (a * u2 + b * w2) (a * y1 + b * y1')
      (a * y2 + b * y2') (a * z1 + b * z1') (a * z2 + b * z2') =
      a * reward (M.price t ω) M.q M.α u1 u2 y1 y2 z1 z2 +
        b * reward (M.price t ω) M.q M.α w1 w2 y1' y2' z1' z2' := by
    simp only [reward]
    linear_combination ((M.price t ω).cP * M.q) * hab
  have hZ : a * z1 + b * z1' + (a * z2 + b * z2') = a * (z1 + z2) + b * (z1' + z2') := by ring
  have hcc := (hCc t ω).2 (show z1 + z2 ∈ Set.Ici (0:ℝ) from add_nonneg hF.2.2.1 hF.2.2.2.1)
    (show z1' + z2' ∈ Set.Ici (0:ℝ) from add_nonneg hF'.2.2.1 hF'.2.2.2.1) ha hb hab
  simp only [smul_eq_mul] at hcc
  simp only [objN, hrw, hZ]
  nlinarith [mul_le_mul_of_nonneg_left hcc hβ0.le]

open Classical in
lemma good_succ_meas {M : Model Ω} (hS : M.Standing) {n : ℕ} (hG : Good M n) (t : ℕ)
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) (ha0 : ∀ ω, 0 ≤ a ω)
    (hb0 : ∀ ω, 0 ≤ b ω) :
    Measurable (fun ω => valueAux M (n + 1) t (a ω) (b ω) ω) := by
  obtain ⟨K, hK0, B, hB0, hCb, hCc, hCm⟩ := Cn_facts hS hG
  obtain ⟨K', hK'0, hK'⟩ := objN_bound hS hG
  have hq := (std_bounds hS).1
  have hβ0 := (std_bounds hS).2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, hmeas⟩ := hS
  let g : ℚ × ℚ × ℚ × ℚ → Ω → ℝ := fun r ω =>
    if Feasible M.q (a ω) (b ω) r.1 r.2.1 r.2.2.1 r.2.2.2 then
      objN M n t ω (a ω) (b ω) r.1 r.2.1 r.2.2.1 r.2.2.2
    else objN M n t ω (a ω) (b ω) 0 0 0 0
  have hobjm : ∀ y1 y2 z1 z2 : ℝ, 0 ≤ z1 + z2 →
      Measurable (fun ω => objN M n t ω (a ω) (b ω) y1 y2 z1 z2) := by
    intro y1 y2 z1 z2 hz
    obtain ⟨hpC, hp1, hp2, hcH, hcP, -, -, -⟩ := hmeas t
    have hC := hCm t (z1 + z2) hz
    simp only [objN, reward]
    fun_prop
  have hgm : ∀ r, Measurable (g r) := by
    rintro ⟨r1, r2, r3, r4⟩
    have hset : MeasurableSet {ω | Feasible M.q (a ω) (b ω) r1 r2 r3 r4} := by
      simp only [Feasible, Set.setOf_and]
      exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        ((MeasurableSet.const _).inter
        ((measurableSet_le measurable_const ha).inter (measurableSet_le measurable_const hb))))))
    by_cases hr : (0:ℝ) ≤ (r3:ℝ) + (r4:ℝ)
    · exact Measurable.ite hset (hobjm _ _ _ _ hr) (hobjm 0 0 0 0 (by norm_num))
    · have : g (r1, r2, r3, r4) = fun ω => objN M n t ω (a ω) (b ω) 0 0 0 0 := by
        funext ω
        simp only [g]
        rw [if_neg]
        rintro ⟨-, -, h3, h4, -⟩
        exact hr (add_nonneg h3 h4)
      rw [this]
      exact hobjm 0 0 0 0 (by norm_num)
  have heq : (fun ω => valueAux M (n + 1) t (a ω) (b ω) ω) = fun ω => ⨆ r, g r ω := by
    funext ω
    rw [valueAux_succ]
    have hbdd := SN_bdd hK' t ω (ha0 ω) (hb0 ω)
    have hF0 := feas0 hq.le (ha0 ω) (hb0 ω)
    have hmem : ∀ r, g r ω ∈ SN M n t (a ω) (b ω) ω := by
      intro r
      simp only [g]
      split_ifs with h
      · exact ⟨_, _, _, _, h, rfl⟩
      · exact ⟨0, 0, 0, 0, hF0, rfl⟩
    have hgb : BddAbove (Set.range fun r => g r ω) := by
      obtain ⟨c, hc⟩ := hbdd
      exact ⟨c, by rintro _ ⟨r, rfl⟩; exact hc (hmem r)⟩
    apply le_antisymm
    · refine csSup_le ⟨_, 0, 0, 0, 0, hF0, rfl⟩ ?_
      rintro v ⟨y1, y2, z1, z2, hF, rfl⟩
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨r1, r2, r3, r4, hFr, hle⟩ := approx (M.price t ω) M.q M.α M.β (a ω) (b ω)
        y1 y2 z1 z2 ε (Cn M n t ω) hβ0.le (hCc t ω) hF hε
      have hg : g (r1, r2, r3, r4) ω = objN M n t ω (a ω) (b ω) r1 r2 r3 r4 := if_pos hFr
      have h2 := le_ciSup hgb (r1, r2, r3, r4)
      rw [hg] at h2
      unfold objN at h2 ⊢
      linarith
    · exact ciSup_le fun r => le_csSup hbdd (hmem r)
  rw [heq]
  exact Measurable.iSup hgm

lemma good_succ {M : Model Ω} (hS : M.Standing) {n : ℕ} (hG : Good M n) : Good M (n + 1) := by
  obtain ⟨K', hK'0, hK'⟩ := objN_bound hS hG
  have hq := (std_bounds hS).1
  refine ⟨⟨K', hK'0, fun t s1 s2 ω hs1 hs2 => ?_⟩, fun t ω => good_succ_conc hS hG t ω,
    fun t a b ha hb ha0 hb0 => good_succ_meas hS hG t a b ha hb ha0 hb0⟩
  have hF0 := feas0 hq.le hs1 hs2
  rw [valueAux_succ, abs_le]
  constructor
  · have h0 := hK' t ω s1 s2 0 0 0 0 hs1 hs2 hF0
    exact (abs_le.mp h0).1.trans (le_csSup (SN_bdd hK' t ω hs1 hs2) ⟨0, 0, 0, 0, hF0, rfl⟩)
  · refine csSup_le ⟨_, 0, 0, 0, 0, hF0, rfl⟩ ?_
    rintro v ⟨y1, y2, z1, z2, hF, rfl⟩
    exact (le_abs_self _).trans (hK' t ω s1 s2 y1 y2 z1 z2 hs1 hs2 hF)

lemma good_all {M : Model Ω} (hS : M.Standing) : ∀ n, Good M n
  | 0 => good_zero M
  | n + 1 => good_succ hS (good_all hS n)

end HogPres

open HogFarm.SalesAlloc in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hS : M.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T) (ω : Ω) :
    ConcaveOn ℝ (Set.Ici 0) (cont M t ω) ∧
    ConcaveOn ℝ (Set.Ici 0) (holdGain M t ω) := by
  have hβ0 : 0 ≤ M.β := (HogPres.std_bounds hS).2.2.2.1.le
  obtain ⟨-, -, -, -, -, hCc, -⟩ := HogPres.Cn_facts hS (HogPres.good_all hS (M.T - t))
  have hcont : cont M t ω = fun Z => M.β * HogPres.Cn M (M.T - t) t ω Z := by
    funext Z
    simp only [cont, value, HogPres.Cn]
    rw [show M.T + 1 - (t + 1) = M.T - t by omega]
  have h1 : ConcaveOn ℝ (Set.Ici 0) (cont M t ω) := by
    rw [hcont]; exact (hCc t ω).smul hβ0
  refine ⟨h1, convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have := h1.2 hx hy ha hb hab
  simp only [holdGain, smul_eq_mul] at this ⊢
  nlinarith [this]
