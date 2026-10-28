-- Prove2me | solution 1 for IsingLTL.BeliefProp.theorem_2_6_bp_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T09:46:49.244997+00:00
-- url     : https://prove2.me/submissions/a2fc00e0-a820-420a-8f80-951241b8b7a3

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_BPIteration

set_option autoImplicit false

namespace BPConv183

/-- `Φ(q) = (a + q)/(1 + a q)`: the ratio map of one incoming message. -/
noncomputable def Phi (a q : ℝ) : ℝ := (a + q) / (1 + a * q)

/-- `ψ(s) = log Φ(e^s)`. -/
noncomputable def psi (a s : ℝ) : ℝ := Real.log (a + Real.exp s) - Real.log (1 + a * Real.exp s)

lemma psi_eq (a s : ℝ) (ha : 0 < a) : psi a s = Real.log (Phi a (Real.exp s)) := by
  unfold psi Phi
  rw [Real.log_div (by positivity) (by positivity)]

lemma Phi_bounds (a q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    a ≤ Phi a q ∧ Phi a q ≤ 1 := by
  unfold Phi
  have hd : 0 < 1 + a * q := by positivity
  constructor
  · rw [le_div_iff₀ hd]; nlinarith [mul_nonneg (mul_nonneg ha.le hq) (sub_nonneg.2 ha1)]
  · rw [div_le_one hd]; nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hq1)]

lemma logPhi_bounds (a q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.log a ≤ Real.log (Phi a q) ∧ Real.log (Phi a q) ≤ 0 := by
  obtain ⟨h1, h2⟩ := Phi_bounds a q ha ha1 hq hq1
  exact ⟨Real.log_le_log ha h1, Real.log_nonpos (by linarith) h2⟩

lemma dformula (a y : ℝ) (ha : 0 < a) (hy : 0 < y) :
    y / (a + y) - a * y / (1 + a * y) = y * (1 - a ^ 2) / ((a + y) * (1 + a * y)) := by
  have h1 : (a + y) ≠ 0 := by positivity
  have h2 : (1 + a * y) ≠ 0 := by positivity
  field_simp
  ring

lemma psi_hasDerivAt (a : ℝ) (ha : 0 < a) (s : ℝ) :
    HasDerivAt (psi a)
      (Real.exp s / (a + Real.exp s) - a * Real.exp s / (1 + a * Real.exp s)) s := by
  have h1 : HasDerivAt (fun s => a + Real.exp s) (Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_add a
  have h2 : HasDerivAt (fun s => 1 + a * Real.exp s) (a * Real.exp s) s :=
    ((Real.hasDerivAt_exp s).const_mul a).const_add 1
  have p1 : 0 < a + Real.exp s := by positivity
  have p2 : 0 < 1 + a * Real.exp s := by positivity
  exact (h1.log p1.ne').sub (h2.log p2.ne')

lemma psi_deriv (a : ℝ) (ha : 0 < a) (s : ℝ) :
    deriv (psi a) s = Real.exp s * (1 - a ^ 2) / ((a + Real.exp s) * (1 + a * Real.exp s)) := by
  rw [(psi_hasDerivAt a ha s).deriv, dformula a _ ha (Real.exp_pos s)]

lemma psi_differentiable (a : ℝ) (ha : 0 < a) : Differentiable ℝ (psi a) :=
  fun s => (psi_hasDerivAt a ha s).differentiableAt

lemma psi_continuous (a : ℝ) (ha : 0 < a) : Continuous (psi a) :=
  (psi_differentiable a ha).continuous

lemma psi_mono (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : Monotone (psi a) := by
  apply monotone_of_deriv_nonneg (psi_differentiable a ha)
  intro s
  rw [psi_deriv a ha s]
  have : 0 ≤ 1 - a ^ 2 := by nlinarith
  positivity

lemma psi_convex (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : ConvexOn ℝ (Set.Iic 0) (psi a) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Iic 0) (psi_continuous a ha).continuousOn
    (psi_differentiable a ha).differentiableOn
  rw [interior_Iic]
  intro s1 hs1 s2 hs2 h12
  simp only [Set.mem_Iio] at hs1 hs2
  rw [psi_deriv a ha, psi_deriv a ha]
  set y1 := Real.exp s1 with hy1
  set y2 := Real.exp s2 with hy2
  have p1 : 0 < y1 := Real.exp_pos s1
  have p2 : 0 < y2 := Real.exp_pos s2
  have h12' : y1 ≤ y2 := Real.exp_le_exp.2 h12
  have hy2l : y2 ≤ 1 := by rw [hy2]; exact Real.exp_le_one_iff.2 hs2.le
  have hc : 0 ≤ 1 - a ^ 2 := by nlinarith
  rw [mul_comm y1, mul_comm y2, mul_div_assoc, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hc
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : y2 * ((a + y1) * (1 + a * y1)) - y1 * ((a + y2) * (1 + a * y2))
      = a * (y2 - y1) * (1 - y1 * y2) := by ring
  have : 0 ≤ a * (y2 - y1) * (1 - y1 * y2) := by
    apply mul_nonneg (mul_nonneg ha.le (by linarith))
    nlinarith
  linarith

lemma psi_zero (a : ℝ) (ha : 0 < a) : psi a 0 = 0 := by
  unfold psi; simp [add_comm]

lemma psi_scale (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (s c : ℝ) (hs : s ≤ 0) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) : psi a (c * s) ≤ c * psi a s := by
  have h := (psi_convex a ha ha1).2 (show s ∈ Set.Iic (0:ℝ) from hs)
    (Set.mem_Iic.2 le_rfl) hc0 (sub_nonneg.2 hc1) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, psi_zero a ha] at h
  exact h

lemma psi_bounds (a s : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hs : s ≤ 0) :
    Real.log a ≤ psi a s ∧ psi a s ≤ 0 := by
  rw [psi_eq a s ha]
  exact logPhi_bounds a _ ha ha1 (Real.exp_pos s).le (Real.exp_le_one_iff.2 hs)

lemma abs_exp_sub_le (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  rcases le_total y x with h | h
  · have e1 := Real.add_one_le_exp (y - x)
    have e2 : Real.exp x * Real.exp (y - x) = Real.exp y := by rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 hx
    have e4 := Real.exp_pos x
    rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 h]), abs_of_nonneg (by linarith)]
    nlinarith
  · have e1 := Real.add_one_le_exp (x - y)
    have e2 : Real.exp y * Real.exp (x - y) = Real.exp x := by rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 hy
    have e4 := Real.exp_pos y
    rw [abs_of_nonpos (by linarith [Real.exp_le_exp.2 h]), abs_of_nonpos (by linarith)]
    nlinarith

lemma abs_inv_one_add_le (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    |1 / (1 + X) - 1 / (1 + Y)| ≤ |X - Y| := by
  have h1 : (0:ℝ) < 1 + X := by linarith
  have h2 : (0:ℝ) < 1 + Y := by linarith
  have e : 1 / (1 + X) - 1 / (1 + Y) = (Y - X) / ((1 + X) * (1 + Y)) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + X) * (1 + Y)), abs_sub_comm]
  rw [div_le_iff₀ (by positivity)]
  have : 1 ≤ (1 + X) * (1 + Y) := by nlinarith
  nlinarith [abs_nonneg (X - Y)]

open IsingLTL.BeliefProp

section Graph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The log-ratio form of the BP map. -/
noncomputable def S (a B : ℝ) (x : V → V → ℝ) : V → V → ℝ :=
  fun i j => -2 * B + ∑ l ∈ (G.neighborFinset i).erase j, psi a (x l i)

lemma mem_erase_adj (i j l : V) (hl : l ∈ (G.neighborFinset i).erase j) : G.Adj l i :=
  ((SimpleGraph.mem_neighborFinset G i l).1 (Finset.mem_of_mem_erase hl)).symm

lemma S_congr (a B : ℝ) (x y : V → V → ℝ) (h : ∀ l i, G.Adj l i → x l i = y l i) :
    S G a B x = S G a B y := by
  funext i j
  unfold S
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [h l i (mem_erase_adj G i j l hl)]

lemma S_continuous (a B : ℝ) (ha : 0 < a) : Continuous (S G a B) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  exact continuous_const.add (continuous_finsetSum _ fun l _ =>
    (psi_continuous a ha).comp ((continuous_apply i).comp (continuous_apply l)))

lemma sum_box (B β : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hdeg : ∀ v, G.degree v ≤ Δ) (i j : V)
    (f : V → ℝ) (hf : ∀ l ∈ (G.neighborFinset i).erase j, -(2 * β) ≤ f l ∧ f l ≤ 0) :
    -(2 * B + 2 * β * Δ) ≤ -2 * B + ∑ l ∈ (G.neighborFinset i).erase j, f l ∧
      -2 * B + ∑ l ∈ (G.neighborFinset i).erase j, f l ≤ -2 * B := by
  set s := (G.neighborFinset i).erase j
  have hcard : (s.card : ℝ) ≤ Δ := by
    have : s.card ≤ Δ := (Finset.card_erase_le).trans
      (by rw [G.card_neighborFinset_eq_degree]; exact hdeg i)
    exact_mod_cast this
  have up : ∑ l ∈ s, f l ≤ 0 := Finset.sum_nonpos fun l hl => (hf l hl).2
  have lo : (s.card : ℝ) * (-(2 * β)) ≤ ∑ l ∈ s, f l := by
    have := Finset.card_nsmul_le_sum s f (-(2 * β)) fun l hl => (hf l hl).1
    simpa [nsmul_eq_mul] using this
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hcard) hβ]
  · linarith

lemma S_box (a B β : ℝ) (Δ : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (haβ : Real.log a = -(2 * β))
    (hβ : 0 ≤ β) (hdeg : ∀ v, G.degree v ≤ Δ) (x : V → V → ℝ)
    (hx : ∀ l i, G.Adj l i → x l i ≤ 0) (i j : V) :
    -(2 * B + 2 * β * Δ) ≤ S G a B x i j ∧ S G a B x i j ≤ -2 * B := by
  unfold S
  apply sum_box G B β Δ hβ hdeg i j
  intro l hl
  have := psi_bounds a (x l i) ha ha1 (hx l i (mem_erase_adj G i j l hl))
  rw [haβ] at this
  exact this

lemma S_step (a B β : ℝ) (Δ : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (haβ : Real.log a = -(2 * β))
    (hβ : 0 ≤ β) (hB : 0 < B) (hdeg : ∀ v, G.degree v ≤ Δ) (x y : V → V → ℝ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : ∀ l i, G.Adj l i → x l i ≤ 0) (hy : ∀ l i, G.Adj l i → y l i ≤ 0)
    (hxy : ∀ l i, G.Adj l i → x l i ≤ (1 - δ) * y l i) (i j : V) :
    S G a B x i j ≤ (1 - δ * (1 - 2 * B / (2 * B + 2 * β * Δ))) * S G a B y i j := by
  have hL : 0 < 2 * B + 2 * β * Δ := by positivity
  have hyb := S_box G a B β Δ ha ha1 haβ hβ hdeg y hy i j
  set L := 2 * B + 2 * β * Δ with hLdef
  have hkL : 2 * B / L * L = 2 * B := div_mul_cancel₀ _ hL.ne'
  have hk0 : 0 ≤ 2 * B / L := by positivity
  have hmain : S G a B x i j ≤ (1 - δ) * S G a B y i j - 2 * B * δ := by
    unfold S
    have : ∑ l ∈ (G.neighborFinset i).erase j, psi a (x l i)
        ≤ (1 - δ) * ∑ l ∈ (G.neighborFinset i).erase j, psi a (y l i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l hl
      have hadj := mem_erase_adj G i j l hl
      calc psi a (x l i) ≤ psi a ((1 - δ) * y l i) := psi_mono a ha ha1 (hxy l i hadj)
        _ ≤ (1 - δ) * psi a (y l i) :=
          psi_scale a ha ha1 _ _ (hy l i hadj) (by linarith) (by linarith)
    nlinarith
  have hk : -(2 * B) ≤ 2 * B / L * S G a B y i j := by
    have := mul_le_mul_of_nonneg_left hyb.1 hk0
    rw [mul_neg, hkL] at this
    exact this
  nlinarith [mul_le_mul_of_nonneg_left hk hδ0]

/-- Closeness in the multiplicative sense, at every pair. -/
def Close (δ : ℝ) (x y : V → V → ℝ) : Prop :=
  ∀ i j, x i j ≤ (1 - δ) * y i j ∧ y i j ≤ (1 - δ) * x i j

/-- The box `[-L, -2B]`, at every pair. -/
def Box (L B : ℝ) (x : V → V → ℝ) : Prop := ∀ i j, -L ≤ x i j ∧ x i j ≤ -2 * B

lemma box_close (L B : ℝ) (hL : 0 < L) (hBL : 2 * B ≤ L) (hB : 0 < B) (x y : V → V → ℝ)
    (hx : Box L B x) (hy : Box L B y) : Close (1 - 2 * B / L) x y := by
  have hkL : 2 * B / L * L = 2 * B := div_mul_cancel₀ _ hL.ne'
  have hk0 : 0 ≤ 2 * B / L := by positivity
  intro i j
  have h1 := mul_le_mul_of_nonneg_left (hy i j).1 hk0
  have h2 := mul_le_mul_of_nonneg_left (hx i j).1 hk0
  rw [mul_neg, hkL] at h1 h2
  constructor <;> nlinarith [hx i j, hy i j]

lemma close_abs (L B δ : ℝ) (x y : V → V → ℝ) (hx : Box L B x) (hy : Box L B y)
    (hc : Close δ x y) (hδ : 0 ≤ δ) (i j : V) : |x i j - y i j| ≤ δ * L := by
  rw [abs_sub_le_iff]
  have := hc i j
  have := hx i j
  have := hy i j
  constructor <;> nlinarith

lemma close_step (a B β : ℝ) (Δ : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (haβ : Real.log a = -(2 * β))
    (hβ : 0 ≤ β) (hB : 0 < B) (hdeg : ∀ v, G.degree v ≤ Δ) (x y : V → V → ℝ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : Box (2 * B + 2 * β * Δ) B x) (hy : Box (2 * B + 2 * β * Δ) B y) (hc : Close δ x y) :
    Close (δ * (1 - 2 * B / (2 * B + 2 * β * Δ))) (S G a B x) (S G a B y) := by
  have hx0 : ∀ l i, G.Adj l i → x l i ≤ 0 := fun l i _ => by linarith [(hx l i).2]
  have hy0 : ∀ l i, G.Adj l i → y l i ≤ 0 := fun l i _ => by linarith [(hy l i).2]
  intro i j
  exact ⟨S_step G a B β Δ ha ha1 haβ hβ hB hdeg x y δ hδ0 hδ1 hx0 hy0
      (fun l i _ => (hc l i).1) i j,
    S_step G a B β Δ ha ha1 haβ hβ hB hdeg y x δ hδ0 hδ1 hy0 hx0
      (fun l i _ => (hc l i).2) i j⟩

noncomputable def useq (a B : ℝ) (n : ℕ) : V → V → ℝ := (S G a B)^[n] (fun _ _ => -2 * B)

lemma useq_succ (a B : ℝ) (n : ℕ) : useq G a B (n + 1) = S G a B (useq G a B n) :=
  Function.iterate_succ_apply' _ _ _

lemma exists_fix (a B β : ℝ) (Δ : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (haβ : Real.log a = -(2 * β))
    (hβ : 0 ≤ β) (hB : 0 < B) (hdeg : ∀ v, G.degree v ≤ Δ) :
    ∃ s : V → V → ℝ, S G a B s = s ∧ Box (2 * B + 2 * β * Δ) B s := by
  have hL : 0 < 2 * B + 2 * β * Δ := by positivity
  have hBL : 2 * B ≤ 2 * B + 2 * β * Δ := by nlinarith [mul_nonneg hβ (Nat.cast_nonneg Δ : (0:ℝ) ≤ Δ)]
  set L := 2 * B + 2 * β * Δ with hLdef
  set κ := 2 * B / L with hκ
  have hk0 : 0 < κ := by positivity
  have hk1 : κ ≤ 1 := by rw [hκ, div_le_one hL]; exact hBL
  have hbox : ∀ n, Box L B (useq G a B n) := by
    intro n
    induction n with
    | zero => intro i j; simp only [useq, Function.iterate_zero, id]; constructor <;> linarith
    | succ n ih =>
      rw [useq_succ]
      intro i j
      exact S_box G a B β Δ ha ha1 haβ hβ hdeg _ (fun l i _ => by linarith [(ih l i).2]) i j
  have hclose : ∀ n, Close ((1 - κ) ^ (n + 1)) (useq G a B n) (useq G a B (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using box_close L B hL hBL hB _ _ (hbox 0) (hbox 1)
    | succ n ih =>
      have := close_step G a B β Δ ha ha1 haβ hβ hB hdeg _ _ _ (pow_nonneg (by linarith) _)
        (pow_le_one₀ (by linarith) (by linarith)) (hbox n) (hbox (n + 1)) ih
      rw [← useq_succ, ← useq_succ] at this
      rw [pow_succ]
      exact this
  have hdist : ∀ n, dist (useq G a B n) (useq G a B (n + 1)) ≤ (L * (1 - κ)) * (1 - κ) ^ n := by
    intro n
    have h0 : 0 ≤ (L * (1 - κ)) * (1 - κ) ^ n :=
      mul_nonneg (mul_nonneg hL.le (by linarith)) (pow_nonneg (by linarith) n)
    rw [dist_pi_le_iff h0]; intro i
    rw [dist_pi_le_iff h0]; intro j
    rw [Real.dist_eq]
    have := close_abs L B _ _ _ (hbox n) (hbox (n + 1)) (hclose n) (pow_nonneg (by linarith) _) i j
    calc _ ≤ (1 - κ) ^ (n + 1) * L := this
      _ = _ := by ring
  have hc := cauchySeq_of_le_geometric (1 - κ) (L * (1 - κ)) (by linarith) hdist
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hc
  have h1 : Filter.Tendsto (fun n => useq G a B (n + 1)) Filter.atTop (nhds s) :=
    hs.comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto (fun n => useq G a B (n + 1)) Filter.atTop (nhds (S G a B s)) := by
    have := ((S_continuous G a B ha).tendsto s).comp hs
    refine this.congr ?_
    intro n
    simp only [Function.comp, useq_succ]
  refine ⟨s, tendsto_nhds_unique h2 h1, fun i j => ?_⟩
  have hij : Filter.Tendsto (fun n => useq G a B n i j) Filter.atTop (nhds (s i j)) :=
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hs i) j
  exact ⟨ge_of_tendsto' hij (fun n => (hbox n i j).1), le_of_tendsto' hij (fun n => (hbox n i j).2)⟩

end Graph

section BP
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma msg_facts (m : Bool → ℝ) (hm : IsDistribution m) (hp : m false ≤ m true) :
    0 < m true ∧ 0 ≤ m false ∧ m true + m false = 1 ∧ m false / m true ≤ 1 ∧ m true ≤ 1 := by
  obtain ⟨h0, h1⟩ := hm
  rw [Fintype.sum_bool] at h1
  have hf := h0 false
  have ht : 0 < m true := by linarith
  exact ⟨ht, hf, h1, (div_le_one ht).2 hp, by linarith⟩

lemma dist_of_ratio (m : Bool → ℝ) (hm : IsDistribution m) (ht : 0 < m true) (r : ℝ)
    (hr : m false / m true = r) : m true = 1 / (1 + r) ∧ m false = r / (1 + r) := by
  obtain ⟨h0, h1⟩ := hm
  rw [Fintype.sum_bool] at h1
  have hf : m false = r * m true := by rw [← hr]; field_simp
  have hr0 : 0 ≤ r := by rw [← hr]; exact div_nonneg (h0 false) ht.le
  have hd : (0:ℝ) < 1 + r := by linarith
  have hT : m true = 1 / (1 + r) := by
    rw [eq_div_iff hd.ne']; linear_combination h1 - hf
  refine ⟨hT, ?_⟩
  rw [hf, hT]; field_simp

lemma tv_bool (p q : Bool → ℝ) (hp : IsDistribution p) (hq : IsDistribution q) :
    tvDist p q = |p true - q true| := by
  have h1 := hp.2
  have h2 := hq.2
  rw [Fintype.sum_bool] at h1 h2
  unfold tvDist
  rw [Fintype.sum_bool]
  have : p false - q false = -(p true - q true) := by linarith
  rw [this, abs_neg]; ring

lemma sum_true (β : ℝ) (m : Bool → ℝ) :
    ∑ xl : Bool, Real.exp (β * spin true * spin xl) * m xl =
      Real.exp β * m true + Real.exp (-β) * m false := by
  simp [Fintype.sum_bool, spin]

lemma sum_false (β : ℝ) (m : Bool → ℝ) :
    ∑ xl : Bool, Real.exp (β * spin false * spin xl) * m xl =
      Real.exp (-β) * m true + Real.exp β * m false := by
  simp [Fintype.sum_bool, spin]

lemma ratio_eq (β p f : ℝ) (hp : 0 < p) (hf : 0 ≤ f) :
    (Real.exp (-β) * p + Real.exp β * f) / (Real.exp β * p + Real.exp (-β) * f)
      = Phi (Real.exp (-(2 * β))) (f / p) := by
  have e1 : Real.exp (-β) = Real.exp (-(2 * β)) * Real.exp β := by
    rw [← Real.exp_add]; ring_nf
  have hb := Real.exp_pos β
  have ha := Real.exp_pos (-(2 * β))
  have hp0 : p ≠ 0 := hp.ne'
  have hq : 0 ≤ f / p := div_nonneg hf hp.le
  have h1 : Real.exp β * p + Real.exp (-(2 * β)) * Real.exp β * f ≠ 0 := by
    have : 0 < Real.exp β * p + Real.exp (-(2 * β)) * Real.exp β * f := by
      have := mul_nonneg (mul_nonneg ha.le hb.le) hf
      nlinarith [mul_pos hb hp]
    exact this.ne'
  have h2 : 1 + Real.exp (-(2 * β)) * (f / p) ≠ 0 := by
    have := mul_nonneg ha.le hq
    linarith
  unfold Phi
  rw [e1, div_eq_div_iff h1 h2]
  field_simp

/-- Log-ratio `log (ν(−)/ν(+))` of a message family. -/
noncomputable def lr (ν : V → V → Bool → ℝ) (i j : V) : ℝ := Real.log (ν i j false / ν i j true)

lemma bpIter_succ (β B : ℝ) (n : ℕ) (ν0 : V → V → Bool → ℝ) :
    bpIter G β B (n + 1) ν0 = bp G β B (bpIter G β B n ν0) := by
  unfold bpIter; exact Function.iterate_succ_apply' _ _ _

lemma bp_facts (β B : ℝ) (ν : V → V → Bool → ℝ) (hm : IsMsgFamily G ν) (hp : IsPositiveMsg G ν)
    (i j : V) (hij : G.Adj i j) :
    IsDistribution (bp G β B ν i j) ∧ 0 < bp G β B ν i j true ∧ 0 < bp G β B ν i j false ∧
      lr (bp G β B ν) i j =
        -2 * B + ∑ l ∈ (G.neighborFinset i).erase j,
          Real.log (Phi (Real.exp (-(2 * β))) (ν l i false / ν l i true)) := by
  have hmsg : ∀ l ∈ (G.neighborFinset i).erase j, 0 < ν l i true ∧ 0 ≤ ν l i false ∧
      ν l i true + ν l i false = 1 ∧ ν l i false / ν l i true ≤ 1 ∧ ν l i true ≤ 1 :=
    fun l hl => msg_facts _ (hm l i (mem_erase_adj G i j l hl)) (hp l i (mem_erase_adj G i j l hl))
  have hT : bpUnnorm G β B ν i j true = Real.exp B * ∏ l ∈ (G.neighborFinset i).erase j,
      (Real.exp β * ν l i true + Real.exp (-β) * ν l i false) := by
    simp only [bpUnnorm, sum_true]; simp [spin]
  have hF : bpUnnorm G β B ν i j false = Real.exp (-B) * ∏ l ∈ (G.neighborFinset i).erase j,
      (Real.exp (-β) * ν l i true + Real.exp β * ν l i false) := by
    simp only [bpUnnorm, sum_false]; simp [spin]
  have pT : ∀ l ∈ (G.neighborFinset i).erase j,
      0 < Real.exp β * ν l i true + Real.exp (-β) * ν l i false := fun l hl =>
    add_pos_of_pos_of_nonneg (mul_pos (Real.exp_pos _) (hmsg l hl).1)
      (mul_nonneg (Real.exp_pos _).le (hmsg l hl).2.1)
  have pF : ∀ l ∈ (G.neighborFinset i).erase j,
      0 < Real.exp (-β) * ν l i true + Real.exp β * ν l i false := fun l hl =>
    add_pos_of_pos_of_nonneg (mul_pos (Real.exp_pos _) (hmsg l hl).1)
      (mul_nonneg (Real.exp_pos _).le (hmsg l hl).2.1)
  have UT : 0 < bpUnnorm G β B ν i j true := by
    rw [hT]; exact mul_pos (Real.exp_pos _) (Finset.prod_pos pT)
  have UF : 0 < bpUnnorm G β B ν i j false := by
    rw [hF]; exact mul_pos (Real.exp_pos _) (Finset.prod_pos pF)
  have D : 0 < bpUnnorm G β B ν i j true + bpUnnorm G β B ν i j false := by linarith
  have hbp : ∀ x, bp G β B ν i j x = bpUnnorm G β B ν i j x /
      (bpUnnorm G β B ν i j true + bpUnnorm G β B ν i j false) := fun x => by
    simp [bp, hij]
  have hnn : ∀ x, 0 ≤ bpUnnorm G β B ν i j x := fun x => by
    cases x
    · exact UF.le
    · exact UT.le
  refine ⟨⟨fun x => by rw [hbp]; exact div_nonneg (hnn x) D.le, ?_⟩, ?_, ?_, ?_⟩
  · rw [Fintype.sum_bool, hbp, hbp, ← add_div, div_self D.ne']
  · rw [hbp]; exact div_pos UT D
  · rw [hbp]; exact div_pos UF D
  · unfold lr
    rw [hbp, hbp, div_div_div_cancel_right₀ D.ne', hF, hT, mul_div_mul_comm,
      ← Finset.prod_div_distrib, ← Real.exp_sub]
    have hPhi : ∀ l ∈ (G.neighborFinset i).erase j,
        (Real.exp (-β) * ν l i true + Real.exp β * ν l i false) /
          (Real.exp β * ν l i true + Real.exp (-β) * ν l i false)
        = Phi (Real.exp (-(2 * β))) (ν l i false / ν l i true) := fun l hl =>
      ratio_eq β _ _ (hmsg l hl).1 (hmsg l hl).2.1
    rw [Finset.prod_congr rfl hPhi]
    have hpos : ∀ l ∈ (G.neighborFinset i).erase j,
        Phi (Real.exp (-(2 * β))) (ν l i false / ν l i true) ≠ 0 := fun l hl => by
      have hq0 : 0 ≤ ν l i false / ν l i true := div_nonneg (hmsg l hl).2.1 (hmsg l hl).1.le
      have ha := Real.exp_pos (-(2 * β))
      unfold Phi
      exact (div_pos (by linarith) (by nlinarith [mul_nonneg ha.le hq0])).ne'
    rw [Real.log_mul (Real.exp_pos _).ne' (Finset.prod_ne_zero_iff.2 hpos), Real.log_exp,
      Real.log_prod hpos]
    ring_nf

lemma bp_box (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hdeg : ∀ v, G.degree v ≤ Δ)
    (ν : V → V → Bool → ℝ) (hm : IsMsgFamily G ν) (hp : IsPositiveMsg G ν)
    (i j : V) (hij : G.Adj i j) :
    -(2 * B + 2 * β * Δ) ≤ lr (bp G β B ν) i j ∧ lr (bp G β B ν) i j ≤ -2 * B := by
  rw [(bp_facts G β B ν hm hp i j hij).2.2.2]
  apply sum_box G B β Δ hβ hdeg i j
  intro l hl
  have hmf := msg_facts _ (hm l i (mem_erase_adj G i j l hl)) (hp l i (mem_erase_adj G i j l hl))
  have := logPhi_bounds (Real.exp (-(2 * β))) (ν l i false / ν l i true) (Real.exp_pos _)
    (Real.exp_le_one_iff.2 (by linarith)) (div_nonneg hmf.2.1 hmf.1.le) hmf.2.2.2.1
  rw [Real.log_exp] at this
  exact this

lemma bp_S (β B : ℝ) (ν : V → V → Bool → ℝ) (hm : IsMsgFamily G ν) (hp : IsPositiveMsg G ν)
    (hF : ∀ l i, G.Adj l i → 0 < ν l i false) (i j : V) (hij : G.Adj i j) :
    lr (bp G β B ν) i j = S G (Real.exp (-(2 * β))) B (lr ν) i j := by
  rw [(bp_facts G β B ν hm hp i j hij).2.2.2]
  unfold S
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hadj := mem_erase_adj G i j l hl
  have hmf := msg_facts _ (hm l i hadj) (hp l i hadj)
  rw [psi_eq _ _ (Real.exp_pos _), lr, Real.exp_log (div_pos (hF l i hadj) hmf.1)]

lemma bp_pos (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hB : 0 < B) (hdeg : ∀ v, G.degree v ≤ Δ)
    (ν : V → V → Bool → ℝ) (hm : IsMsgFamily G ν) (hp : IsPositiveMsg G ν) :
    IsMsgFamily G (bp G β B ν) ∧ IsPositiveMsg G (bp G β B ν) := by
  refine ⟨fun i j hij => (bp_facts G β B ν hm hp i j hij).1, fun i j hij => ?_⟩
  obtain ⟨-, hT, hF, -⟩ := bp_facts G β B ν hm hp i j hij
  have hb := (bp_box G β B Δ hβ hdeg ν hm hp i j hij).2
  unfold lr at hb
  have : bp G β B ν i j false / bp G β B ν i j true ≤ 1 :=
    (Real.log_nonpos_iff (div_pos hF hT).le).1 (by linarith)
  exact (div_le_one hT).1 this

/-- The fixed-point messages built from a log-ratio family `s`. -/
noncomputable def nuStar (s : V → V → ℝ) : V → V → Bool → ℝ :=
  fun i j x => if G.Adj i j then
    (if x then 1 / (1 + Real.exp (s i j)) else Real.exp (s i j) / (1 + Real.exp (s i j))) else 0

lemma nuStar_facts (s : V → V → ℝ) (i j : V) (hij : G.Adj i j) (hs : s i j ≤ 0) :
    IsDistribution (nuStar G s i j) ∧ nuStar G s i j false ≤ nuStar G s i j true ∧
      0 < nuStar G s i j true ∧ 0 < nuStar G s i j false ∧ lr (nuStar G s) i j = s i j := by
  have he := Real.exp_pos (s i j)
  have he1 : Real.exp (s i j) ≤ 1 := Real.exp_le_one_iff.2 hs
  have hd : (0:ℝ) < 1 + Real.exp (s i j) := by linarith
  have eT : nuStar G s i j true = 1 / (1 + Real.exp (s i j)) := by simp [nuStar, hij]
  have eF : nuStar G s i j false = Real.exp (s i j) / (1 + Real.exp (s i j)) := by
    simp [nuStar, hij]
  refine ⟨⟨fun x => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · cases x
    · rw [eF]; positivity
    · rw [eT]; positivity
  · rw [Fintype.sum_bool, eT, eF, ← add_div, div_self hd.ne']
  · rw [eT, eF]; exact div_le_div_of_nonneg_right he1 hd.le
  · rw [eT]; positivity
  · rw [eF]; positivity
  · unfold lr
    rw [eT, eF, div_div_div_cancel_right₀ hd.ne', div_one, Real.log_exp]

lemma nuStar_fix (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (s : V → V → ℝ)
    (hfix : S G (Real.exp (-(2 * β))) B s = s) (hs : ∀ i j, s i j ≤ 0) :
    bp G β B (nuStar G s) = nuStar G s := by
  have hm : IsMsgFamily G (nuStar G s) := fun i j h => (nuStar_facts G s i j h (hs i j)).1
  have hp : IsPositiveMsg G (nuStar G s) := fun i j h => (nuStar_facts G s i j h (hs i j)).2.1
  have hF : ∀ l i, G.Adj l i → 0 < nuStar G s l i false :=
    fun l i h => (nuStar_facts G s l i h (hs l i)).2.2.2.1
  funext i j x
  by_cases hij : G.Adj i j
  · obtain ⟨hd, hT, -, -⟩ := bp_facts G β B (nuStar G s) hm hp i j hij
    have hS : lr (bp G β B (nuStar G s)) i j = s i j := by
      rw [bp_S G β B _ hm hp hF i j hij,
        S_congr G _ B (lr (nuStar G s)) s (fun l i h => (nuStar_facts G s l i h (hs l i)).2.2.2.2),
        hfix]
    have hr : bp G β B (nuStar G s) i j false / bp G β B (nuStar G s) i j true
        = Real.exp (s i j) := by
      rw [← hS, lr, Real.exp_log (div_pos (bp_facts G β B _ hm hp i j hij).2.2.1 hT)]
    obtain ⟨h1, h2⟩ := dist_of_ratio _ hd hT _ hr
    cases x
    · rw [h2]; simp [nuStar, hij]
    · rw [h1]; simp [nuStar, hij]
  · simp [bp, nuStar, hij]

/-- The log-ratio of `ν` on edges, `s` off edges. -/
noncomputable def xOf (s : V → V → ℝ) (ν : V → V → Bool → ℝ) : V → V → ℝ :=
  fun i j => if G.Adj i j then lr ν i j else s i j

lemma converge (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hB : 0 < B) (hdeg : ∀ v, G.degree v ≤ Δ)
    (s : V → V → ℝ) (hfix : S G (Real.exp (-(2 * β))) B s = s)
    (hbox : Box (2 * B + 2 * β * Δ) B s)
    (ν0 : V → V → Bool → ℝ) (hm0 : IsMsgFamily G ν0) (hp0 : IsPositiveMsg G ν0)
    (t : ℕ) (i j : V) (hij : G.Adj i j) :
    tvDist (bpIter G β B t ν0 i j) (nuStar G s i j) ≤
      (2 * B + 2 * β * Δ + 1) * Real.exp (-(2 * B / (2 * B + 2 * β * Δ)) * t) := by
  have hL : 0 < 2 * B + 2 * β * Δ := by positivity
  have hBL : 2 * B ≤ 2 * B + 2 * β * Δ := by
    nlinarith [mul_nonneg hβ (Nat.cast_nonneg Δ : (0:ℝ) ≤ Δ)]
  set L := 2 * B + 2 * β * Δ with hLdef
  set κ := 2 * B / L with hκ
  have hk0 : 0 < κ := by positivity
  have hk1 : κ ≤ 1 := by rw [hκ, div_le_one hL]; exact hBL
  set a := Real.exp (-(2 * β)) with ha_def
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have haβ : Real.log a = -(2 * β) := Real.log_exp _
  have hs0 : ∀ i j, s i j ≤ 0 := fun i j => by linarith [(hbox i j).2]
  have hI : ∀ t, IsMsgFamily G (bpIter G β B t ν0) ∧ IsPositiveMsg G (bpIter G β B t ν0) := by
    intro t
    induction t with
    | zero => exact ⟨hm0, hp0⟩
    | succ n ih => rw [bpIter_succ]; exact bp_pos G β B Δ hβ hB hdeg _ ih.1 ih.2
  have hFpos : ∀ n l i, G.Adj l i → 0 < bpIter G β B (n + 1) ν0 l i false := by
    intro n l i h
    rw [bpIter_succ]
    exact (bp_facts G β B _ (hI n).1 (hI n).2 l i h).2.2.1
  have hxbox : ∀ n, Box L B (xOf G s (bpIter G β B (n + 1) ν0)) := by
    intro n i j
    by_cases h : G.Adj i j
    · simp only [xOf, if_pos h]
      rw [bpIter_succ]
      exact bp_box G β B Δ hβ hdeg _ (hI n).1 (hI n).2 i j h
    · simp only [xOf, if_neg h]
      exact hbox i j
  have hcl : ∀ n, Close ((1 - κ) ^ (n + 1)) (xOf G s (bpIter G β B (n + 1) ν0)) s := by
    intro n
    induction n with
    | zero => simpa using box_close L B hL hBL hB _ _ (hxbox 0) hbox
    | succ n ih =>
      have hc := close_step G a B β Δ ha ha1 haβ hβ hB hdeg _ _ _ (pow_nonneg (by linarith) _)
        (pow_le_one₀ (by linarith) (by linarith)) (hxbox n) hbox ih
      rw [hfix] at hc
      intro i j
      by_cases h : G.Adj i j
      · have e : xOf G s (bpIter G β B (n + 1 + 1) ν0) i j
            = S G a B (xOf G s (bpIter G β B (n + 1) ν0)) i j := by
          simp only [xOf, if_pos h]
          rw [bpIter_succ G β B (n + 1), bp_S G β B _ (hI (n + 1)).1 (hI (n + 1)).2 (hFpos n) i j h]
          rw [S_congr G a B (lr (bpIter G β B (n + 1) ν0)) (xOf G s (bpIter G β B (n + 1) ν0))
            (fun l i' hl => by simp [xOf, hl])]
        rw [e, pow_succ]
        exact hc i j
      · simp only [xOf, if_neg h]
        have := hs0 i j
        have hd : 0 ≤ (1 - κ) ^ (n + 1 + 1) := pow_nonneg (by linarith) _
        constructor <;> nlinarith
  have hmsgT := (hI t).1 i j hij
  have hS := nuStar_facts G s i j hij (hs0 i j)
  rw [tv_bool _ _ hmsgT hS.1]
  cases t with
  | zero =>
    obtain ⟨a1, -, -, -, a5⟩ := msg_facts _ hmsgT ((hI 0).2 i j hij)
    obtain ⟨b1, -, -, -, b5⟩ := msg_facts _ hS.1 hS.2.1
    simp only [Nat.cast_zero, CharP.cast_eq_zero, mul_zero, Real.exp_zero, mul_one]
    rw [abs_sub_le_iff]
    constructor <;> linarith
  | succ n =>
    have hT : 0 < bpIter G β B (n + 1) ν0 i j true := by
      rw [bpIter_succ]; exact (bp_facts G β B _ (hI n).1 (hI n).2 i j hij).2.1
    have hr : bpIter G β B (n + 1) ν0 i j false / bpIter G β B (n + 1) ν0 i j true
        = Real.exp (lr (bpIter G β B (n + 1) ν0) i j) :=
      (Real.exp_log (div_pos (hFpos n i j hij) hT)).symm
    have e1 := (dist_of_ratio _ hmsgT hT _ hr).1
    have hrs : nuStar G s i j false / nuStar G s i j true = Real.exp (s i j) := by
      rw [← hS.2.2.2.2, lr, Real.exp_log (div_pos hS.2.2.2.1 hS.2.2.1)]
    have e2 := (dist_of_ratio _ hS.1 hS.2.2.1 _ hrs).1
    rw [e1, e2]
    have hxb := hxbox n i j
    have hcl' := close_abs L B _ _ _ (hxbox n) hbox (hcl n) (pow_nonneg (by linarith) _) i j
    simp only [xOf, if_pos hij] at hxb hcl'
    have hxle : lr (bpIter G β B (n + 1) ν0) i j ≤ 0 := by linarith [hxb.2]
    have hexp : 1 - κ ≤ Real.exp (-κ) := by linarith [Real.add_one_le_exp (-κ)]
    calc |1 / (1 + Real.exp (lr (bpIter G β B (n + 1) ν0) i j)) - 1 / (1 + Real.exp (s i j))|
        ≤ |Real.exp (lr (bpIter G β B (n + 1) ν0) i j) - Real.exp (s i j)| :=
          abs_inv_one_add_le _ _ (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ |lr (bpIter G β B (n + 1) ν0) i j - s i j| := abs_exp_sub_le _ _ hxle (hs0 i j)
      _ ≤ (1 - κ) ^ (n + 1) * L := hcl'
      _ ≤ Real.exp (-κ) ^ (n + 1) * (L + 1) :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) hexp _) (by linarith) hL.le (by positivity)
      _ = (L + 1) * Real.exp (-κ * ((n + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_nat_mul]; ring_nf

end BP

theorem main (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hB : 0 < B) :
    ∃ A lam : ℝ, 0 < lam ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ Δ) →
        ∃ νstar : V → V → Bool → ℝ, IsMsgFamily G νstar ∧ bp G β B νstar = νstar ∧
          ∀ ν0 : V → V → Bool → ℝ, IsMsgFamily G ν0 → IsPositiveMsg G ν0 →
            ∀ (t : ℕ) (i j : V), G.Adj i j →
              tvDist (bpIter G β B t ν0 i j) (νstar i j) ≤ A * Real.exp (-lam * t) := by
  refine ⟨2 * B + 2 * β * Δ + 1, 2 * B / (2 * B + 2 * β * Δ), by positivity, ?_⟩
  intro V _ _ G _ hdeg
  have ha : 0 < Real.exp (-(2 * β)) := Real.exp_pos _
  have ha1 : Real.exp (-(2 * β)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  obtain ⟨s, hfix, hbox⟩ := exists_fix G _ B β Δ ha ha1 (Real.log_exp _) hβ hB hdeg
  have hs0 : ∀ i j, s i j ≤ 0 := fun i j => by linarith [(hbox i j).2]
  refine ⟨nuStar G s, fun i j h => (nuStar_facts G s i j h (hs0 i j)).1,
    nuStar_fix G β B Δ hβ s hfix hs0, ?_⟩
  intro ν0 hm0 hp0 t i j hij
  exact converge G β B Δ hβ hB hdeg s hfix hbox ν0 hm0 hp0 t i j hij

end BPConv183

open IsingLTL.BeliefProp in
theorem solution (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hB : 0 < B) :
    ∃ A lam : ℝ, 0 < lam ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ Δ) →
        ∃ νstar : V → V → Bool → ℝ, IsMsgFamily G νstar ∧ bp G β B νstar = νstar ∧
          ∀ ν0 : V → V → Bool → ℝ, IsMsgFamily G ν0 → IsPositiveMsg G ν0 →
            ∀ (t : ℕ) (i j : V), G.Adj i j →
              tvDist (bpIter G β B t ν0 i j) (νstar i j) ≤ A * Real.exp (-lam * t) := by
  exact BPConv183.main β B Δ hβ hB
