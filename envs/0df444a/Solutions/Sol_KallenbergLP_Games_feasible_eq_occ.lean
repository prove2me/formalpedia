-- Prove2me | solution 1 for KallenbergLP.Games.feasible_eq_occ
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:53:28.76788+00:00
-- url     : https://prove2.me/submissions/01834c6b-74b3-44cc-b3fa-d68dd8a3339b

import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController



namespace KallenbergLP.Games

set_option linter.unusedSectionVars false
open Finset

variable {N : ℕ} {α β : Type} [Fintype α] [Fintype β]

theorem History.ext' {n : ℕ} {h1 h2 : History N α β n} (hs : h1.states = h2.states)
    (h1' : h1.act1 = h2.act1) (h2' : h1.act2 = h2.act2) : h1 = h2 := by
  cases h1; cases h2; cases hs; cases h1'; cases h2'; rfl

def History.snoc {n : ℕ} (h : History N α β n) (a : α) (b : β) (k : Fin N) :
    History N α β (n+1) where
  states := Fin.snoc (α := fun _ => Fin N) h.states k
  act1 := Fin.snoc (α := fun _ => α) h.act1 a
  act2 := Fin.snoc (α := fun _ => β) h.act2 b

def History.init' {n : ℕ} (h : History N α β (n+1)) : History N α β n where
  states := Fin.init h.states
  act1 := Fin.init h.act1
  act2 := Fin.init h.act2

theorem snoc_states_lt {n : ℕ} (h : History N α β n) (a : α) (b : β) (k : Fin N)
    (j : Fin (n+2)) (hj : j.val < n+1) : (h.snoc a b k).states j = h.states ⟨j.val, hj⟩ := by
  simp [History.snoc, Fin.snoc, hj]; rfl

theorem snoc_last {n : ℕ} (h : History N α β n) (a : α) (b : β) (k : Fin N) :
    (h.snoc a b k).last = k := by
  show Fin.snoc (α := fun _ => Fin N) h.states k (Fin.last (n+1)) = k
  simp

theorem prefix_snoc_cs {n : ℕ} (h : History N α β n) (a : α) (b : β) (s : Fin N) (k : Fin n) :
    (h.snoc a b s).prefix k.castSucc = h.prefix k := by
  apply History.ext'
  · funext m; simp only [History.prefix]; rw [snoc_states_lt]
  · funext m; simp only [History.prefix, History.snoc]
    have : (⟨m.val, by omega⟩ : Fin (n+1)) = Fin.castSucc ⟨m.val, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · funext m; simp only [History.prefix, History.snoc]
    have : (⟨m.val, by omega⟩ : Fin (n+1)) = Fin.castSucc ⟨m.val, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]

theorem prefix_snoc_last {n : ℕ} (h : History N α β n) (a : α) (b : β) (s : Fin N) :
    (h.snoc a b s).prefix (Fin.last n) = h := by
  apply History.ext'
  · funext m; simp only [History.prefix]
    rw [snoc_states_lt _ _ _ _ _ (by have := m.isLt; simp only [Fin.val_last] at this; omega)]; rfl
  · funext m; simp only [History.prefix, History.snoc]
    have : (⟨m.val, by omega⟩ : Fin (n+1)) = Fin.castSucc m := rfl
    rw [this, Fin.snoc_castSucc]
  · funext m; simp only [History.prefix, History.snoc]
    have : (⟨m.val, by omega⟩ : Fin (n+1)) = Fin.castSucc m := rfl
    rw [this, Fin.snoc_castSucc]

def snocEquiv (n : ℕ) : History N α β n × α × β × Fin N ≃ History N α β (n+1) where
  toFun p := p.1.snoc p.2.1 p.2.2.1 p.2.2.2
  invFun h := (h.init', h.act1 (Fin.last n), h.act2 (Fin.last n), h.states (Fin.last (n+1)))
  left_inv p := by
    obtain ⟨h, a, b, k⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, by simp [History.snoc], by simp [History.snoc], by simp [History.snoc]⟩
    apply History.ext' <;> simp [History.snoc, History.init']
  right_inv h := by
    apply History.ext' <;> simp [History.snoc, History.init']

theorem sum_hist_succ {n : ℕ} (F : History N α β (n+1) → ℝ) :
    ∑ h', F h' = ∑ h : History N α β n, ∑ a, ∑ b, ∑ k, F (h.snoc a b k) := by
  rw [← (snocEquiv n).sum_comp]
  simp [Fintype.sum_prod_type, snocEquiv]

theorem sum_comm3 {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (f : X → Y → Z → ℝ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ x, ∑ y, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem sum_comm4 {X Y Z W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (f : X → Y → Z → W → ℝ) :
    ∑ x, ∑ y, ∑ z, ∑ w, f x y z w = ∑ w, ∑ x, ∑ y, ∑ z, f x y z w := by
  calc ∑ x, ∑ y, ∑ z, ∑ w, f x y z w = ∑ x, ∑ w, ∑ y, ∑ z, f x y z w :=
        Finset.sum_congr rfl (fun x _ => sum_comm3 _)
    _ = _ := Finset.sum_comm

variable (G : Game N α β)

theorem hp_snoc (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) {n : ℕ} (h : History N α β n)
    (a : α) (b : β) (k : Fin N) :
    historyProb G R1 R2 i (n+1) (h.snoc a b k) =
      historyProb G R1 R2 i n h * (R1.choose n h a * R2.choose n h b * G.p h.last a b k) := by
  unfold historyProb
  rw [Fin.prod_univ_castSucc]
  simp only [prefix_snoc_cs, prefix_snoc_last, Fin.val_castSucc, Fin.val_last]
  rw [snoc_states_lt _ _ _ _ _ (by simp)]
  have e1 : ∀ m : Fin n, (h.snoc a b k).act1 m.castSucc = h.act1 m := by
    intro m; simp [History.snoc]
  have e2 : ∀ m : Fin n, (h.snoc a b k).act2 m.castSucc = h.act2 m := by
    intro m; simp [History.snoc]
  have e3 : ∀ m : Fin n, (h.snoc a b k).states ⟨m.val, by omega⟩ = h.states ⟨m.val, by omega⟩ :=
    fun m => snoc_states_lt _ _ _ _ _ _
  have e4 : ∀ m : Fin n, (h.snoc a b k).states ⟨m.val + 1, by omega⟩ =
      h.states ⟨m.val + 1, by omega⟩ := fun m => snoc_states_lt _ _ _ _ _ _
  have e5 : (h.snoc a b k).act1 (Fin.last n) = a := by simp [History.snoc]
  have e6 : (h.snoc a b k).act2 (Fin.last n) = b := by simp [History.snoc]
  have e7 : (h.snoc a b k).states ⟨n, by omega⟩ = h.last := snoc_states_lt _ _ _ _ _ _
  have e8 : (h.snoc a b k).states ⟨n + 1, by omega⟩ = k := snoc_last _ _ _ _
  simp only [e1, e2, e3, e4, e5, e6, e7, e8]
  ring

def qd (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (j : Fin N) : ℝ :=
  ∑ h : History N α β n, if h.last = j then historyProb G R1 R2 i n h else 0

theorem fac_nonneg (s : Fin N) (a : α) (b : β) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxa : a ∉ G.A s → x = 0) (hyb : b ∉ G.B s → y = 0) (k : Fin N) :
    0 ≤ x * y * G.p s a b k := by
  by_cases ha : a ∈ G.A s
  · by_cases hb : b ∈ G.B s
    · exact mul_nonneg (mul_nonneg hx hy) (G.p_nonneg s a ha b hb k)
    · rw [hyb hb]; simp
  · rw [hxa ha]; simp

theorem hp_nonneg (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ)
    (h : History N α β n) : 0 ≤ historyProb G R1 R2 i n h := by
  unfold historyProb
  apply mul_nonneg (by split_ifs <;> norm_num)
  apply Finset.prod_nonneg
  intro k _
  exact fac_nonneg G _ _ _ _ _ (R1.choose_nonneg _ _ _) (R2.choose_nonneg _ _ _)
    (R1.choose_outside _ _ _) (R2.choose_outside _ _ _) _

theorem sap_nonneg (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (j : Fin N) (a : α)
    (b : β) : 0 ≤ stateActionProb G R1 R2 i n j a b := by
  unfold stateActionProb
  apply Finset.sum_nonneg; intro h _
  split_ifs
  · exact mul_nonneg (mul_nonneg (hp_nonneg G _ _ _ _ _) (R1.choose_nonneg _ _ _))
      (R2.choose_nonneg _ _ _)
  · exact le_rfl

theorem sap_outside (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (j : Fin N) (a : α)
    (b : β) (hab : a ∉ G.A j ∨ b ∉ G.B j) : stateActionProb G R1 R2 i n j a b = 0 := by
  unfold stateActionProb
  apply Finset.sum_eq_zero; intro h _
  split_ifs with hj
  · subst hj
    rcases hab with ha | hb
    · rw [R1.choose_outside _ _ _ ha]; simp
    · rw [R2.choose_outside _ _ _ hb]; simp
  · rfl

theorem sap_marg (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (j : Fin N) :
    ∑ a, ∑ b, stateActionProb G R1 R2 i n j a b = qd G R1 R2 i n j := by
  unfold stateActionProb qd
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs
  · have : ∀ a, ∑ b, historyProb G R1 R2 i n h * R1.choose n h a * R2.choose n h b =
        historyProb G R1 R2 i n h * R1.choose n h a := by
      intro a; rw [← Finset.mul_sum, R2.choose_sum_one, mul_one]
    simp only [this]; rw [← Finset.mul_sum, R1.choose_sum_one, mul_one]
  · simp

theorem qd_flow (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (k : Fin N) :
    qd G R1 R2 i (n+1) k =
      ∑ j, ∑ a, ∑ b, stateActionProb G R1 R2 i n j a b * G.p j a b k := by
  unfold qd stateActionProb
  rw [sum_hist_succ]
  simp only [snoc_last, hp_snoc, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  symm
  rw [sum_comm4]
  calc _ = _ := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Fintype.sum_eq_single h.last]
        · simp only [if_true]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring
        · intro j hj; simp [Ne.symm hj]

def hist0 (s : Fin N) : History N α β 0 := ⟨fun _ => s, Fin.elim0, Fin.elim0⟩

theorem qd_zero (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (j : Fin N) :
    qd G R1 R2 i 0 j = if j = i then 1 else 0 := by
  unfold qd
  have e : ∀ h : History N α β 0, h = hist0 h.last := by
    intro h
    apply History.ext'
    · funext m
      have : m = ⟨0, by omega⟩ := Fin.ext (by have := m.isLt; omega)
      subst this; rfl
    · funext m; exact m.elim0
    · funext m; exact m.elim0
  rw [Fintype.sum_eq_single (hist0 j)]
  · simp [hist0, History.last, historyProb]; rfl
  · intro h hh
    rw [if_neg]
    intro hl; apply hh; rw [e h, hl]

theorem sum_comm2 {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    ∑ x, ∑ y, f x y = ∑ y, ∑ x, f x y := by
  rw [Finset.sum_comm]

def gfun (y : Fin N → ℝ) (j : Fin N) (a : α) (b : β) : ℝ :=
  G.r j a b + ∑ k, G.p j a b k * y k - y j

def Qv (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (y : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ j, qd G R1 R2 i n j * y j

theorem flow_dot (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (y : Fin N → ℝ) :
    ∑ k, qd G R1 R2 i (n+1) k * y k =
      ∑ j, ∑ a, ∑ b, stateActionProb G R1 R2 i n j a b * ∑ k, G.p j a b k * y k := by
  simp only [qd_flow, Finset.sum_mul, Finset.mul_sum]
  symm; rw [sum_comm4]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem marg_dot (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (y : Fin N → ℝ) :
    ∑ j, qd G R1 R2 i n j * y j =
      ∑ j, ∑ a, ∑ b, stateActionProb G R1 R2 i n j a b * y j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sap_marg, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]

theorem step_id (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (y : Fin N → ℝ) (n : ℕ) :
    periodReward G R1 R2 i n + Qv G R1 R2 i y (n+1) - Qv G R1 R2 i y n =
      ∑ j, ∑ a, ∑ b, stateActionProb G R1 R2 i n j a b * gfun G y j a b := by
  unfold periodReward Qv gfun
  rw [flow_dot, marg_dot]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem qd_nonneg (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) (j : Fin N) :
    0 ≤ qd G R1 R2 i n j := by
  unfold qd
  apply Finset.sum_nonneg; intro h _
  split_ifs
  · exact hp_nonneg G _ _ _ _ _
  · exact le_rfl

theorem Qv_zero (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (y : Fin N → ℝ) :
    Qv G R1 R2 i y 0 = y i := by
  unfold Qv; simp [qd_zero]

theorem qmu_le (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (μ : Fin N → ℝ) (c : ℝ)
    (hc0 : 0 ≤ c) (hμ : ∀ i, ∀ a ∈ G.A i, ∀ b ∈ G.B i, ∑ j, G.p i a b j * μ j ≤ c * μ i)
    (n : ℕ) : ∑ j, qd G R1 R2 i n j * μ j ≤ c ^ n * μ i := by
  induction n with
  | zero => simp [qd_zero]
  | succ n ih =>
    rw [flow_dot]
    calc _ ≤ ∑ j, ∑ a, ∑ b, stateActionProb G R1 R2 i n j a b * (c * μ j) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ =>
            Finset.sum_le_sum fun b _ => ?_
          by_cases hab : a ∈ G.A j ∧ b ∈ G.B j
          · exact mul_le_mul_of_nonneg_left (hμ j a hab.1 b hab.2) (sap_nonneg G _ _ _ _ _ _ _)
          · rw [sap_outside G _ _ _ _ _ _ _ (by tauto)]; simp
      _ = c * ∑ j, qd G R1 R2 i n j * μ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← sap_marg, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
      _ ≤ c * (c ^ n * μ i) := mul_le_mul_of_nonneg_left ih hc0
      _ = c ^ (n+1) * μ i := by ring

theorem abs_dot_le (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (μ : Fin N → ℝ) (c : ℝ)
    (hμp : ∀ i, 0 < μ i) (hc0 : 0 ≤ c)
    (hμ : ∀ i, ∀ a ∈ G.A i, ∀ b ∈ G.B i, ∑ j, G.p i a b j * μ j ≤ c * μ i)
    (y : Fin N → ℝ) (n : ℕ) :
    |∑ j, qd G R1 R2 i n j * y j| ≤ ((∑ j, |y j| / μ j) * μ i) * c ^ n := by
  set K := ∑ j, |y j| / μ j
  have hy : ∀ j, |y j| ≤ K * μ j := by
    intro j
    have : |y j| / μ j ≤ K :=
      Finset.single_le_sum (f := fun j => |y j| / μ j) (fun j _ => by
        have := hμp j; positivity) (Finset.mem_univ j)
    rw [div_le_iff₀ (hμp j)] at this; exact this
  have hK : 0 ≤ K := Finset.sum_nonneg fun j _ => by have := hμp j; positivity
  calc _ ≤ ∑ j, |qd G R1 R2 i n j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, qd G R1 R2 i n j * (K * μ j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (qd_nonneg G _ _ _ _ _)]
        exact mul_le_mul_of_nonneg_left (hy j) (qd_nonneg G _ _ _ _ _)
    _ = K * ∑ j, qd G R1 R2 i n j * μ j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    _ ≤ K * (c ^ n * μ i) := mul_le_mul_of_nonneg_left (qmu_le G _ _ _ _ _ hc0 hμ n) hK
    _ = _ := by ring

theorem abs_pr_le (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (μ : Fin N → ℝ) (c : ℝ)
    (hμp : ∀ i, 0 < μ i) (hc0 : 0 ≤ c)
    (hμ : ∀ i, ∀ a ∈ G.A i, ∀ b ∈ G.B i, ∑ j, G.p i a b j * μ j ≤ c * μ i) (n : ℕ) :
    |periodReward G R1 R2 i n| ≤
      (((∑ j, |(∑ a, ∑ b, |G.r j a b| : ℝ)| / μ j)) * μ i) * c ^ n := by
  set Rm : Fin N → ℝ := fun j => ∑ a, ∑ b, |G.r j a b|
  have hRm : ∀ j, |Rm j| = Rm j := fun j => abs_of_nonneg (by positivity)
  calc _ ≤ ∑ j, ∑ a, ∑ b, |stateActionProb G R1 R2 i n j a b * G.r j a b| := by
        unfold periodReward
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ a, ∑ b, stateActionProb G R1 R2 i n j a b * Rm j := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_of_nonneg (sap_nonneg G _ _ _ _ _ _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (sap_nonneg G _ _ _ _ _ _ _)
        exact (Finset.single_le_sum (f := fun b => |G.r j a b|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b, |G.r j a b|)
          (fun _ _ => by positivity) (Finset.mem_univ a))
    _ = ∑ j, qd G R1 R2 i n j * Rm j := (marg_dot G _ _ _ _ _).symm
    _ ≤ |∑ j, qd G R1 R2 i n j * Rm j| := le_abs_self _
    _ ≤ _ := by
        have := abs_dot_le G R1 R2 i μ c hμp hc0 hμ Rm n
        simpa [Rm] using this

theorem summable_pr (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (hA : Assumption621 G) :
    Summable (fun n => periodReward G R1 R2 i n) := by
  obtain ⟨μ, c, hμp, hc0, hc1, hμ⟩ := hA
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hc0 hc1).mul_left
    (((∑ j, |(∑ a, ∑ b, |G.r j a b| : ℝ)| / μ j)) * μ i)) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact abs_pr_le G R1 R2 i μ c hμp hc0 hμ n

theorem Qv_tendsto (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (hA : Assumption621 G)
    (y : Fin N → ℝ) : Filter.Tendsto (fun n => Qv G R1 R2 i y n) Filter.atTop (nhds 0) := by
  obtain ⟨μ, c, hμp, hc0, hc1, hμ⟩ := hA
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul
    (((∑ j, |y j| / μ j)) * μ i)
  rw [mul_zero] at ht
  refine squeeze_zero_norm (fun n => ?_) ht
  rw [Real.norm_eq_abs]
  exact abs_dot_le G R1 R2 i μ c hμp hc0 hμ y n

theorem total_le_of_step (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (hA : Assumption621 G)
    (y : Fin N → ℝ) (δ : ℝ)
    (hstep : ∀ n, periodReward G R1 R2 i n + Qv G R1 R2 i y (n+1) - Qv G R1 R2 i y n ≤
      if n = 0 then δ else 0) :
    totalReward G R1 R2 i ≤ y i + δ := by
  have hS := (summable_pr G R1 R2 i hA).hasSum.tendsto_sum_nat
  have hQ := Qv_tendsto G R1 R2 i hA y
  have hR : Filter.Tendsto (fun n => y i - Qv G R1 R2 i y n + δ) Filter.atTop
      (nhds (y i - 0 + δ)) := (tendsto_const_nhds.sub hQ).add tendsto_const_nhds
  rw [sub_zero] at hR
  unfold totalReward
  refine le_of_tendsto_of_tendsto hS hR (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have key : ∀ n, 1 ≤ n → ∑ t ∈ Finset.range n, periodReward G R1 R2 i t +
      Qv G R1 R2 i y n - Qv G R1 R2 i y 0 ≤ δ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => have := hstep 0; simp only [if_pos] at this; simp; linarith
    | succ m hm ih =>
      have := hstep m
      rw [if_neg (by omega)] at this
      rw [Finset.sum_range_succ]; linarith
  have := key n hn
  rw [Qv_zero] at this
  linarith

theorem le_total_of_step (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (hA : Assumption621 G)
    (y : Fin N → ℝ)
    (hstep : ∀ n, 0 ≤ periodReward G R1 R2 i n + Qv G R1 R2 i y (n+1) - Qv G R1 R2 i y n) :
    y i ≤ totalReward G R1 R2 i := by
  have hS := (summable_pr G R1 R2 i hA).hasSum.tendsto_sum_nat
  have hQ := Qv_tendsto G R1 R2 i hA y
  have hR : Filter.Tendsto (fun n => y i - Qv G R1 R2 i y n) Filter.atTop
      (nhds (y i - 0)) := tendsto_const_nhds.sub hQ
  rw [sub_zero] at hR
  unfold totalReward
  refine le_of_tendsto_of_tendsto hR hS (Filter.Eventually.of_forall fun n => ?_)
  have key : ∀ n, 0 ≤ ∑ t ∈ Finset.range n, periodReward G R1 R2 i t +
      Qv G R1 R2 i y n - Qv G R1 R2 i y 0 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => have := hstep m; rw [Finset.sum_range_succ]; linarith
  have := key n
  rw [Qv_zero] at this
  linarith

theorem sap_stat2 (R1 : Policy1 G) (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ) (i : Fin N)
    (n : ℕ) (j : Fin N) (a : α) (b : β) :
    stateActionProb G R1 (stationary2 G ρ hρ) i n j a b =
      ρ j b * ∑ b', stateActionProb G R1 (stationary2 G ρ hρ) i n j a b' := by
  unfold stateActionProb
  simp only [stationary2]
  rw [sum_comm2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs with hj
  · subst hj; rw [← Finset.mul_sum, (hρ h.last).2.2]; ring
  · simp

theorem sap_stat1 (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (R2 : Policy2 G) (i : Fin N)
    (n : ℕ) (j : Fin N) (a : α) (b : β) :
    stateActionProb G (stationary1 G π hπ) R2 i n j a b =
      π j a * ∑ a', stateActionProb G (stationary1 G π hπ) R2 i n j a' b := by
  unfold stateActionProb
  simp only [stationary1]
  rw [sum_comm2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs with hj
  · subst hj
    have e : ∀ (X Y : ℝ), ∑ a', X * π h.last a' * Y = X * Y := by
      intro X Y; rw [← Finset.sum_mul, ← Finset.mul_sum, (hπ h.last).2.2]; ring
    rw [e]; ring
  · simp

theorem sap_stat12 (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (ρ : Fin N → β → ℝ)
    (hρ : IsDecisionRule2 G ρ) (i : Fin N) (n : ℕ) (j : Fin N) (a : α) (b : β) :
    stateActionProb G (stationary1 G π hπ) (stationary2 G ρ hρ) i n j a b =
      π j a * ρ j b * qd G (stationary1 G π hπ) (stationary2 G ρ hρ) i n j := by
  rw [sap_stat2]
  have : ∀ b', stateActionProb G (stationary1 G π hπ) (stationary2 G ρ hρ) i n j a b' =
      π j a * ∑ a', stateActionProb G (stationary1 G π hπ) (stationary2 G ρ hρ) i n j a' b' :=
    fun b' => sap_stat1 G π hπ _ i n j a b'
  simp only [this]
  rw [← Finset.mul_sum, sum_comm2, sap_marg]; ring

/-- Player I arbitrary, player II stationary with a superharmonic-type certificate. -/
theorem total_le_stat2 (hA : Assumption621 G) (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ)
    (y : Fin N → ℝ) (hy : ∀ j, ∀ a ∈ G.A j, ∑ b, ρ j b * gfun G y j a b ≤ 0)
    (R1 : Policy1 G) (i : Fin N) : totalReward G R1 (stationary2 G ρ hρ) i ≤ y i := by
  have := total_le_of_step G R1 (stationary2 G ρ hρ) i hA y 0 (fun n => ?_)
  · simpa using this
  rw [step_id]
  have h0 : (if n = 0 then (0:ℝ) else 0) = 0 := by split_ifs <;> rfl
  rw [h0]
  refine Finset.sum_nonpos fun j _ => Finset.sum_nonpos fun a _ => ?_
  by_cases ha : a ∈ G.A j
  · have : ∀ b, stateActionProb G R1 (stationary2 G ρ hρ) i n j a b * gfun G y j a b =
        (∑ b', stateActionProb G R1 (stationary2 G ρ hρ) i n j a b') * (ρ j b * gfun G y j a b) := by
      intro b; rw [sap_stat2]; ring
    simp only [this]
    rw [← Finset.mul_sum]
    exact mul_nonpos_of_nonneg_of_nonpos
      (Finset.sum_nonneg fun b _ => sap_nonneg G _ _ _ _ _ _ _) (hy j a ha)
  · refine le_of_eq (Finset.sum_eq_zero fun b _ => ?_)
    rw [sap_outside G _ _ _ _ _ _ _ (Or.inl ha)]; simp

/-- Player I stationary with a subharmonic-type certificate, player II arbitrary. -/
theorem le_total_stat1 (hA : Assumption621 G) (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π)
    (y : Fin N → ℝ) (hy : ∀ j, ∀ b ∈ G.B j, 0 ≤ ∑ a, π j a * gfun G y j a b)
    (R2 : Policy2 G) (i : Fin N) : y i ≤ totalReward G (stationary1 G π hπ) R2 i := by
  refine le_total_of_step G (stationary1 G π hπ) R2 i hA y (fun n => ?_)
  rw [step_id]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [sum_comm2]
  refine Finset.sum_nonneg fun b _ => ?_
  by_cases hb : b ∈ G.B j
  · have : ∀ a, stateActionProb G (stationary1 G π hπ) R2 i n j a b * gfun G y j a b =
        (∑ a', stateActionProb G (stationary1 G π hπ) R2 i n j a' b) * (π j a * gfun G y j a b) := by
      intro a; rw [sap_stat1]; ring
    simp only [this]
    rw [← Finset.mul_sum]
    exact mul_nonneg (Finset.sum_nonneg fun a _ => sap_nonneg G _ _ _ _ _ _ _) (hy j b hb)
  · refine le_of_eq (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [sap_outside G _ _ _ _ _ _ _ (Or.inr hb)]; simp

def Gst (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (y : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∑ a, ∑ b, π j a * ρ j b * gfun G y j a b

theorem step_stat12 (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (ρ : Fin N → β → ℝ)
    (hρ : IsDecisionRule2 G ρ) (i : Fin N) (y : Fin N → ℝ) (n : ℕ) :
    periodReward G (stationary1 G π hπ) (stationary2 G ρ hρ) i n +
      Qv G (stationary1 G π hπ) (stationary2 G ρ hρ) i y (n+1) -
      Qv G (stationary1 G π hπ) (stationary2 G ρ hρ) i y n =
      ∑ j, qd G (stationary1 G π hπ) (stationary2 G ρ hρ) i n j * Gst G π ρ y j := by
  rw [step_id]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Gst
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sap_stat12]; ring

theorem total_le_stat12 (hA : Assumption621 G) (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π)
    (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ) (y : Fin N → ℝ) (δ : ℝ) (i : Fin N)
    (hG : ∀ j, Gst G π ρ y j ≤ 0) (hGi : Gst G π ρ y i ≤ δ) :
    totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) i ≤ y i + δ := by
  refine total_le_of_step G _ _ i hA y δ (fun n => ?_)
  rw [step_stat12]
  split_ifs with hn
  · subst hn; simp only [qd_zero]; simpa using hGi
  · exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (qd_nonneg G _ _ _ _ _) (hG j)

theorem le_total_stat12 (hA : Assumption621 G) (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π)
    (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ) (y : Fin N → ℝ) (i : Fin N)
    (hG : ∀ j, 0 ≤ Gst G π ρ y j) :
    y i ≤ totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) i := by
  refine le_total_of_step G _ _ i hA y (fun n => ?_)
  rw [step_stat12]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (qd_nonneg G _ _ _ _ _) (hG j)

section Simplex

variable {γ : Type} [Fintype γ]

def simp' (S : Finset γ) : Set (γ → ℝ) :=
  {x | (∀ c, 0 ≤ x c) ∧ (∀ c, c ∉ S → x c = 0) ∧ ∑ c, x c = 1}

theorem simp'_convex (S : Finset γ) : Convex ℝ (simp' S) := by
  intro x hx z hz s t hs ht hst
  refine ⟨fun c => ?_, fun c hc => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 c; have := hz.1 c; positivity
  · simp [hx.2.1 c hc, hz.2.1 c hc]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2.2, hz.2.2, hst, mul_one]

theorem simp'_compact (S : Finset γ) : IsCompact (simp' S) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : γ → ℝ)) (b := 1)) ?_ ?_
  · have h1 : IsClosed {x : γ → ℝ | ∀ c, 0 ≤ x c} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c)
    have h2 : IsClosed {x : γ → ℝ | ∀ c, c ∉ S → x c = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun c => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply c) continuous_const
    have h3 : IsClosed {x : γ → ℝ | ∑ c, x c = 1} :=
      isClosed_eq (continuous_finsetSum _ fun c _ => continuous_apply c) continuous_const
    exact h1.inter (h2.inter h3)
  · intro x hx
    refine ⟨fun c => hx.1 c, fun c => ?_⟩
    have := Finset.single_le_sum (f := x) (fun c _ => hx.1 c) (Finset.mem_univ c)
    simpa [hx.2.2] using this

theorem single_mem_simp' [DecidableEq γ] (S : Finset γ) (c : γ) (hc : c ∈ S) :
    (Pi.single c 1 : γ → ℝ) ∈ simp' S := by
  refine ⟨fun d => ?_, fun d hd => ?_, ?_⟩
  · by_cases h : d = c
    · subst h; simp
    · simp [h]
  · have : d ≠ c := fun h => hd (h ▸ hc)
    simp [this]
  · simp

theorem wavg_le (S : Finset γ) (x : γ → ℝ) (hx : x ∈ simp' S) (H : γ → ℝ) (C : ℝ)
    (hH : ∀ c ∈ S, H c ≤ C) : ∑ c, x c * H c ≤ C := by
  calc ∑ c, x c * H c ≤ ∑ c, x c * C := by
        refine Finset.sum_le_sum fun c _ => ?_
        by_cases hc : c ∈ S
        · exact mul_le_mul_of_nonneg_left (hH c hc) (hx.1 c)
        · rw [hx.2.1 c hc]; simp
    _ = C := by rw [← Finset.sum_mul, hx.2.2, one_mul]

theorem wavg_ge (S : Finset γ) (x : γ → ℝ) (hx : x ∈ simp' S) (H : γ → ℝ) (C : ℝ)
    (hH : ∀ c ∈ S, C ≤ H c) : C ≤ ∑ c, x c * H c := by
  have := wavg_le S x hx (fun c => -H c) (-C) (fun c hc => neg_le_neg (hH c hc))
  simp only [mul_neg, Finset.sum_neg_distrib] at this
  linarith

theorem wavg_const (S : Finset γ) (x : γ → ℝ) (hx : x ∈ simp' S) (C : ℝ) :
    ∑ c, x c * C = C := by rw [← Finset.sum_mul, hx.2.2, one_mul]

end Simplex

def Mat (i : Fin N) (y : Fin N → ℝ) (a : α) (b : β) : ℝ := G.r i a b + ∑ k, G.p i a b k * y k

def payoff (i : Fin N) (y : Fin N → ℝ) (ρ : β → ℝ) (π : α → ℝ) : ℝ :=
  ∑ b, ρ b * ∑ a, π a * Mat G i y a b

theorem exists_saddle (i : Fin N) (y : Fin N → ℝ) :
    ∃ ρ ∈ simp' (G.B i), ∃ π ∈ simp' (G.A i),
      ∀ ρ' ∈ simp' (G.B i), ∀ π' ∈ simp' (G.A i), payoff G i y ρ π' ≤ payoff G i y ρ' π := by
  classical
  obtain ⟨b0, hb0⟩ := G.B_nonempty i
  obtain ⟨a0, ha0⟩ := G.A_nonempty i
  have hcont1 : ∀ π : α → ℝ, Continuous fun ρ : β → ℝ => payoff G i y ρ π := by
    intro π; unfold payoff; fun_prop
  have hcont2 : ∀ ρ : β → ℝ, Continuous fun π : α → ℝ => payoff G i y ρ π := by
    intro ρ; unfold payoff; fun_prop
  have hlin1 : ∀ π : α → ℝ, ConvexOn ℝ (simp' (G.B i)) fun ρ => payoff G i y ρ π := by
    intro π
    refine ⟨simp'_convex _, fun x _ z _ s t _ _ _ => le_of_eq ?_⟩
    simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hlin2 : ∀ ρ : β → ℝ, ConcaveOn ℝ (simp' (G.A i)) fun π => payoff G i y ρ π := by
    intro ρ
    refine ⟨simp'_convex _, fun x _ z _ s t _ _ _ => le_of_eq ?_⟩
    simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    congr 1 <;> (refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_; ring)
  obtain ⟨ρ, hρ, π, hπ, hs⟩ := Sion.exists_isSaddlePointOn (f := fun ρ π => payoff G i y ρ π)
    ⟨_, single_mem_simp' _ b0 hb0⟩ (simp'_convex _) (simp'_compact _)
    (fun π _ => (hcont1 π).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun π _ => (hlin1 π).quasiconvexOn)
    (simp'_convex _) ⟨_, single_mem_simp' _ a0 ha0⟩ (simp'_compact _)
    (fun ρ _ => (hcont2 ρ).upperSemicontinuous.upperSemicontinuousOn _)
    (fun ρ _ => (hlin2 ρ).quasiconcaveOn)
  exact ⟨ρ, hρ, π, hπ, fun ρ' hρ' π' hπ' => hs ρ' hρ' π' hπ'⟩

noncomputable def rhoS (i : Fin N) (y : Fin N → ℝ) : β → ℝ := (exists_saddle G i y).choose

noncomputable def piS (i : Fin N) (y : Fin N → ℝ) : α → ℝ :=
  (exists_saddle G i y).choose_spec.2.choose

theorem rhoS_mem (i : Fin N) (y : Fin N → ℝ) : rhoS G i y ∈ simp' (G.B i) :=
  (exists_saddle G i y).choose_spec.1

theorem piS_mem (i : Fin N) (y : Fin N → ℝ) : piS G i y ∈ simp' (G.A i) :=
  (exists_saddle G i y).choose_spec.2.choose_spec.1

theorem saddle_spec (i : Fin N) (y : Fin N → ℝ) :
    ∀ ρ' ∈ simp' (G.B i), ∀ π' ∈ simp' (G.A i),
      payoff G i y (rhoS G i y) π' ≤ payoff G i y ρ' (piS G i y) :=
  (exists_saddle G i y).choose_spec.2.choose_spec.2

noncomputable def sval (i : Fin N) (y : Fin N → ℝ) : ℝ := payoff G i y (rhoS G i y) (piS G i y)

theorem payoff_sub (i : Fin N) (y y' : Fin N → ℝ) (ρ : β → ℝ) (π : α → ℝ) :
    payoff G i y ρ π - payoff G i y' ρ π =
      ∑ b, ρ b * ∑ a, π a * ∑ k, G.p i a b k * (y k - y' k) := by
  unfold payoff Mat
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_sub]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem sval_sub_le (μ : Fin N → ℝ) (c : ℝ)
    (hμ : ∀ i, ∀ a ∈ G.A i, ∀ b ∈ G.B i, ∑ j, G.p i a b j * μ j ≤ c * μ i)
    (i : Fin N) (y y' : Fin N → ℝ) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ k, |y k - y' k| ≤ D * μ k) :
    sval G i y - sval G i y' ≤ c * μ i * D := by
  have h1 : sval G i y ≤ payoff G i y (rhoS G i y') (piS G i y) :=
    saddle_spec G i y _ (rhoS_mem G i y') _ (piS_mem G i y)
  have h2 : payoff G i y' (rhoS G i y') (piS G i y) ≤ sval G i y' :=
    saddle_spec G i y' _ (rhoS_mem G i y') _ (piS_mem G i y)
  have h3 : payoff G i y (rhoS G i y') (piS G i y) - payoff G i y' (rhoS G i y') (piS G i y)
      ≤ c * μ i * D := by
    rw [payoff_sub]
    refine wavg_le _ _ (rhoS_mem G i y') _ _ fun b hb => ?_
    refine wavg_le _ _ (piS_mem G i y) _ _ fun a ha => ?_
    calc ∑ k, G.p i a b k * (y k - y' k) ≤ ∑ k, G.p i a b k * (D * μ k) := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hD k))
            (G.p_nonneg i a ha b hb k)
      _ = D * ∑ k, G.p i a b k * μ k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ ≤ D * (c * μ i) := by
          exact mul_le_mul_of_nonneg_left (hμ i a ha b hb) hD0
      _ = c * μ i * D := by ring
  unfold sval at *
  linarith

theorem exists_fixed (hA : Assumption621 G) : ∃ y : Fin N → ℝ, ∀ i, sval G i y = y i := by
  obtain ⟨μ, c, hμp, hc0, hc1, hμ⟩ := hA
  let U : (Fin N → ℝ) → (Fin N → ℝ) := fun u i => sval G i (fun k => μ k * u k) / μ i
  have hU : ∀ u v, dist (U u) (U v) ≤ c * dist u v := by
    intro u v
    refine (dist_pi_le_iff (mul_nonneg hc0 dist_nonneg)).2 fun i => ?_
    have hD : ∀ k, |μ k * u k - μ k * v k| ≤ dist u v * μ k := by
      intro k
      rw [← mul_sub, abs_mul, abs_of_pos (hμp k), mul_comm]
      exact mul_le_mul_of_nonneg_right (by rw [← Real.dist_eq]; exact dist_le_pi_dist u v k)
        (hμp k).le
    have hD' : ∀ k, |μ k * v k - μ k * u k| ≤ dist u v * μ k := by
      intro k; rw [abs_sub_comm]; exact hD k
    have e1 := sval_sub_le G μ c hμ i _ _ _ dist_nonneg hD
    have e2 := sval_sub_le G μ c hμ i _ _ _ dist_nonneg hD'
    rw [Real.dist_eq]
    simp only [U]
    rw [← sub_div, abs_div, abs_of_pos (hμp i), div_le_iff₀ (hμp i), abs_le]
    constructor <;> nlinarith
  have hK : ContractingWith (⟨c, hc0⟩ : NNReal) U := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    · exact NNReal.coe_lt_coe.mp (by exact hc1)
    · exact hU u v
  have hfix : U (ContractingWith.fixedPoint U hK) = ContractingWith.fixedPoint U hK :=
    ContractingWith.fixedPoint_isFixedPt (f := U) hK
  refine ⟨fun k => μ k * ContractingWith.fixedPoint U hK k, fun i => ?_⟩
  have := congrFun hfix i
  simp only [U] at this
  rw [div_eq_iff (hμp i).ne'] at this
  rw [this]; ring

theorem shapley_core (hA : Assumption621 G) :
    ∃ (y : Fin N → ℝ) (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ),
      IsDecisionRule1 G π ∧ IsDecisionRule2 G ρ ∧
      (∀ j, ∀ a ∈ G.A j, ∑ b, ρ j b * gfun G y j a b ≤ 0) ∧
      (∀ j, ∀ b ∈ G.B j, 0 ≤ ∑ a, π j a * gfun G y j a b) := by
  classical
  obtain ⟨y, hy⟩ := exists_fixed G hA
  refine ⟨y, fun j => piS G j y, fun j => rhoS G j y, fun j => piS_mem G j y,
    fun j => rhoS_mem G j y, ?_, ?_⟩
  · intro j a ha
    have h := saddle_spec G j y _ (rhoS_mem G j y) _ (single_mem_simp' _ a ha)
    have e : payoff G j y (rhoS G j y) (Pi.single a 1) = ∑ b, rhoS G j y b * Mat G j y a b := by
      unfold payoff
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      simp [Pi.single_apply]
    have e2 : ∑ b, rhoS G j y b * gfun G y j a b =
        ∑ b, rhoS G j y b * Mat G j y a b - ∑ b, rhoS G j y b * y j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold gfun Mat; ring
    rw [e2, wavg_const _ _ (rhoS_mem G j y)]
    have := hy j
    unfold sval at this
    linarith
  · intro j b hb
    have h := saddle_spec G j y _ (single_mem_simp' _ b hb) _ (piS_mem G j y)
    have e : payoff G j y (Pi.single b 1) (piS G j y) = ∑ a, piS G j y a * Mat G j y a b := by
      unfold payoff
      simp [Pi.single_apply]
    have e2 : ∑ a, piS G j y a * gfun G y j a b =
        ∑ a, piS G j y a * Mat G j y a b - ∑ a, piS G j y a * y j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold gfun Mat; ring
    rw [e2, wavg_const _ _ (piS_mem G j y)]
    have := hy j
    unfold sval at this
    linarith

theorem shapley_full (hA : Assumption621 G) :
    ∃ (y : Fin N → ℝ) (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (hπ : IsDecisionRule1 G π)
      (hρ : IsDecisionRule2 G ρ),
      IsOptimalPair G (stationary1 G π hπ) (stationary2 G ρ hρ) ∧
      (∀ i, y i = totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) i) ∧
      (∀ j, ∀ a ∈ G.A j, ∑ b, ρ j b * gfun G y j a b ≤ 0) := by
  obtain ⟨y, π, ρ, hπ, hρ, h1, h2⟩ := shapley_core G hA
  have up := fun R1 i => total_le_stat2 G hA ρ hρ y h1 R1 i
  have lo := fun R2 i => le_total_stat1 G hA π hπ y h2 R2 i
  have eq : ∀ i, y i = totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) i :=
    fun i => le_antisymm (lo _ i) (up _ i)
  refine ⟨y, π, ρ, hπ, hρ, fun R1 R2 i => ⟨?_, ?_⟩, eq, h1⟩
  · rw [← eq i]; exact up R1 i
  · rw [← eq i]; exact lo R2 i

theorem shapley_stationary_optimal_core (G : Game N α β) (hA : Assumption621 G) :
    ∃ (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (hπ : IsDecisionRule1 G π)
      (hρ : IsDecisionRule2 G ρ), IsOptimalPair G (stationary1 G π hπ) (stationary2 G ρ hρ) := by
  obtain ⟨y, π, ρ, hπ, hρ, h, -⟩ := shapley_full G hA
  exact ⟨π, ρ, hπ, hρ, h⟩

theorem gfun_avg_eq (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ) (y : Fin N → ℝ)
    (i : Fin N) (a : α) :
    ∑ b, ρ i b * gfun G y i a b = rho_r G ρ i a + ∑ j, rho_p G ρ i a j * y j - y i := by
  have h1 : ∑ b, ρ i b * ∑ k, G.p i a b k * y k = ∑ k, rho_p G ρ i a k * y k := by
    unfold rho_p
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [sum_comm2]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 : ∑ b, ρ i b * y i = y i := by rw [← Finset.sum_mul, (hρ i).2.2, one_mul]
  have e : ∀ b, ρ i b * gfun G y i a b =
      G.r i a b * ρ i b + ρ i b * (∑ k, G.p i a b k * y k) - ρ i b * y i := by
    intro b; unfold gfun; ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  rfl

theorem value_smallest_superharmonic_core (G : Game N α β) (hA : Assumption621 G) :
    ∃ y : Fin N → ℝ, IsValueOfGame G y ∧
      IsLeast {y' : Fin N → ℝ | TMGSuperharmonic G y'} y := by
  obtain ⟨y, π, ρ, hπ, hρ, hopt, heq, h1⟩ := shapley_full G hA
  obtain ⟨-, -, -, -, -, h2⟩ := shapley_core G hA
  refine ⟨y, ⟨_, _, hopt, heq⟩, ⟨ρ, hρ, fun i a ha => ?_⟩, fun y' hy' => ?_⟩
  · have := h1 i a ha; rw [gfun_avg_eq G ρ hρ] at this; linarith
  · obtain ⟨ρ', hρ', hs⟩ := hy'
    intro i
    have hc : ∀ j, ∀ a ∈ G.A j, ∑ b, ρ' j b * gfun G y' j a b ≤ 0 := by
      intro j a ha; rw [gfun_avg_eq G ρ' hρ']; have := hs j a ha; linarith
    have u := total_le_stat2 G hA ρ' hρ' y' hc (stationary1 G π hπ) i
    have l : y i ≤ totalReward G (stationary1 G π hπ) (stationary2 G ρ' hρ') i :=
      (hopt (stationary1 G π hπ) (stationary2 G ρ' hρ') i).2 |>.trans' (le_of_eq (heq i))
    linarith

section MatrixPart

open scoped Matrix

theorem vecMul_one_sub (P : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (k : Fin N) :
    (v ᵥ* (1 - P)) k = v k - ∑ j, v j * P j k := by
  simp [Matrix.vecMul, dotProduct, Matrix.sub_apply, Matrix.one_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem left_kernel_zero (P : Matrix (Fin N) (Fin N) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (μ : Fin N → ℝ) (c : ℝ) (hμp : ∀ i, 0 < μ i) (hc1 : c < 1)
    (hPμ : ∀ i, ∑ j, P i j * μ j ≤ c * μ i)
    (w : Fin N → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw : ∀ k, w k ≤ ∑ j, w j * P j k) : w = 0 := by
  have hS : ∑ k, w k * μ k ≤ c * ∑ k, w k * μ k :=
    calc ∑ k, w k * μ k ≤ ∑ k, (∑ j, w j * P j k) * μ k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hw k) (hμp k).le
      _ = ∑ j, w j * ∑ k, P j k * μ k := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [sum_comm2]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ ∑ j, w j * (c * μ j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hPμ j) (hw0 j)
      _ = c * ∑ k, w k * μ k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ w k * μ k := fun k _ => mul_nonneg (hw0 k) (hμp k).le
  have hS0 : 0 ≤ ∑ k, w k * μ k := Finset.sum_nonneg hnn
  have hz : ∑ k, w k * μ k = 0 := by nlinarith
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hz
  funext k
  have := hz k (Finset.mem_univ k)
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (hμp k).ne'

theorem one_sub_isUnit (P : Matrix (Fin N) (Fin N) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (μ : Fin N → ℝ) (c : ℝ) (hμp : ∀ i, 0 < μ i) (hc1 : c < 1)
    (hPμ : ∀ i, ∑ j, P i j * μ j ≤ c * μ i) : IsUnit (1 - P).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  apply hv0
  have hk : ∀ k, v k = ∑ j, v j * P j k := by
    intro k
    have := congrFun hv k
    rw [vecMul_one_sub] at this
    simp only [Pi.zero_apply] at this
    linarith
  have habs := left_kernel_zero P hP μ c hμp hc1 hPμ (fun k => |v k|) (fun k => abs_nonneg _)
    (fun k => by
      rw [hk k]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (hP j k)])
  funext k
  have := congrFun habs k
  simpa using this

theorem s_vecMul (P : Matrix (Fin N) (Fin N) ℝ) (hdet : IsUnit (1 - P).det) (β' : Fin N → ℝ) :
    (β' ᵥ* (1 - P)⁻¹) ᵥ* (1 - P) = β' := by
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]

theorem s_ge (P : Matrix (Fin N) (Fin N) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (μ : Fin N → ℝ) (c : ℝ) (hμp : ∀ i, 0 < μ i) (hc1 : c < 1)
    (hPμ : ∀ i, ∑ j, P i j * μ j ≤ c * μ i) (β' : Fin N → ℝ) (hβ : ∀ j, 0 ≤ β' j) (k : Fin N) :
    β' k ≤ (β' ᵥ* (1 - P)⁻¹) k := by
  set s := β' ᵥ* (1 - P)⁻¹ with hs_def
  have hdet := one_sub_isUnit P hP μ c hμp hc1 hPμ
  have hs : ∀ k, s k - ∑ j, s j * P j k = β' k := by
    intro k; rw [← vecMul_one_sub, hs_def, s_vecMul P hdet]
  have hw := left_kernel_zero P hP μ c hμp hc1 hPμ (fun k => max (-s k) 0)
    (fun k => le_max_right _ _) (fun k => by
      have hsum : ∑ j, (-s j) * P j k ≤ ∑ j, max (-s j) 0 * P j k :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hP j k)
      have hsum0 : 0 ≤ ∑ j, max (-s j) 0 * P j k :=
        Finset.sum_nonneg fun j _ => mul_nonneg (le_max_right _ _) (hP j k)
      have := hs k
      have hneg : ∑ j, (-s j) * P j k = -∑ j, s j * P j k := by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      have := hβ k
      apply max_le <;> linarith)
  have hsn : ∀ j, 0 ≤ s j := by
    intro j
    have := congrFun hw j
    simp only [Pi.zero_apply] at this
    have := le_max_left (-s j) 0
    linarith
  have := hs k
  have : 0 ≤ ∑ j, s j * P j k := Finset.sum_nonneg fun j _ => mul_nonneg (hsn j) (hP j k)
  linarith

end MatrixPart

section SingleController

open scoped Matrix

theorem b0_mem (i : Fin N) : (G.B_nonempty i).choose ∈ G.B i := (G.B_nonempty i).choose_spec

theorem ctrlP_nonneg (i : Fin N) (a : α) (ha : a ∈ G.A i) (j : Fin N) : 0 ≤ ctrlP G i a j :=
  G.p_nonneg i a ha _ (b0_mem G i) j

theorem ctrlP_eq (hC : Assumption622 G) (i : Fin N) (a : α) (ha : a ∈ G.A i) (b : β)
    (hb : b ∈ G.B i) (j : Fin N) : G.p i a b j = ctrlP G i a j :=
  hC i a ha b hb _ (b0_mem G i) j

theorem sum_univ_eq_sum_A (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (j : Fin N)
    (F : α → ℝ) : ∑ a, π j a * F a = ∑ a ∈ G.A j, π j a * F a :=
  (Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => by rw [(hπ j).2.1 a ha]; ring)).symm

theorem sum_A_pi (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (j : Fin N) :
    ∑ a ∈ G.A j, π j a = 1 := by
  have := sum_univ_eq_sum_A G π hπ j (fun _ => 1)
  simp only [mul_one] at this
  rw [← this, (hπ j).2.2]

theorem transMat_nonneg (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (i j : Fin N) :
    0 ≤ transMat G π i j :=
  Finset.sum_nonneg fun a ha => mul_nonneg (ctrlP_nonneg G i a ha j) ((hπ i).1 a)

theorem transMat_mu (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (μ : Fin N → ℝ) (c : ℝ)
    (hμ : ∀ i, ∀ a ∈ G.A i, ∀ b ∈ G.B i, ∑ j, G.p i a b j * μ j ≤ c * μ i) (i : Fin N) :
    ∑ j, transMat G π i j * μ j ≤ c * μ i := by
  unfold transMat
  calc ∑ j, (∑ a ∈ G.A i, ctrlP G i a j * π i a) * μ j
        = ∑ a ∈ G.A i, π i a * ∑ j, ctrlP G i a j * μ j := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∑ a ∈ G.A i, π i a * (c * μ i) :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hμ i a ha _ (b0_mem G i))
          ((hπ i).1 a)
    _ = c * μ i := by rw [← Finset.sum_mul, sum_A_pi G π hπ i, one_mul]

/-- `s(π) = β^T (I - P(π))^{-1}`. -/
noncomputable def sv (β' : Fin N → ℝ) (π : Fin N → α → ℝ) : Fin N → ℝ :=
  β' ᵥ* (1 - transMat G π)⁻¹

theorem occ_eq (β' : Fin N → ℝ) (π : Fin N → α → ℝ) (i : Fin N) (a : α) :
    occ G β' π i a = sv G β' π i * π i a := rfl

theorem sum_occ (β' : Fin N → ℝ) (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (i : Fin N) :
    ∑ a ∈ G.A i, occ G β' π i a = sv G β' π i := by
  simp only [occ_eq, ← Finset.mul_sum, sum_A_pi G π hπ i, mul_one]

theorem pi_avg_p (hC : Assumption622 G) (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π)
    (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ) (y : Fin N → ℝ) (j : Fin N) :
    ∑ a, ∑ b, π j a * ρ j b * ∑ k, G.p j a b k * y k = ∑ k, transMat G π j k * y k := by
  have h1 : ∀ a ∈ G.A j, ∑ b, ρ j b * ∑ k, G.p j a b k * y k = ∑ k, ctrlP G j a k * y k := by
    intro a ha
    have hρm : ρ j ∈ simp' (G.B j) := hρ j
    apply le_antisymm
    · exact wavg_le _ _ hρm _ _ fun b hb => le_of_eq (by simp only [ctrlP_eq G hC j a ha b hb])
    · exact wavg_ge _ _ hρm _ _ fun b hb => le_of_eq (by simp only [ctrlP_eq G hC j a ha b hb])
  calc ∑ a, ∑ b, π j a * ρ j b * ∑ k, G.p j a b k * y k
      = ∑ a, π j a * ∑ b, ρ j b * ∑ k, G.p j a b k * y k := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    _ = ∑ a ∈ G.A j, π j a * ∑ b, ρ j b * ∑ k, G.p j a b k * y k := sum_univ_eq_sum_A G π hπ j _
    _ = ∑ a ∈ G.A j, π j a * ∑ k, ctrlP G j a k * y k :=
        Finset.sum_congr rfl fun a ha => by rw [h1 a ha]
    _ = ∑ k, transMat G π j k * y k := by
        unfold transMat
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
        ring

def rr (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (j : Fin N) : ℝ :=
  ∑ a, ∑ b, π j a * ρ j b * G.r j a b

theorem rr_eq (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (j : Fin N) :
    rr G π ρ j = ∑ b, ρ j b * pi_r G π j b := by
  unfold rr pi_r
  rw [sum_comm2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring

theorem total_stat_formula (hA : Assumption621 G) (hC : Assumption622 G)
    (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (ρ : Fin N → β → ℝ)
    (hρ : IsDecisionRule2 G ρ) (v : Fin N → ℝ)
    (hv : ∀ j, v j = rr G π ρ j + ∑ k, transMat G π j k * v k) (i : Fin N) :
    totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) i = v i := by
  have hG : ∀ j, Gst G π ρ v j = 0 := by
    intro j
    unfold Gst gfun
    have e : ∀ a b, π j a * ρ j b * (G.r j a b + ∑ k, G.p j a b k * v k - v j) =
        π j a * ρ j b * G.r j a b + π j a * ρ j b * ∑ k, G.p j a b k * v k -
          π j a * (ρ j b * v j) := by intro a b; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [pi_avg_p G hC π hπ ρ hρ v j]
    have h2 : ∑ a, ∑ b, π j a * (ρ j b * v j) = v j := by
      simp only [← Finset.mul_sum]
      rw [wavg_const _ _ (hρ j), wavg_const _ _ (hπ j)]
    rw [h2]
    have := hv j
    unfold rr at this
    linarith
  have h1 := total_le_stat12 G hA π hπ ρ hρ v 0 i (fun j => (hG j).le) (hG i).le
  have h2 := le_total_stat12 G hA π hπ ρ hρ v i (fun j => (hG j).ge)
  linarith

theorem weighted_total (hA : Assumption621 G) (hC : Assumption622 G)
    (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) (ρ : Fin N → β → ℝ)
    (hρ : IsDecisionRule2 G ρ) (β' : Fin N → ℝ) :
    ∑ j, β' j * totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) j =
      ∑ i, sv G β' π i * ∑ b, ρ i b * pi_r G π i b := by
  obtain ⟨μ, c, hμp, hc0, hc1, hμ⟩ := hA
  have hdet := one_sub_isUnit (transMat G π) (transMat_nonneg G π hπ) μ c hμp hc1
    (transMat_mu G π hπ μ c hμ)
  set M := 1 - transMat G π
  set v := M⁻¹ *ᵥ (rr G π ρ)
  have hMv : M *ᵥ v = rr G π ρ := by
    simp only [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hv : ∀ j, v j = rr G π ρ j + ∑ k, transMat G π j k * v k := by
    intro j
    have := congrFun hMv j
    simp only [M, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.mulVec,
      dotProduct] at this
    simp only [Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    linarith
  have ht := total_stat_formula G ⟨μ, c, hμp, hc0, hc1, hμ⟩ hC π hπ ρ hρ v hv
  simp only [ht]
  have hs : sv G β' π ᵥ* M = β' := s_vecMul _ hdet β'
  calc ∑ j, β' j * v j = β' ⬝ᵥ v := rfl
    _ = (sv G β' π ᵥ* M) ⬝ᵥ v := by rw [hs]
    _ = sv G β' π ⬝ᵥ (M *ᵥ v) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = _ := by
        rw [hMv]
        simp only [dotProduct, rr_eq]

end SingleController

section Final

open scoped Matrix

theorem occ_feasible_core (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) :
    LP622Feasible G β' (occ G β' π) (zval G β' π) ∧
      IsLeast
        {c : ℝ | ∃ (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ),
          c = ∑ j, β' j * totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) j}
        (∑ i, zval G β' π i) := by
  classical
  have hA' := hA
  obtain ⟨μ, c, hμp, hc0, hc1, hμ⟩ := hA
  have hdet := one_sub_isUnit (transMat G π) (transMat_nonneg G π hπ) μ c hμp hc1
    (transMat_mu G π hπ μ c hμ)
  have hs_ge : ∀ k, β' k ≤ sv G β' π k := s_ge _ (transMat_nonneg G π hπ) μ c hμp hc1
    (transMat_mu G π hπ μ c hμ) β' (fun j => (hβ j).le)
  have hs_nn : ∀ k, 0 ≤ sv G β' π k := fun k => (hβ k).le.trans (hs_ge k)
  have hsM : sv G β' π ᵥ* (1 - transMat G π) = β' := s_vecMul _ hdet β'
  have hz_eq : ∀ i, zval G β' π i =
      (G.B i).inf' (G.B_nonempty i) (fun b => pi_r G π i b * sv G β' π i) := by
    intro i; unfold zval; simp only [sum_occ G β' π hπ i]
  have hz_le : ∀ i, ∀ b ∈ G.B i, zval G β' π i ≤ pi_r G π i b * sv G β' π i := by
    intro i b hb; rw [hz_eq]; exact Finset.inf'_le _ hb
  refine ⟨⟨fun j => ?_, fun i b hb => ?_, fun i a ha => ?_, fun i a ha => ?_⟩, ?_, ?_⟩
  · have := congrFun hsM j
    rw [vecMul_one_sub] at this
    rw [← this]
    have e1 : ∀ i, ∑ a ∈ G.A i, ((if i = j then 1 else 0) - ctrlP G i a j) * occ G β' π i a =
        sv G β' π i * (if i = j then 1 else 0) - sv G β' π i * transMat G π i j := by
      intro i
      have e : ∀ a, ((if i = j then (1:ℝ) else 0) - ctrlP G i a j) * occ G β' π i a =
          sv G β' π i * (if i = j then 1 else 0) * π i a -
            sv G β' π i * (ctrlP G i a j * π i a) := by
        intro a; rw [occ_eq]; ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_A_pi G π hπ i, mul_one]
      rfl
    simp only [e1, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  · have := hz_le i b hb
    have e : ∑ a ∈ G.A i, G.r i a b * occ G β' π i a = pi_r G π i b * sv G β' π i := by
      calc ∑ a ∈ G.A i, G.r i a b * occ G β' π i a
          = ∑ a ∈ G.A i, π i a * (G.r i a b * sv G β' π i) :=
            Finset.sum_congr rfl fun a _ => by rw [occ_eq]; ring
        _ = ∑ a, π i a * (G.r i a b * sv G β' π i) := (sum_univ_eq_sum_A G π hπ i _).symm
        _ = pi_r G π i b * sv G β' π i := by
            unfold pi_r; rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_; ring
    linarith
  · rw [occ_eq]; exact mul_nonneg (hs_nn i) ((hπ i).1 a)
  · rw [occ_eq, (hπ i).2.1 a ha, mul_zero]
  · have hb : ∀ i, ∃ b ∈ G.B i, ∀ b' ∈ G.B i, pi_r G π i b ≤ pi_r G π i b' :=
      fun i => Finset.exists_min_image _ _ (G.B_nonempty i)
    choose bs hbs hbmin using hb
    let ρ : Fin N → β → ℝ := fun i => Pi.single (bs i) 1
    have hρ : IsDecisionRule2 G ρ := fun i => single_mem_simp' _ _ (hbs i)
    refine ⟨ρ, hρ, ?_⟩
    rw [weighted_total G hA' hC π hπ ρ hρ β']
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : ∑ b, ρ i b * pi_r G π i b = pi_r G π i (bs i) := by
      simp [ρ, Pi.single_apply]
    rw [e]
    apply le_antisymm
    · rw [mul_comm]; exact hz_le i _ (hbs i)
    · rw [hz_eq, mul_comm]
      exact Finset.le_inf' _ _ fun b hb =>
        mul_le_mul_of_nonneg_right (hbmin i b hb) (hs_nn i)
  · rintro x ⟨ρ, hρ, rfl⟩
    rw [weighted_total G hA' hC π hπ ρ hρ β']
    refine Finset.sum_le_sum fun i _ => ?_
    have := wavg_ge _ _ (hρ i) (fun b => pi_r G π i b * sv G β' π i) _ (hz_le i)
    calc zval G β' π i ≤ ∑ b, ρ i b * (pi_r G π i b * sv G β' π i) := this
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring

theorem feasible_eq_occ_core (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (x : Fin N → α → ℝ) (z : Fin N → ℝ) (hxz : LP622Feasible G β' x z) :
    IsDecisionRule1 G (piOfX G x) ∧ x = occ G β' (piOfX G x) ∧ z ≤ zval G β' (piOfX G x) := by
  obtain ⟨μ, c, hμp, hc0, hc1, hμ⟩ := hA
  obtain ⟨hflow, hz, hx0, hxout⟩ := hxz
  set s : Fin N → ℝ := fun i => ∑ a ∈ G.A i, x i a with hs_def
  have hsuniv : ∀ i, ∑ a, x i a = s i := fun i =>
    (Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hxout i a ha)).symm
  have hflow' : ∀ j, s j - ∑ i, ∑ a ∈ G.A i, ctrlP G i a j * x i a = β' j := by
    intro j
    rw [← hflow j]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    congr 1
    rw [Fintype.sum_eq_single j (fun i hij => by simp [hij])]
    simp [s]
  have hspos : ∀ j, 0 < s j := by
    intro j
    have := hflow' j
    have : 0 ≤ ∑ i, ∑ a ∈ G.A i, ctrlP G i a j * x i a :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a ha =>
        mul_nonneg (ctrlP_nonneg G i a ha j) (hx0 i a ha)
    have := hβ j
    linarith
  have hpi : ∀ i a, piOfX G x i a = x i a / s i := fun i a => rfl
  have hπ : IsDecisionRule1 G (piOfX G x) := by
    intro i
    refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
    · rw [hpi]
      by_cases ha : a ∈ G.A i
      · exact div_nonneg (hx0 i a ha) (hspos i).le
      · rw [hxout i a ha, zero_div]
    · rw [hpi, hxout i a ha, zero_div]
    · simp only [hpi, ← Finset.sum_div, hsuniv]
      exact div_self (hspos i).ne'
  have hdet := one_sub_isUnit (transMat G (piOfX G x)) (transMat_nonneg G _ hπ) μ c hμp hc1
    (transMat_mu G _ hπ μ c hμ)
  have hsM : s ᵥ* (1 - transMat G (piOfX G x)) = β' := by
    funext k
    rw [vecMul_one_sub, ← hflow' k]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold transMat
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hpi]
    field_simp [(hspos i).ne']
  have hsv : sv G β' (piOfX G x) = s := by
    unfold sv
    rw [← hsM, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
  have hxocc : x = occ G β' (piOfX G x) := by
    funext i a
    rw [occ_eq, hsv, hpi]
    field_simp [(hspos i).ne']
  refine ⟨hπ, hxocc, fun i => ?_⟩
  unfold zval
  rw [sum_occ G β' _ hπ i, hsv]
  refine Finset.le_inf' _ _ fun b hb => ?_
  have e : pi_r G (piOfX G x) i b * s i = ∑ a ∈ G.A i, G.r i a b * x i a := by
    unfold pi_r
    rw [Finset.sum_mul]
    rw [← Finset.sum_subset (Finset.subset_univ (G.A i)) (fun a _ ha => by
      rw [hpi, hxout i a ha]; ring)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hpi]
    field_simp [(hspos i).ne']
  rw [e]
  have := hz i b hb
  linarith

theorem gfun_avg_ctrl (hC : Assumption622 G) (y : Fin N → ℝ) (ρ : Fin N → β → ℝ)
    (hρ : IsDecisionRule2 G ρ) (j : Fin N) (a : α) (ha : a ∈ G.A j) :
    ∑ b, ρ j b * gfun G y j a b =
      (∑ b ∈ G.B j, G.r j a b * ρ j b) + ∑ k, ctrlP G j a k * y k - y j := by
  have hρm : ρ j ∈ simp' (G.B j) := hρ j
  have h1 : ∑ b, ρ j b * ∑ k, G.p j a b k * y k = ∑ k, ctrlP G j a k * y k := by
    apply le_antisymm
    · exact wavg_le _ _ hρm _ _ fun b hb => le_of_eq (by simp only [ctrlP_eq G hC j a ha b hb])
    · exact wavg_ge _ _ hρm _ _ fun b hb => le_of_eq (by simp only [ctrlP_eq G hC j a ha b hb])
  have h2 : ∑ b, ρ j b * y j = y j := wavg_const _ _ hρm _
  have h3 : ∑ b, ρ j b * G.r j a b = ∑ b ∈ G.B j, G.r j a b * ρ j b := by
    rw [← Finset.sum_subset (Finset.subset_univ (G.B j)) (fun b _ hb => by
      rw [(hρ j).2.1 b hb]; ring)]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e : ∀ b, ρ j b * gfun G y j a b =
      ρ j b * G.r j a b + ρ j b * (∑ k, G.p j a b k * y k) - ρ j b * y j := by
    intro b; unfold gfun; ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2, h3]

theorem lp_lhs (y : Fin N → ℝ) (j : Fin N) (a : α) :
    ∑ k, ((if j = k then 1 else 0) - ctrlP G j a k) * y k = y j - ∑ k, ctrlP G j a k * y k := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem Gst_eq (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (y : Fin N → ℝ) (j : Fin N) :
    Gst G π ρ y j = ∑ a, π j a * ∑ b, ρ j b * gfun G y j a b := by
  unfold Gst
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring

theorem lp_pair_value_optimal_core (G : Game N α β) (hA : Assumption621 G)
    (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (ys : Fin N → ℝ) (ρs : Fin N → β → ℝ) (h1 : LP621Optimal G β' ys ρs)
    (xs : Fin N → α → ℝ) (zs : Fin N → ℝ) (h2 : LP622Optimal G β' xs zs) :
    ∃ (hπ : IsDecisionRule1 G (piOfX G xs)) (hρ : IsDecisionRule2 G ρs),
      IsOptimalPair G (stationary1 G (piOfX G xs) hπ) (stationary2 G ρs hρ) ∧
        ∀ i, ys i = totalReward G (stationary1 G (piOfX G xs) hπ) (stationary2 G ρs hρ) i := by
  classical
  obtain ⟨hπ, hxocc, hzle⟩ := feasible_eq_occ_core G hA hC β' hβ xs zs h2.1
  obtain ⟨hf1, hf2, hf3, hf4⟩ := h1.1
  have hρ : IsDecisionRule2 G ρs := by
    intro i
    refine ⟨fun b => ?_, hf4 i, ?_⟩
    · by_cases hb : b ∈ G.B i
      · exact hf3 i b hb
      · rw [hf4 i b hb]
    · rw [← hf2 i]
      exact (Finset.sum_subset (Finset.subset_univ _) (fun b _ hb => hf4 i b hb)).symm
  have hcert_s : ∀ j, ∀ a ∈ G.A j, ∑ b, ρs j b * gfun G ys j a b ≤ 0 := by
    intro j a ha
    rw [gfun_avg_ctrl G hC ys ρs hρ j a ha]
    have := hf1 j a ha
    rw [lp_lhs] at this
    linarith
  have U1 := fun R1 i => total_le_stat2 G hA ρs hρ ys hcert_s R1 i
  obtain ⟨y', π', ρ', hπ', hρ', c1, c2⟩ := shapley_core G hA
  have hfeas' : LP621Feasible G y' ρ' := by
    refine ⟨fun i a ha => ?_, fun i => ?_, fun i b _ => (hρ' i).1 b, fun i b hb => (hρ' i).2.1 b hb⟩
    · have := c1 i a ha
      rw [gfun_avg_ctrl G hC y' ρ' hρ' i a ha] at this
      rw [lp_lhs]
      linarith
    · rw [Finset.sum_subset (Finset.subset_univ _) (fun b _ hb => (hρ' i).2.1 b hb)]
      exact (hρ' i).2.2
  have hle1 : ∑ j, β' j * ys j ≤ ∑ j, β' j * y' j := h1.2 _ _ hfeas'
  obtain ⟨hfeasπ', hmemπ', -⟩ := occ_feasible_core G hA hC β' hβ π' hπ'
  have hle2 : ∑ j, β' j * y' j ≤ ∑ i, zval G β' π' i := by
    obtain ⟨ρ, hρ0, heq⟩ := hmemπ'
    rw [heq]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (le_total_stat1 G hA π' hπ' y' c2 _ j) (hβ j).le
  have hle3 : ∑ i, zval G β' π' i ≤ ∑ i, zs i := h2.2 _ _ hfeasπ'
  have hcert_π : ∀ j, ∀ b ∈ G.B j, 0 ≤ ∑ a, piOfX G xs j a * gfun G ys j a b := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨j0, b0, hb0, hlt⟩ := hneg
    let ρ2 : Fin N → β → ℝ := Function.update ρs j0 (Pi.single b0 1)
    have hρ2 : IsDecisionRule2 G ρ2 := by
      intro i
      by_cases hi : i = j0
      · subst hi
        have : ρ2 i = Pi.single b0 1 := by simp [ρ2]
        rw [this]; exact single_mem_simp' _ _ hb0
      · have : ρ2 i = ρs i := by simp [ρ2, hi]
        rw [this]; exact hρ i
    have hG : ∀ j, Gst G (piOfX G xs) ρ2 ys j ≤ 0 := by
      intro j
      rw [Gst_eq]
      by_cases hj : j = j0
      · subst hj
        have : ρ2 j = Pi.single b0 1 := by simp [ρ2]
        rw [this]
        have e : ∀ a, ∑ b, (Pi.single b0 1 : β → ℝ) b * gfun G ys j a b = gfun G ys j a b0 := by
          intro a; simp [Pi.single_apply]
        simp only [e]; exact hlt.le
      · have : ρ2 j = ρs j := by simp [ρ2, hj]
        rw [this, sum_univ_eq_sum_A G _ hπ j]
        exact Finset.sum_nonpos fun a ha =>
          mul_nonpos_of_nonneg_of_nonpos ((hπ j).1 a) (hcert_s j a ha)
    have hG0 : Gst G (piOfX G xs) ρ2 ys j0 < 0 := by
      rw [Gst_eq]
      have : ρ2 j0 = Pi.single b0 1 := by simp [ρ2]
      rw [this]
      have e : ∀ a, ∑ b, (Pi.single b0 1 : β → ℝ) b * gfun G ys j0 a b = gfun G ys j0 a b0 := by
        intro a; simp [Pi.single_apply]
      simp only [e]; exact hlt
    have ht : ∀ i, totalReward G (stationary1 G _ hπ) (stationary2 G ρ2 hρ2) i ≤
        ys i + Gst G (piOfX G xs) ρ2 ys i :=
      fun i => total_le_stat12 G hA _ hπ ρ2 hρ2 ys _ i hG le_rfl
    have hsum : ∑ i, β' i * totalReward G (stationary1 G _ hπ) (stationary2 G ρ2 hρ2) i ≤
        ∑ i, β' i * ys i + β' j0 * Gst G (piOfX G xs) ρ2 ys j0 := by
      calc _ ≤ ∑ i, (β' i * ys i + β' i * Gst G (piOfX G xs) ρ2 ys i) :=
            Finset.sum_le_sum fun i _ => by
              rw [← mul_add]; exact mul_le_mul_of_nonneg_left (ht i) (hβ i).le
        _ = ∑ i, β' i * ys i + ∑ i, β' i * Gst G (piOfX G xs) ρ2 ys i := Finset.sum_add_distrib
        _ ≤ _ := by
            refine add_le_add le_rfl ?_
            calc ∑ i, β' i * Gst G (piOfX G xs) ρ2 ys i ≤
                ∑ i, (if i = j0 then β' j0 * Gst G (piOfX G xs) ρ2 ys j0 else 0) :=
                  Finset.sum_le_sum fun i _ => by
                    split_ifs with hi
                    · rw [hi]
                    · exact mul_nonpos_of_nonneg_of_nonpos (hβ i).le (hG i)
              _ = _ := by simp
    obtain ⟨-, -, hlow⟩ := occ_feasible_core G hA hC β' hβ (piOfX G xs) hπ
    have hl := hlow ⟨ρ2, hρ2, rfl⟩
    have hzs : ∑ i, zs i ≤ ∑ i, zval G β' (piOfX G xs) i := Finset.sum_le_sum fun i _ => hzle i
    have := mul_neg_of_pos_of_neg (hβ j0) hG0
    linarith
  have L1 := fun R2 i => le_total_stat1 G hA (piOfX G xs) hπ ys hcert_π R2 i
  have heq : ∀ i, ys i = totalReward G (stationary1 G (piOfX G xs) hπ) (stationary2 G ρs hρ) i :=
    fun i => le_antisymm (L1 _ i) (U1 _ i)
  refine ⟨hπ, hρ, fun R1 R2 i => ⟨?_, ?_⟩, heq⟩
  · rw [← heq i]; exact U1 R1 i
  · rw [← heq i]; exact L1 R2 i

end Final

end KallenbergLP.Games

open KallenbergLP.Games


theorem solution {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (x : Fin N → α → ℝ) (z : Fin N → ℝ) (hxz : LP622Feasible G β' x z) :
    IsDecisionRule1 G (piOfX G x) ∧ x = occ G β' (piOfX G x) ∧ z ≤ zval G β' (piOfX G x) := by
  exact feasible_eq_occ_core G hA hC β' hβ x z hxz
