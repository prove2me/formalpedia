-- Prove2me | solution 1 for KallenbergLP.Games.shapley_stationary_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:45:46.674115+00:00
-- url     : https://prove2.me/submissions/01872161-2da1-46ee-908b-4631f085e96c

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

end KallenbergLP.Games

open KallenbergLP.Games


theorem solution {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) :
    ∃ (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (hπ : IsDecisionRule1 G π)
      (hρ : IsDecisionRule2 G ρ), IsOptimalPair G (stationary1 G π hπ) (stationary2 G ρ hρ) := by
  exact shapley_stationary_optimal_core G hA
