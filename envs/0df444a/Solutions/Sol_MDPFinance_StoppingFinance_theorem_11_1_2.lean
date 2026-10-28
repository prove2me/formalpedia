-- Prove2me | solution 1 for MDPFinance.StoppingFinance.theorem_11_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:31:54.327967+00:00
-- url     : https://prove2.me/submissions/30470a01-7fe9-4c6e-873d-cd5483f1a1d8

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_BinomialModel

open MeasureTheory

namespace S100Put
open MDPFinance.StoppingFinance

variable (M : BinomialModel)

/-! ### Part 1: deterministic properties of `J` -/

lemma u_pos : 0 < M.u := lt_trans M.d_pos M.d_lt_u

lemma J_succ (n : ℕ) (x : ℝ) : M.J (n + 1) x =
    max (M.payoff x) (M.beta * (M.q * M.J n (x * M.u) + (1 - M.q) * M.J n (x * M.d))) := rfl

lemma J_zero (x : ℝ) : M.J 0 x = max (M.K - x) 0 := rfl

lemma payoff_cont : Continuous M.payoff :=
  (continuous_const.sub continuous_id).max continuous_const

lemma J_cont : ∀ n, Continuous (M.J n)
  | 0 => payoff_cont M
  | n + 1 => by
    have h := J_cont n
    have : M.J (n + 1) = fun x =>
        max (M.payoff x) (M.beta * (M.q * M.J n (x * M.u) + (1 - M.q) * M.J n (x * M.d))) := rfl
    rw [this]
    exact (payoff_cont M).max (continuous_const.mul
      ((continuous_const.mul (h.comp (continuous_id.mul continuous_const))).add
        (continuous_const.mul (h.comp (continuous_id.mul continuous_const)))))

lemma payoff_nonneg (x : ℝ) : 0 ≤ M.payoff x := le_max_right _ _

lemma sub_le_payoff (x : ℝ) : M.K - x ≤ M.payoff x := le_max_left _ _

lemma J_ge_payoff : ∀ n x, M.payoff x ≤ M.J n x
  | 0, _ => le_rfl
  | n + 1, x => by rw [J_succ]; exact le_max_left _ _

lemma J_nonneg (n : ℕ) (x : ℝ) : 0 ≤ M.J n x := (payoff_nonneg M x).trans (J_ge_payoff M n x)

lemma J_ge_sub (n : ℕ) (x : ℝ) : M.K - x ≤ M.J n x := (sub_le_payoff M x).trans (J_ge_payoff M n x)

lemma max_add' (a b c : ℝ) : max a b + c = max (a + c) (b + c) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

lemma J_add_mono : ∀ n, ∀ x y : ℝ, x ≤ y → M.J n x + x ≤ M.J n y + y
  | 0, x, y, hxy => by
    rw [J_zero, J_zero, max_add', max_add']
    exact max_le_max (by linarith) (by linarith)
  | n + 1, x, y, hxy => by
    have ih := J_add_mono n
    have hb := M.beta_mem.1
    have hq := M.q_mem
    have hu := u_pos M
    have hd := M.d_pos
    rw [J_succ, J_succ, max_add', max_add']
    refine max_le_max ?_ ?_
    · unfold BinomialModel.payoff
      rw [max_add', max_add']
      exact max_le_max (by linarith) (by linarith)
    · have e : ∀ z : ℝ, M.beta * (M.q * M.J n (z * M.u) + (1 - M.q) * M.J n (z * M.d)) + z
          = M.beta * M.q * (M.J n (z * M.u) + z * M.u)
            + M.beta * (1 - M.q) * (M.J n (z * M.d) + z * M.d) := by
        intro z; linear_combination (-z) * M.riskNeutral
      rw [e, e]
      have h1 := ih (x * M.u) (y * M.u) (mul_le_mul_of_nonneg_right hxy hu.le)
      have h2 := ih (x * M.d) (y * M.d) (mul_le_mul_of_nonneg_right hxy hd.le)
      have c1 : 0 ≤ M.beta * M.q := mul_nonneg hb.le hq.1.le
      have c2 : 0 ≤ M.beta * (1 - M.q) := mul_nonneg hb.le (by linarith [hq.2])
      have := mul_le_mul_of_nonneg_left h1 c1
      have := mul_le_mul_of_nonneg_left h2 c2
      linarith

lemma J_le_succ : ∀ n x, M.J n x ≤ M.J (n + 1) x
  | 0, x => by rw [J_succ]; exact le_max_left _ _
  | n + 1, x => by
    rw [J_succ, J_succ M (n + 1)]
    refine max_le_max le_rfl ?_
    have hb := M.beta_mem.1
    have hq := M.q_mem
    have h1 := J_le_succ n (x * M.u)
    have h2 := J_le_succ n (x * M.d)
    have := mul_le_mul_of_nonneg_left h1 hq.1.le
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - M.q by linarith [hq.2])
    exact mul_le_mul_of_nonneg_left (by linarith) hb.le

lemma J_mono_idx {m n : ℕ} (h : m ≤ n) (x : ℝ) : M.J m x ≤ M.J n x :=
  (monotone_nat_of_le_succ (fun k => J_le_succ M k x)) h

lemma J_at_zero : ∀ n, M.J n 0 = M.K
  | 0 => by rw [J_zero]; simp [M.K_pos.le]
  | n + 1 => by
    rw [J_succ, zero_mul, zero_mul, J_at_zero n]
    have hb := M.beta_mem
    have hK := M.K_pos
    have hp : M.payoff 0 = M.K := by unfold BinomialModel.payoff; simp [hK.le]
    rw [hp, max_eq_left]
    have : M.beta * (M.q * M.K + (1 - M.q) * M.K) = M.beta * M.K := by ring
    rw [this]
    nlinarith [hb.2]

/-- The continuation value is at most `J (n+1)`. -/
lemma cont_le (n : ℕ) (x : ℝ) :
    M.beta * (M.q * M.J n (x * M.u) + (1 - M.q) * M.J n (x * M.d)) ≤ M.J (n + 1) x := by
  rw [J_succ]; exact le_max_right _ _

/-- If `J (n+1) x ≠ K - x` then `J (n+1) x` equals the continuation value. -/
lemma J_eq_cont (n : ℕ) (x : ℝ) (h : M.J (n + 1) x ≠ M.K - x) :
    M.J (n + 1) x = M.beta * (M.q * M.J n (x * M.u) + (1 - M.q) * M.J n (x * M.d)) := by
  have hb := M.beta_mem.1
  have hq := M.q_mem
  have hc : 0 ≤ M.beta * (M.q * M.J n (x * M.u) + (1 - M.q) * M.J n (x * M.d)) := by
    have := J_nonneg M n (x * M.u)
    have := J_nonneg M n (x * M.d)
    have : 0 ≤ 1 - M.q := by linarith [hq.2]
    exact mul_nonneg hb.le (add_nonneg (mul_nonneg hq.1.le (by assumption))
      (mul_nonneg this (by assumption)))
  rw [J_succ] at h ⊢
  unfold BinomialModel.payoff at h ⊢
  rcases le_total (M.K - x) 0 with h1 | h1
  · rw [max_eq_right h1, max_eq_right hc]
  · rw [max_eq_left h1] at h ⊢
    rcases le_total (M.K - x) (M.beta * (M.q * M.J n (x * M.u) + (1 - M.q) * M.J n (x * M.d)))
      with h2 | h2
    · rw [max_eq_right h2]
    · rw [max_eq_left h2] at h; exact absurd rfl h

/-! ### Exercise thresholds -/

def A (N n : ℕ) : Set ℝ := {y | M.J (N - n) y + y ≤ M.K}

noncomputable def xs (N : ℕ) (n : ℕ) : ℝ := sSup (A M N n)

lemma A_closed (N n : ℕ) : IsClosed (A M N n) :=
  isClosed_le ((J_cont M _).add continuous_id) continuous_const

lemma A_bdd (N n : ℕ) : BddAbove (A M N n) :=
  ⟨M.K, fun y hy => by have := J_nonneg M (N - n) y; simp only [A, Set.mem_setOf_eq] at hy; linarith⟩

lemma zero_mem_A (N n : ℕ) : (0 : ℝ) ∈ A M N n := by
  simp only [A, Set.mem_setOf_eq, J_at_zero, add_zero, le_refl]

lemma mem_A_iff (N n : ℕ) (y : ℝ) : y ∈ A M N n ↔ y ≤ xs M N n := by
  constructor
  · intro hy; exact le_csSup (A_bdd M N n) hy
  · intro hy
    have hm : xs M N n ∈ A M N n :=
      (A_closed M N n).csSup_mem ⟨0, zero_mem_A M N n⟩ (A_bdd M N n)
    simp only [A, Set.mem_setOf_eq] at hm ⊢
    have := J_add_mono M (N - n) y (xs M N n) hy
    linarith

lemma price_iff (N n : ℕ) (y : ℝ) : M.J (N - n) y = M.K - y ↔ y ≤ xs M N n := by
  rw [← mem_A_iff]
  simp only [A, Set.mem_setOf_eq]
  have := J_ge_sub M (N - n) y
  constructor
  · intro h; linarith
  · intro h; linarith

lemma xs_N (N : ℕ) : xs M N N = M.K := by
  have : A M N N = Set.Iic M.K := by
    ext y
    simp only [A, Nat.sub_self, J_zero, Set.mem_setOf_eq, Set.mem_Iic, max_add']
    constructor
    · intro h; linarith [le_max_right (M.K - y + y) (0 + y)]
    · intro h; exact max_le (by linarith) (by linarith)
  rw [xs, this, csSup_Iic]

lemma xs_nonneg (N n : ℕ) : 0 ≤ xs M N n := (mem_A_iff M N n 0).1 (zero_mem_A M N n)

lemma xs_mono (N n : ℕ) (hn : n < N) : xs M N n ≤ xs M N (n + 1) := by
  refine csSup_le_csSup (A_bdd M N (n + 1)) ⟨0, zero_mem_A M N n⟩ ?_
  intro y hy
  simp only [A, Set.mem_setOf_eq] at hy ⊢
  have := J_mono_idx M (show N - (n + 1) ≤ N - n by omega) y
  linarith

/-! ### Part 2: integration over cylinders -/

def Dep (n : ℕ) (F : (ℕ → Bool) → ℝ) : Prop :=
  ∀ w w' : ℕ → Bool, (∀ i < n, w i = w' i) → F w = F w'

def ext {n : ℕ} (b : Fin n → Bool) : ℕ → Bool := fun i => if h : i < n then b ⟨i, h⟩ else false

def cyl {n : ℕ} (b : Fin n → Bool) : Set (ℕ → Bool) := {w | ∀ i : Fin n, w (i : ℕ) = b i}

def wt (b : Bool) : ℝ := if b then M.q else 1 - M.q

lemma cyl_meas {n : ℕ} (b : Fin n → Bool) : MeasurableSet (cyl b) := by
  have : cyl b = ⋂ i : Fin n, (fun w : ℕ → Bool => w i) ⁻¹' {b i} := by
    ext w; simp [cyl]
  rw [this]
  exact MeasurableSet.iInter fun i => measurable_pi_apply _ (measurableSet_singleton _)

lemma decomp {n : ℕ} {F : (ℕ → Bool) → ℝ} (hF : Dep n F) (w : ℕ → Bool) :
    F w = ∑ b : Fin n → Bool, (cyl b).indicator (fun _ => F (ext b)) w := by
  rw [Finset.sum_eq_single (fun i : Fin n => w i)]
  · rw [Set.indicator_of_mem (by intro i; rfl)]
    apply hF
    intro i hi
    simp [ext, hi]
  · intro b _ hb
    rw [Set.indicator_of_notMem]
    intro h
    apply hb
    funext i
    exact (h i).symm
  · simp

lemma Q_cyl {Q : Measure (ℕ → Bool)} (hQ : M.IsPathLaw Q) {n : ℕ} (b : Fin n → Bool) :
    Q.real (cyl b) = ∏ i, wt M (b i) := by
  have hq := M.q_mem
  rw [measureReal_def, cyl, hQ.2, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold wt
  cases b i
  · simp [ENNReal.toReal_ofReal (show 0 ≤ 1 - M.q by linarith [hq.2])]
  · simp [ENNReal.toReal_ofReal hq.1.le]

lemma integral_dep {Q : Measure (ℕ → Bool)} (hQ : M.IsPathLaw Q) {n : ℕ}
    {F : (ℕ → Bool) → ℝ} (hF : Dep n F) :
    Integrable F Q ∧ ∫ w, F w ∂Q = ∑ b : Fin n → Bool, (∏ i, wt M (b i)) * F (ext b) := by
  have := hQ.1
  have e : (fun w => ∑ b : Fin n → Bool, (cyl b).indicator (fun _ => F (ext b)) w) =ᵐ[Q] F :=
    Filter.Eventually.of_forall fun w => (decomp hF w).symm
  have hi : ∀ b : Fin n → Bool, Integrable ((cyl b).indicator (fun _ => F (ext b))) Q :=
    fun b => (integrable_const _).indicator (cyl_meas b)
  refine ⟨?_, ?_⟩
  · exact (integrable_finsetSum _ fun b _ => hi b).congr e
  · rw [← integral_congr_ae e, integral_finsetSum _ fun b _ => hi b]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_indicator_const _ (cyl_meas b), Q_cyl M hQ, smul_eq_mul]

lemma ext_snoc_lt {k : ℕ} (c : Fin k → Bool) (t : Bool) (i : ℕ) (hi : i < k) :
    ext (Fin.snoc c t : Fin (k + 1) → Bool) i = ext c i := by
  have h1 : i < k + 1 := by omega
  simp only [ext, h1, hi, dite_true]
  have : (⟨i, h1⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma ext_snoc_k {k : ℕ} (c : Fin k → Bool) (t : Bool) :
    ext (Fin.snoc c t : Fin (k + 1) → Bool) k = t := by
  simp only [ext, lt_add_one, dite_true]
  have : (⟨k, lt_add_one k⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [this, Fin.snoc_last]

lemma onestep {Q : Measure (ℕ → Bool)} (hQ : M.IsPathLaw Q) {k : ℕ}
    (Φ : (ℕ → Bool) → Bool → ℝ) (hΦ : ∀ b, Dep k (fun w => Φ w b)) :
    ∫ w, Φ w (w k) ∂Q = ∫ w, (M.q * Φ w true + (1 - M.q) * Φ w false) ∂Q := by
  have hL : Dep (k + 1) (fun w => Φ w (w k)) := by
    intro w w' h
    simp only
    rw [h k (lt_add_one k)]
    exact hΦ _ w w' (fun i hi => h i (by omega))
  have hR : Dep k (fun w => M.q * Φ w true + (1 - M.q) * Φ w false) := by
    intro w w' h
    have h1 := hΦ true w w' h
    have h2 := hΦ false w w' h
    simp only at h1 h2 ⊢
    rw [h1, h2]
  rw [(integral_dep M hQ hL).2, (integral_dep M hQ hR).2]
  rw [← (Fin.snocEquiv fun _ : Fin (k + 1) => Bool).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_bool]
  have hse : ∀ t : Bool, (Fin.snocEquiv fun _ : Fin (k + 1) => Bool) (t, c) = Fin.snoc c t :=
    fun _ => rfl
  simp only [hse]
  simp only [ Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    ext_snoc_k]
  have e : ∀ t b, Φ (ext (Fin.snoc c t : Fin (k + 1) → Bool)) b = Φ (ext c) b :=
    fun t b => hΦ b _ _ (fun i hi => ext_snoc_lt c t i hi)
  rw [e, e]
  simp only [wt, if_true, Bool.false_eq_true, if_false]
  ring

/-! ### Part 3: dynamic programming over stopping times -/

lemma stock_dep (x : ℝ) : ∀ k, Dep k (M.stock x k)
  | 0 => fun _ _ _ => rfl
  | k + 1 => fun w w' h => by
    simp only [BinomialModel.stock]
    rw [stock_dep x k w w' (fun i hi => h i (by omega)), h k (by omega)]

section DP

variable {M} (τ : (ℕ → Bool) → ℕ∞) (N : ℕ) (x : ℝ)

noncomputable def tt (w : ℕ → Bool) : ℕ := (τ w).toNat

lemma tau_eq (hN : ∀ w, τ w ≤ (N : ℕ∞)) (w : ℕ → Bool) : τ w = (tt τ w : ℕ∞) :=
  (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top N) (hN w))).symm

lemma tt_le (hN : ∀ w, τ w ≤ (N : ℕ∞)) (w : ℕ → Bool) : tt τ w ≤ N := by
  have := hN w
  rw [tau_eq τ N hN w] at this
  exact_mod_cast this

lemma tt_agree (hτ : IsStoppingTime τ) (hN : ∀ w, τ w ≤ (N : ℕ∞)) {k : ℕ} {w w' : ℕ → Bool}
    (h : ∀ i < k, w i = w' i) (hw : tt τ w ≤ k) : tt τ w' = tt τ w := by
  have h1 := tau_eq τ N hN w
  have h2 := (hτ (tt τ w) w w' (fun i hi => h i (by omega))).1 h1
  rw [tt, h2, ENat.toNat_natCast]

noncomputable def R (w : ℕ → Bool) : ℝ :=
  M.beta ^ (tt τ w) * M.payoff (M.stock x (tt τ w) w)

noncomputable def Z (k : ℕ) (w : ℕ → Bool) : ℝ :=
  if tt τ w < k then R (M := M) τ x w else M.beta ^ k * M.J (N - k) (M.stock x k w)

lemma rewardPlus_eq (hN : ∀ w, τ w ≤ (N : ℕ∞)) (w : ℕ → Bool) :
    M.rewardPlus x τ w = R (M := M) τ x w := by
  unfold BinomialModel.rewardPlus
  rw [tau_eq τ N hN w]
  rfl

lemma R_agree (hτ : IsStoppingTime τ) (hN : ∀ w, τ w ≤ (N : ℕ∞)) {k : ℕ} {w w' : ℕ → Bool}
    (h : ∀ i < k, w i = w' i) (hw : tt τ w ≤ k) : R (M := M) τ x w = R (M := M) τ x w' := by
  unfold R
  rw [tt_agree τ N hτ hN h hw, stock_dep M x (tt τ w) w w' (fun i hi => h i (by omega))]

lemma lt_iff_agree (hτ : IsStoppingTime τ) (hN : ∀ w, τ w ≤ (N : ℕ∞)) {k m : ℕ}
    (hm : m ≤ k + 1) {w w' : ℕ → Bool}
    (h : ∀ i < k, w i = w' i) : tt τ w < m ↔ tt τ w' < m := by
  have h' : ∀ i < k, w' i = w i := fun i hi => (h i hi).symm
  constructor
  · intro hw; rw [tt_agree τ N hτ hN h (by omega)]; exact hw
  · intro hw; rw [tt_agree τ N hτ hN h' (by omega)]; exact hw

lemma Z_dep (hτ : IsStoppingTime τ) (hN : ∀ w, τ w ≤ (N : ℕ∞)) (k : ℕ) :
    Dep k (Z (M := M) τ N x k) := by
  intro w w' h
  unfold Z
  have hiff := lt_iff_agree τ N hτ hN (show k ≤ k + 1 by omega) h
  by_cases hw : tt τ w < k
  · rw [if_pos hw, if_pos (hiff.1 hw), R_agree τ N x hτ hN h hw.le]
  · rw [if_neg hw, if_neg (fun h' => hw (hiff.2 h')), stock_dep M x k w w' h]

lemma R_dep (hτ : IsStoppingTime τ) (hN : ∀ w, τ w ≤ (N : ℕ∞)) : Dep N (R (M := M) τ x) :=
  fun _ _ h => R_agree τ N x hτ hN h (tt_le τ N hN _)

lemma R_nonneg (w : ℕ → Bool) : 0 ≤ R (M := M) τ x w := by
  unfold R
  have := M.beta_mem.1
  have := payoff_nonneg M (M.stock x (tt τ w) w)
  positivity

noncomputable def Φ (k : ℕ) (w : ℕ → Bool) (b : Bool) : ℝ :=
  if tt τ w < k + 1 then R (M := M) τ x w
  else M.beta ^ (k + 1) * M.J (N - (k + 1)) (M.stock x k w * (if b then M.u else M.d))

noncomputable def Y (k : ℕ) (w : ℕ → Bool) : ℝ :=
  M.q * Φ (M := M) τ N x k w true + (1 - M.q) * Φ (M := M) τ N x k w false

lemma Φ_dep (hτ : IsStoppingTime τ) (hN : ∀ w, τ w ≤ (N : ℕ∞)) (k : ℕ) (b : Bool) :
    Dep k (fun w => Φ (M := M) τ N x k w b) := by
  intro w w' h
  simp only [Φ]
  have hiff := lt_iff_agree τ N hτ hN (show k + 1 ≤ k + 1 by omega) h
  by_cases hw : tt τ w < k + 1
  · rw [if_pos hw, if_pos (hiff.1 hw), R_agree τ N x hτ hN h (by omega)]
  · rw [if_neg hw, if_neg (fun h' => hw (hiff.2 h')), stock_dep M x k w w' h]

lemma Y_dep (hτ : IsStoppingTime τ) (hN : ∀ w, τ w ≤ (N : ℕ∞)) (k : ℕ) :
    Dep k (Y (M := M) τ N x k) := by
  intro w w' h
  have h1 := Φ_dep (M := M) τ N x hτ hN k true w w' h
  have h2 := Φ_dep (M := M) τ N x hτ hN k false w w' h
  simp only at h1 h2
  simp only [Y]
  rw [h1, h2]

lemma Z_succ_eq (k : ℕ) (w : ℕ → Bool) :
    Z (M := M) τ N x (k + 1) w = Φ (M := M) τ N x k w (w k) := by
  simp only [Z, Φ, BinomialModel.stock]

lemma Y_le_eq (k : ℕ) (hk : k < N) (w : ℕ → Bool) :
    Y (M := M) τ N x k w ≤ Z (M := M) τ N x k w ∧
    ((tt τ w = k → M.payoff (M.stock x k w) = M.J (N - k) (M.stock x k w)) →
     (k < tt τ w → M.J (N - k) (M.stock x k w) =
        M.beta * (M.q * M.J (N - (k + 1)) (M.stock x k w * M.u)
          + (1 - M.q) * M.J (N - (k + 1)) (M.stock x k w * M.d))) →
     Y (M := M) τ N x k w = Z (M := M) τ N x k w) := by
  have hb := M.beta_mem.1
  set S := M.stock x k w with hS
  have e : N - k = (N - (k + 1)) + 1 := by omega
  simp only [Y, Φ, Z]
  by_cases h1 : tt τ w < k
  · have h' : tt τ w < k + 1 := by omega
    rw [if_pos h', if_pos h', if_pos h1]
    constructor
    · linarith
    · intro _ _; ring
  rw [if_neg h1]
  by_cases h2 : tt τ w = k
  · have h' : tt τ w < k + 1 := by omega
    rw [if_pos h', if_pos h']
    have hR : R (M := M) τ x w = M.beta ^ k * M.payoff S := by rw [R, h2]
    rw [hR]
    have hle := J_ge_payoff M (N - k) S
    constructor
    · have := mul_le_mul_of_nonneg_left hle (pow_nonneg hb.le k)
      linarith
    · intro hp _
      rw [← hp h2]; ring
  · have h' : ¬ tt τ w < k + 1 := by omega
    rw [if_neg h', if_neg h']
    simp only [if_true, Bool.false_eq_true, if_false]
    have hc := cont_le M (N - (k + 1)) S
    rw [← e] at hc
    constructor
    · have := mul_le_mul_of_nonneg_left hc (pow_nonneg hb.le k)
      rw [pow_succ]
      linarith
    · intro _ hp
      rw [hp (by omega), pow_succ]; ring

lemma step {Q : Measure (ℕ → Bool)} (hQ : M.IsPathLaw Q) (hτ : IsStoppingTime τ)
    (hN : ∀ w, τ w ≤ (N : ℕ∞)) (k : ℕ) :
    ∫ w, Z (M := M) τ N x (k + 1) w ∂Q = ∫ w, Y (M := M) τ N x k w ∂Q := by
  simp_rw [Z_succ_eq]
  exact onestep M hQ _ (Φ_dep τ N x hτ hN k)

lemma Z_zero (w : ℕ → Bool) : Z (M := M) τ N x 0 w = M.J N x := by
  simp [Z, BinomialModel.stock]

lemma Z_N (hN : ∀ w, τ w ≤ (N : ℕ∞)) (w : ℕ → Bool) : Z (M := M) τ N x N w = R (M := M) τ x w := by
  unfold Z
  by_cases h : tt τ w < N
  · rw [if_pos h]
  · rw [if_neg h]
    have : tt τ w = N := le_antisymm (tt_le τ N hN w) (by omega)
    rw [R, this, Nat.sub_self, J_zero]; rfl

lemma main_le {Q : Measure (ℕ → Bool)} (hQ : M.IsPathLaw Q) (hτ : IsStoppingTime τ)
    (hN : ∀ w, τ w ≤ (N : ℕ∞)) :
    ∀ k ≤ N, ∫ w, Z (M := M) τ N x k w ∂Q ≤ M.J N x := by
  have := hQ.1
  intro k
  induction k with
  | zero => intro _; simp [Z_zero]
  | succ k ih =>
    intro hk
    rw [step τ N x hQ hτ hN k]
    refine le_trans (integral_mono (integral_dep M hQ (Y_dep τ N x hτ hN k)).1
      (integral_dep M hQ (Z_dep τ N x hτ hN k)).1 fun w => (Y_le_eq τ N x k hk w).1) (ih (by omega))

lemma main_eq {Q : Measure (ℕ → Bool)} (hQ : M.IsPathLaw Q) (hτ : IsStoppingTime τ)
    (hN : ∀ w, τ w ≤ (N : ℕ∞))
    (g1 : ∀ k < N, ∀ w, tt τ w = k → M.payoff (M.stock x k w) = M.J (N - k) (M.stock x k w))
    (g2 : ∀ k < N, ∀ w, k < tt τ w → M.J (N - k) (M.stock x k w) =
        M.beta * (M.q * M.J (N - (k + 1)) (M.stock x k w * M.u)
          + (1 - M.q) * M.J (N - (k + 1)) (M.stock x k w * M.d))) :
    ∀ k ≤ N, ∫ w, Z (M := M) τ N x k w ∂Q = M.J N x := by
  have := hQ.1
  intro k
  induction k with
  | zero => intro _; simp [Z_zero]
  | succ k ih =>
    intro hk
    rw [step τ N x hQ hτ hN k, ← ih (by omega)]
    congr 1
    funext w
    exact (Y_le_eq τ N x k hk w).2 (g1 k hk w) (g2 k hk w)

lemma integral_R_le {Q : Measure (ℕ → Bool)} (hQ : M.IsPathLaw Q) (hτ : IsStoppingTime τ)
    (hN : ∀ w, τ w ≤ (N : ℕ∞)) : ∫ w, R (M := M) τ x w ∂Q ≤ M.J N x := by
  have := main_le τ N x hQ hτ hN N le_rfl
  simp_rw [Z_N τ N x hN] at this
  exact this

end DP

lemma ereal_eq {Q : Measure (ℕ → Bool)} (f : (ℕ → Bool) → ℝ) (hf : ∀ w, 0 ≤ f w)
    (hi : Integrable f Q) :
    erealIntegral Q (fun w => (f w : EReal)) = ((∫ w, f w ∂Q : ℝ) : EReal) := by
  unfold erealIntegral
  have e1 : ∀ w, ((f w : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (f w) := by
    intro w
    rw [max_eq_left (EReal.coe_nonneg.2 (hf w))]
    rfl
  have e2 : ∀ w, ((-(f w : EReal)) ⊔ 0).toENNReal = 0 := by
    intro w
    rw [max_eq_right]
    · exact EReal.toENNReal_zero
    · rw [EReal.neg_le, neg_zero]; exact EReal.coe_nonneg.2 (hf w)
  simp only [e1, e2, lintegral_zero, EReal.coe_ennreal_zero, neg_zero, add_zero]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf),
    EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg hf)]

/-! ### Threshold time -/

lemma th_char (x : ℝ) (xst : ℕ → ℝ) (N : ℕ) (w : ℕ → Bool) (n : ℕ) :
    M.thresholdTime x xst N w = (n : ℕ∞) ↔
      n ≤ N ∧ (n < N → M.stock x n w ≤ xst n) ∧ ∀ j < n, xst j < M.stock x j w := by
  unfold BinomialModel.thresholdTime
  set s := sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | M.stock x k w ≤ xst k}) with hs
  constructor
  · intro h
    have hnN : n ≤ N := by
      have : (n : ℕ∞) ≤ N := h ▸ min_le_right _ _
      exact_mod_cast this
    refine ⟨hnN, ?_, ?_⟩
    · intro hn
      have hsn : s = n := by
        rcases le_total s N with h' | h'
        · rwa [min_eq_left h'] at h
        · rw [min_eq_right h'] at h
          exact absurd (h ▸ rfl : (N : ℕ∞) = n) (by exact_mod_cast hn.ne')
      by_contra hc
      have : ((n + 1 : ℕ) : ℕ∞) ≤ s := by
        refine le_sInf ?_
        rintro _ ⟨j, hj, rfl⟩
        have h1 : s ≤ j := sInf_le ⟨j, hj, rfl⟩
        rw [hsn] at h1
        have h1' : n ≤ j := by exact_mod_cast h1
        have : j ≠ n := by rintro rfl; exact hc hj
        exact (Nat.cast_le (α := ℕ∞)).2 (show n + 1 ≤ j by omega)
      rw [hsn] at this
      have : n + 1 ≤ n := by exact_mod_cast this
      omega
    · intro j hj
      by_contra hc
      replace hc := not_lt.1 hc
      have h1 : s ≤ j := sInf_le ⟨j, hc, rfl⟩
      have : min s (N : ℕ∞) ≤ j := le_trans (min_le_left _ _) h1
      rw [h] at this
      have : n ≤ j := by exact_mod_cast this
      omega
  · rintro ⟨hnN, hlt, hall⟩
    apply le_antisymm
    · rcases Nat.lt_or_ge n N with hn | hn
      · exact le_trans (min_le_left _ _) (sInf_le ⟨n, hlt hn, rfl⟩)
      · have : n = N := le_antisymm hnN hn
        subst this; exact min_le_right _ _
    · refine le_min (le_sInf ?_) (by exact_mod_cast hnN)
      rintro _ ⟨j, hj, rfl⟩
      by_contra hc
      have hc' : j < n := by
        by_contra h'
        exact hc ((Nat.cast_le (α := ℕ∞)).2 (by omega))
      have := hall j hc'
      simp only [Set.mem_setOf_eq] at hj
      linarith

lemma th_le (x : ℝ) (xst : ℕ → ℝ) (N : ℕ) (w : ℕ → Bool) :
    M.thresholdTime x xst N w ≤ (N : ℕ∞) := min_le_right _ _

lemma th_stop (x : ℝ) (xst : ℕ → ℝ) (N : ℕ) : IsStoppingTime (M.thresholdTime x xst N) := by
  intro n w w' h
  rw [th_char, th_char]
  have e : ∀ j ≤ n, M.stock x j w = M.stock x j w' :=
    fun j hj => stock_dep M x j w w' (fun i hi => h i (by omega))
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨a, fun hn => (e n le_rfl) ▸ b hn, fun j hj => (e j hj.le) ▸ c j hj⟩
  · rintro ⟨a, b, c⟩
    refine ⟨a, fun hn => (e n le_rfl).symm ▸ b hn, fun j hj => (e j hj.le).symm ▸ c j hj⟩

end S100Put

open MDPFinance.StoppingFinance MeasureTheory in
theorem solution (M : MDPFinance.StoppingFinance.BinomialModel) (N : ℕ) :
    (∀ n : ℕ, ContinuousOn (M.price N n) M.E) ∧
    (∀ n : ℕ, ∀ x ∈ M.E, ∀ y ∈ M.E, x ≤ y → M.price N n x + x ≤ M.price N n y + y) ∧
    (∀ (m n : ℕ), m ≤ n → n ≤ N → ∀ x ∈ M.E, M.price N n x ≤ M.price N m x) ∧
    (∃ xstar : ℕ → ℝ,
      xstar N = M.K ∧
      (∀ n : ℕ, n < N → xstar n ≤ xstar (n + 1)) ∧
      (∀ n : ℕ, n ≤ N → 0 ≤ xstar n) ∧
      (∀ (n : ℕ) (x : ℝ), n ≤ N → x ∈ M.E → (M.price N n x = M.K - x ↔ x ≤ xstar n)) ∧
      ∀ Q : Measure (ℕ → Bool), M.IsPathLaw Q → ∀ x ∈ M.E,
        IsStoppingTime (M.thresholdTime x xstar N) ∧
        M.ERewardPlus Q x (M.thresholdTime x xstar N) = M.finiteValue Q N x ∧
        M.finiteValue Q N x = (M.J N x : EReal)) := by
  refine ⟨fun n => (S100Put.J_cont M _).continuousOn, ?_, ?_, ?_⟩
  · intro n x _ y _ hxy
    exact S100Put.J_add_mono M _ x y hxy
  · intro m n hmn _ x _
    exact S100Put.J_mono_idx M (by omega) x
  refine ⟨S100Put.xs M N, S100Put.xs_N M N, fun n hn => S100Put.xs_mono M N n hn,
    fun n _ => S100Put.xs_nonneg M N n, fun n x _ _ => S100Put.price_iff M N n x, ?_⟩
  intro Q hQ x _
  set τs := M.thresholdTime x (S100Put.xs M N) N with hτs
  have hst : IsStoppingTime τs := S100Put.th_stop M x _ N
  have hsN : ∀ w, τs w ≤ (N : ℕ∞) := S100Put.th_le M x _ N
  -- value of any admissible stopping time
  have val : ∀ τ : (ℕ → Bool) → ℕ∞, IsStoppingTime τ → (∀ w, τ w ≤ (N : ℕ∞)) →
      M.ERewardPlus Q x τ = ((∫ w, S100Put.R (M := M) τ x w ∂Q : ℝ) : EReal) := by
    intro τ hτ hN
    unfold BinomialModel.ERewardPlus
    simp_rw [S100Put.rewardPlus_eq τ N x hN]
    exact S100Put.ereal_eq _ (S100Put.R_nonneg τ x)
      (S100Put.integral_dep M hQ (S100Put.R_dep τ N x hτ hN)).1
  have opt : ∫ w, S100Put.R (M := M) τs x w ∂Q = M.J N x := by
    have := S100Put.main_eq τs N x hQ hst hsN ?_ ?_ N le_rfl
    · simp_rw [S100Put.Z_N τs N x hsN] at this
      exact this
    · intro k hk w hw
      have h1 : τs w = (k : ℕ∞) := by rw [S100Put.tau_eq τs N hsN w, hw]
      have h2 := ((S100Put.th_char M x _ N w k).1 h1).2.1 hk
      have h3 := (S100Put.price_iff M N k _).2 h2
      rw [h3]
      unfold BinomialModel.payoff
      rw [max_eq_left]
      have := S100Put.J_nonneg M (N - k) (M.stock x k w)
      linarith
    · intro k hk w hw
      have h1 := S100Put.tau_eq τs N hsN w
      have h2 := ((S100Put.th_char M x (S100Put.xs M N) N w (S100Put.tt τs w)).1 h1).2.2 k hw
      have h3 : M.J (N - k) (M.stock x k w) ≠ M.K - M.stock x k w := by
        intro h; have := (S100Put.price_iff M N k _).1 h; linarith
      have e : N - k = (N - (k + 1)) + 1 := by omega
      rw [e] at h3 ⊢
      exact S100Put.J_eq_cont M _ _ h3
  have fv : M.finiteValue Q N x = (M.J N x : EReal) := by
    apply le_antisymm
    · refine iSup₂_le fun τ hτ => ?_
      rw [val τ hτ.1 hτ.2]
      exact EReal.coe_le_coe_iff.2 (S100Put.integral_R_le τ N x hQ hτ.1 hτ.2)
    · refine le_iSup₂_of_le τs ⟨hst, hsN⟩ ?_
      rw [val τs hst hsN, opt]
  refine ⟨hst, ?_, fv⟩
  rw [fv, val τs hst hsN, opt]
