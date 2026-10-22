-- Prove2me | solution 1 for IncProx.Cyclic.proposition6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T03:22:14.282798+00:00
-- url     : https://prove2.me/submissions/470f3c8a-53eb-4c43-9ec9-65f84c546d0e

import Mathlib
import Definitions.Def_IncProx_Cyclic_Basic

set_option autoImplicit false

namespace IP6

open IncProx.Cyclic Filter Topology

variable {n m : ℕ}

lemma proj_vi {X : Set (Vec n)} (hX : Convex ℝ X) {u p : Vec n} (hp : IsProj X u p)
    {w : Vec n} (hw : w ∈ X) : inner ℝ (u - p) (w - p) ≤ 0 := by
  have hb : BddBelow (Set.range fun v : X => ‖u - (v : Vec n)‖) :=
    ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩
  have heq : ‖u - p‖ = ⨅ v : X, ‖u - (v : Vec n)‖ := by
    apply le_antisymm
    · have : Nonempty X := ⟨⟨p, hp.1⟩⟩
      exact le_ciInf fun v => hp.2 v v.2
    · exact ciInf_le hb ⟨p, hp.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hX hp.1).1 heq w hw

lemma proj_dist {X : Set (Vec n)} {u p q : Vec n} (hp : IsProj X u p) (hq : q ∈ X) :
    ‖p - q‖ ≤ 2 * ‖u - q‖ := by
  have h1 : ‖p - q‖ ≤ ‖u - p‖ + ‖u - q‖ := by
    calc ‖p - q‖ = ‖(u - q) - (u - p)‖ := by congr 1; abel
      _ ≤ ‖u - q‖ + ‖u - p‖ := norm_sub_le _ _
      _ = ‖u - p‖ + ‖u - q‖ := add_comm _ _
  have h2 := hp.2 q hq
  linarith

/-- projection step whose subgradient is taken at the new point -/
lemma proj_new {X : Set (Vec n)} (hX : Convex ℝ X) {f : Vec n → ℝ} {v g p y : Vec n} {a : ℝ}
    (ha : 0 ≤ a) (hp : IsProj X (v - a • g) p) (hg : IsSubgrad f p g) (hy : y ∈ X) :
    ‖p - y‖ ^ 2 ≤ ‖v - y‖ ^ 2 - 2 * a * (f p - f y) := by
  have hvi := proj_vi hX hp hy
  have hs := hg y
  have e1 : v - y = (v - p) + (p - y) := by abel
  have e2 : v - a • g - p = (v - p) - a • g := by abel
  have e3 : y - p = -(p - y) := by abel
  rw [e2, e3, inner_neg_right, inner_sub_left, real_inner_smul_left] at hvi
  rw [e3, inner_neg_right] at hs
  rw [e1, norm_add_sq_real]
  have : 0 ≤ ‖v - p‖ ^ 2 := sq_nonneg _
  nlinarith

lemma proj_base {X : Set (Vec n)} (hX : Convex ℝ X) {u p y : Vec n} (hp : IsProj X u p)
    (hy : y ∈ X) : ‖p - y‖ ^ 2 ≤ ‖u - y‖ ^ 2 := by
  have hvi := proj_vi hX hp hy
  have e1 : u - y = (u - p) + (p - y) := by abel
  have e3 : y - p = -(p - y) := by abel
  rw [e3, inner_neg_right] at hvi
  rw [e1, norm_add_sq_real]
  have : 0 ≤ ‖u - p‖ ^ 2 := sq_nonneg _
  linarith

/-- projection step whose subgradient is taken at the old point -/
lemma proj_old {X : Set (Vec n)} (hX : Convex ℝ X) {h : Vec n → ℝ} {z g p y : Vec n} {a : ℝ}
    (ha : 0 ≤ a) (hp : IsProj X (z - a • g) p) (hg : IsSubgrad h z g) (hy : y ∈ X) :
    ‖p - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 - 2 * a * (h z - h y) + a ^ 2 * ‖g‖ ^ 2 := by
  have h1 := proj_base hX hp hy
  have hs := hg y
  have e1 : z - a • g - y = (z - y) - a • g := by abel
  have e3 : y - z = -(z - y) := by abel
  rw [e1, norm_sub_sq_real (z - y) (a • g), real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at h1
  rw [e3, inner_neg_right, real_inner_comm] at hs
  nlinarith

/-- explicit (no projection) step with subgradient at the new point -/
lemma expl_new {f : Vec n → ℝ} {x g z y : Vec n} {a : ℝ} (ha : 0 ≤ a)
    (hz : z = x - a • g) (hg : IsSubgrad f z g) :
    ‖z - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (f z - f y) := by
  have hs := hg y
  have e1 : x - y = (z - y) + a • g := by rw [hz]; abel
  have e3 : y - z = -(z - y) := by abel
  rw [e3, inner_neg_right, real_inner_comm] at hs
  rw [e1, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have : 0 ≤ a ^ 2 * ‖g‖ ^ 2 := by positivity
  nlinarith

/-- explicit step with subgradient at the old point -/
lemma expl_old {h : Vec n → ℝ} {x g z y : Vec n} {a : ℝ} (ha : 0 ≤ a)
    (hz : z = x - a • g) (hg : IsSubgrad h x g) :
    ‖z - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (h x - h y) + a ^ 2 * ‖g‖ ^ 2 := by
  have hs := hg y
  have e1 : z - y = (x - y) - a • g := by rw [hz]; abel
  have e3 : y - x = -(x - y) := by abel
  rw [e3, inner_neg_right, real_inner_comm] at hs
  rw [e1, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith

/-- the value term of one step -/
noncomputable def Val (P : Problem n m) : Alg → Fin m → Vec n → Vec n → Vec n → ℝ
  | .a19, i, _, z, _ => P.Fi i z
  | .a20, i, _, z, _ => P.Fi i z
  | .a21, i, x, _, x' => P.h i x + P.f i x'

lemma step_ineq (P : Problem n m) (hP : P.Standing) (A : Alg) (i : Fin m) {a c : ℝ}
    {x z gF gH x' y : Vec n} (ha : 0 ≤ a) (hst : Step P A i a x z gF gH x') (hgF : ‖gF‖ ≤ c)
    (hgH : ‖gH‖ ≤ c) (hy : y ∈ P.X) :
    ‖x' - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (Val P A i x z x' - P.Fi i y) + a ^ 2 * c ^ 2 := by
  have hX := hP.X_convex
  cases A with
  | a19 =>
    obtain ⟨h1, h2, h3, h4⟩ := hst
    have k1 := proj_new hX ha h2 h1 hy
    have k2 := proj_old hX ha h4 h3 hy
    have : a ^ 2 * ‖gH‖ ^ 2 ≤ a ^ 2 * c ^ 2 := by gcongr
    simp only [Val, Problem.Fi]
    nlinarith
  | a20 =>
    obtain ⟨h1, h2, h3, h4⟩ := hst
    have k1 := expl_new (y := y) ha h2 h1
    have k2 := proj_old hX ha h4 h3 hy
    have : a ^ 2 * ‖gH‖ ^ 2 ≤ a ^ 2 * c ^ 2 := by gcongr
    simp only [Val, Problem.Fi]
    nlinarith
  | a21 =>
    obtain ⟨h1, h2, h3, h4⟩ := hst
    have k1 := expl_old (y := y) ha h2 h1
    have k2 := proj_new hX ha h4 h3 hy
    have : a ^ 2 * ‖gH‖ ^ 2 ≤ a ^ 2 * c ^ 2 := by gcongr
    simp only [Val, Problem.Fi]
    nlinarith

lemma step_mem (P : Problem n m) (A : Alg) (i : Fin m) {a : ℝ}
    {x z gF gH x' : Vec n} (hst : Step P A i a x z gF gH x') : x' ∈ P.X := by
  cases A with
  | a19 => exact hst.2.2.2.1
  | a20 => exact hst.2.2.2.1
  | a21 => exact hst.2.2.2.1

lemma step_dist (P : Problem n m) (A : Alg) (i : Fin m) {a c : ℝ}
    {x z gF gH x' : Vec n} (ha : 0 ≤ a) (hst : Step P A i a x z gF gH x') (hgF : ‖gF‖ ≤ c)
    (hgH : ‖gH‖ ≤ c) (hx : x ∈ P.X) :
    ‖x' - x‖ ≤ 4 * a * c ∧ ‖z - x‖ ≤ 2 * a * c := by
  have hc : 0 ≤ c := le_trans (norm_nonneg _) hgF
  have nF : ‖a • gF‖ ≤ a * c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]; exact mul_le_mul_of_nonneg_left hgF ha
  have nH : ‖a • gH‖ ≤ a * c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]; exact mul_le_mul_of_nonneg_left hgH ha
  cases A with
  | a19 =>
    obtain ⟨h1, h2, h3, h4⟩ := hst
    have d1 := proj_dist h2 hx
    have d2 := proj_dist h4 h2.1
    have e1 : x - a • gF - x = -(a • gF) := by abel
    have e2 : z - a • gH - z = -(a • gH) := by abel
    rw [e1, norm_neg] at d1
    rw [e2, norm_neg] at d2
    have : ‖x' - x‖ ≤ ‖x' - z‖ + ‖z - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    constructor <;> nlinarith
  | a20 =>
    obtain ⟨h1, h2, h3, h4⟩ := hst
    have d2 := proj_dist h4 hx
    have e1 : z - x = -(a • gF) := by rw [h2]; abel
    have e2 : z - a • gH - x = -(a • gF) - a • gH := by rw [h2]; abel
    have : ‖-(a • gF) - a • gH‖ ≤ ‖-(a • gF)‖ + ‖a • gH‖ := norm_sub_le _ _
    rw [norm_neg] at this
    rw [e2] at d2
    rw [e1, norm_neg]
    constructor <;> nlinarith
  | a21 =>
    obtain ⟨h1, h2, h3, h4⟩ := hst
    have d2 := proj_dist h4 hx
    have e1 : z - x = -(a • gH) := by rw [h2]; abel
    have e2 : z - a • gF - x = -(a • gH) - a • gF := by rw [h2]; abel
    have : ‖-(a • gH) - a • gF‖ ≤ ‖-(a • gH)‖ + ‖a • gF‖ := norm_sub_le _ _
    rw [norm_neg] at this
    rw [e2] at d2
    rw [e1, norm_neg]
    constructor <;> nlinarith

section Cyc

variable [NeZero m] {P : Problem n m} {A : Alg} {α : ℕ → ℝ} {x z gF gH : ℕ → Vec n} {c : ℝ}

lemma assm_bound (hA : AssumptionFor P A x z gF gH c) (k : ℕ) : ‖gF k‖ ≤ c ∧ ‖gH k‖ ≤ c := by
  cases A <;> exact hA.1 k

lemma run_mem (hrun : IsRun P A cyc α x z gF gH) {t : ℕ} (ht : 0 < t) : x t ∈ P.X := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  exact step_mem P A _ (hrun s)

lemma alpha_const (hα : CyclicStepsize m α) {k j : ℕ} (hkm : k % m = 0) (hj : j < m) :
    α (k + j) = α k := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hkm
  have hm : 0 < m := NeZero.pos m
  rw [hα.2 (m * q + j), hα.2 (m * q)]
  congr 2
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hj, add_zero, Nat.mul_div_cancel_left q hm]

lemma cyc_add {k : ℕ} (hkm : k % m = 0) (j : ℕ) : (cyc (k + j) : Fin m) = cyc j := by
  apply Fin.ext
  simp [cyc, Nat.add_mod, hkm]

lemma cyc_val {j : ℕ} (hj : j < m) : ((cyc j : Fin m) : ℕ) = j := Nat.mod_eq_of_lt hj

lemma drift (hα : CyclicStepsize m α) (hrun : IsRun P A cyc α x z gF gH)
    (hb : ∀ k, ‖gF k‖ ≤ c ∧ ‖gH k‖ ≤ c) {k : ℕ} (hk0 : 0 < k) (hkm : k % m = 0) :
    ∀ j ≤ m, ‖x (k + j) - x k‖ ≤ 4 * α k * c * j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjm : j < m := hj
    have h1 := ih hjm.le
    have hst := step_dist P A _ (hα.1 (k + j)).le (hrun (k + j)) (hb (k + j)).1 (hb (k + j)).2
      (run_mem hrun (by omega))
    rw [alpha_const hα hkm hjm] at hst
    have : ‖x (k + (j + 1)) - x k‖ ≤ ‖x (k + j + 1) - x (k + j)‖ + ‖x (k + j) - x k‖ := by
      rw [← add_assoc]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    push_cast
    linarith [hst.1]

lemma val_lb (hα : CyclicStepsize m α) (hrun : IsRun P A cyc α x z gF gH)
    (hA : AssumptionFor P A x z gF gH c) {k : ℕ} (hk0 : 0 < k) (hkm : k % m = 0) {j : ℕ}
    (hj : j < m) :
    P.Fi (cyc j) (x k) - 12 * α k * c ^ 2 * m ≤
      Val P A (cyc (k + j)) (x (k + j)) (z (k + j)) (x (k + j + 1)) := by
  have hb := assm_bound hA
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (hb 0).1
  have ha : 0 < α k := hα.1 k
  have hdr := drift hα hrun hb hk0 hkm j hj.le
  have hst := step_dist P A _ (hα.1 (k + j)).le (hrun (k + j)) (hb (k + j)).1 (hb (k + j)).2
    (run_mem hrun (by omega))
  rw [alpha_const hα hkm hj] at hst
  have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hac : 0 ≤ α k * c := mul_nonneg ha.le hc
  have hp1 := mul_nonneg hac (sub_nonneg.2 hjm)
  have hp2 := mul_nonneg hac hj0
  have hac2 : 0 ≤ α k * c ^ 2 := mul_nonneg ha.le (sq_nonneg c)
  have hp3 := mul_nonneg hac2 (sub_nonneg.2 hjm)
  have hp4 := mul_nonneg hac2 hj0
  rw [cyc_add hkm]
  have hv := cyc_val (m := m) hj
  cases A with
  | a19 =>
    obtain ⟨hf, hh⟩ := hA.2 k hk0 hkm (cyc j)
    rw [hv] at hf hh
    have hd : ‖x k - z (k + j)‖ ≤ 6 * α k * c * m := by
      have : ‖x k - z (k + j)‖ ≤ ‖z (k + j) - x (k + j)‖ + ‖x (k + j) - x k‖ := by
        rw [norm_sub_rev]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      nlinarith [hst.2]
    have hcd := mul_le_mul_of_nonneg_left hd hc
    simp only [Val, Problem.Fi]
    nlinarith
  | a20 =>
    obtain ⟨hf, hh⟩ := hA.2 k hk0 hkm (cyc j)
    rw [hv] at hf hh
    have hd : ‖x k - z (k + j)‖ ≤ 6 * α k * c * m := by
      have : ‖x k - z (k + j)‖ ≤ ‖z (k + j) - x (k + j)‖ + ‖x (k + j) - x k‖ := by
        rw [norm_sub_rev]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      nlinarith [hst.2]
    have hcd := mul_le_mul_of_nonneg_left hd hc
    simp only [Val, Problem.Fi]
    nlinarith
  | a21 =>
    obtain ⟨hf, hh, hf2⟩ := hA.2 k hk0 hkm (cyc j)
    rw [hv] at hf hh hf2
    have hd1 : ‖x k - x (k + j)‖ ≤ 4 * α k * c * m := by rw [norm_sub_rev]; nlinarith
    have hd2 : ‖x (k + j) - x (k + j + 1)‖ ≤ 4 * α k * c := by rw [norm_sub_rev]; exact hst.1
    have q1 := mul_le_mul_of_nonneg_left hd1 hc
    have q2 := mul_le_mul_of_nonneg_left hd2 hc
    simp only [Val, Problem.Fi]
    nlinarith

lemma sum_cyc (P : Problem n m) (v : Vec n) :
    ∑ i ∈ Finset.range m, P.Fi (cyc i) v = P.F v := by
  rw [← Fin.sum_univ_eq_sum_range (fun t => P.Fi (cyc t) v) m]
  simp only [Problem.F]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.2)

lemma cycle_ineq (hP : P.Standing) (hα : CyclicStepsize m α) (hrun : IsRun P A cyc α x z gF gH)
    (hA : AssumptionFor P A x z gF gH c) {k : ℕ} (hk0 : 0 < k) (hkm : k % m = 0) {y : Vec n}
    (hy : y ∈ P.X) :
    ‖x (k + m) - y‖ ^ 2 ≤ ‖x k - y‖ ^ 2 - 2 * α k * (P.F (x k) - P.F y) +
      25 * c ^ 2 * m ^ 2 * α k ^ 2 := by
  have hb := assm_bound hA
  have ha : 0 < α k := hα.1 k
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.one_le
  have key : ∀ j ≤ m, ‖x (k + j) - y‖ ^ 2 ≤ ‖x k - y‖ ^ 2 -
      2 * α k * ∑ i ∈ Finset.range j, (P.Fi (cyc i) (x k) - P.Fi (cyc i) y) +
      j * (25 * α k ^ 2 * c ^ 2 * m) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjm : j < m := hj
      have h1 := ih hjm.le
      have hs := step_ineq P hP A _ (hα.1 (k + j)).le (hrun (k + j)) (hb (k + j)).1
        (hb (k + j)).2 hy
      rw [alpha_const hα hkm hjm, cyc_add hkm] at hs
      have hv := val_lb hα hrun hA hk0 hkm hjm
      rw [cyc_add hkm] at hv
      have hp := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 2 * α k)
      have hq : α k ^ 2 * c ^ 2 ≤ α k ^ 2 * c ^ 2 * m := by
        have := sq_nonneg (α k * c)
        nlinarith
      rw [Finset.sum_range_succ]
      have e : k + (j + 1) = k + j + 1 := by omega
      rw [e]
      push_cast
      nlinarith
  have h := key m le_rfl
  rw [Finset.sum_sub_distrib, sum_cyc, sum_cyc] at h
  nlinarith

end Cyc

lemma desc_false (d b : ℕ → ℝ) (hd0 : ∀ N, 0 ≤ d N) (hb0 : ∀ N, 0 < b N)
    (hb : Tendsto b atTop (𝓝 0)) (hbs : Tendsto (fun M => ∑ N ∈ Finset.range M, b N) atTop atTop)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) (N0 : ℕ)
    (hstep : ∀ N, N0 ≤ N → d (N + 1) ≤ d N - 2 * b N * ε + K * b N ^ 2) : False := by
  have hpos : 0 < ε / (K + 1) := by positivity
  obtain ⟨N1, hN1⟩ := (hb.eventually (eventually_lt_nhds hpos)).exists_forall_of_atTop
  have hst2 : ∀ N, max N0 N1 ≤ N → d (N + 1) ≤ d N - ε * b N := by
    intro N hN
    have h1 := hstep N (le_trans (le_max_left _ _) hN)
    have h2 := hN1 N (le_trans (le_max_right _ _) hN)
    have hbN := hb0 N
    have h3 : K * b N ≤ ε := by
      have : b N * (K + 1) < ε := by rwa [lt_div_iff₀ (by linarith)] at h2
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 hbN.le
    nlinarith
  set N2 := max N0 N1
  have hind : ∀ M, d (N2 + M) ≤ d N2 - ε * ∑ i ∈ Finset.range M, b (N2 + i) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ← add_assoc]
      have := hst2 (N2 + M) (Nat.le_add_right _ _)
      linarith
  obtain ⟨M0, hM0⟩ := (tendsto_atTop.1 hbs
    (∑ N ∈ Finset.range N2, b N + (d N2 + 1) / ε)).exists_forall_of_atTop
  have h1 := hM0 (N2 + M0) (Nat.le_add_left _ _)
  rw [Finset.sum_range_add] at h1
  have h2 := hind M0
  have h3 := hd0 (N2 + M0)
  have h4 : (d N2 + 1) / ε ≤ ∑ i ∈ Finset.range M0, b (N2 + i) := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 hε.le
  have h6 : ε * ((d N2 + 1) / ε) = d N2 + 1 := by field_simp
  linarith

lemma qf_conv (d e : ℕ → ℝ) (hd0 : ∀ N, 0 ≤ d N) (he0 : ∀ N, 0 ≤ e N) (he : Summable e)
    (hstep : ∀ N, d (N + 1) ≤ d N + e N) : ∃ ℓ, Tendsto d atTop (𝓝 ℓ) := by
  set w : ℕ → ℝ := fun N => d N - ∑ i ∈ Finset.range N, e i with hw
  have hanti : Antitone w := by
    refine antitone_nat_of_succ_le fun N => ?_
    simp only [hw, Finset.sum_range_succ]
    linarith [hstep N]
  have hbdd : BddBelow (Set.range w) := by
    refine ⟨-∑' i, e i, ?_⟩
    rintro _ ⟨N, rfl⟩
    have := he.sum_le_tsum (Finset.range N) (fun i _ => he0 i)
    simp only [hw]
    linarith [hd0 N]
  have h1 := tendsto_atTop_ciInf hanti hbdd
  have h2 := he.hasSum.tendsto_sum_nat
  refine ⟨(⨅ N, w N) + ∑' i, e i, ?_⟩
  refine (h1.add h2).congr fun N => ?_
  simp only [hw]
  ring

theorem main {n m : ℕ} [NeZero m] (P : Problem n m) (hP : P.Standing) (A : Alg)
    (α : ℕ → ℝ) (hα : CyclicStepsize m α) (x z gF gH : ℕ → Vec n)
    (hrun : IsRun P A cyc α x z gF gH) (c : ℝ) (hA : AssumptionFor P A x z gF gH c)
    (hα0 : Tendsto α atTop (𝓝 0))
    (hαsum : Tendsto (fun N => ∑ k ∈ Finset.range N, α k) atTop atTop) :
    liminf (fun k => ((P.F (x k) : ℝ) : EReal)) atTop = P.Fstar ∧
    (P.Xstar.Nonempty → Summable (fun k => α k ^ 2) →
      ∃ xs ∈ P.Xstar, Tendsto x atTop (𝓝 xs)) := by
  have hm : 0 < m := NeZero.pos m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := assm_bound hA
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (hb 0).1
  set K : ℝ := 25 * c ^ 2 * m ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set u : ℕ → Vec n := fun N => x (m * (N + 1)) with hu_def
  set b : ℕ → ℝ := fun N => α (m * (N + 1)) with hb_def
  have hb0 : ∀ N, 0 < b N := fun N => hα.1 _
  have hidx : Tendsto (fun N : ℕ => m * (N + 1)) atTop atTop :=
    tendsto_atTop_mono (fun N => le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left (N + 1) hm))
      tendsto_id
  have hbt : Tendsto b atTop (𝓝 0) := hα0.comp hidx
  have hmem : ∀ N, u N ∈ P.X := fun N => run_mem hrun (by positivity)
  have hcyc : ∀ N, ∀ y ∈ P.X, ‖u (N + 1) - y‖ ^ 2 ≤
      ‖u N - y‖ ^ 2 - 2 * b N * (P.F (u N) - P.F y) + K * b N ^ 2 := by
    intro N y hy
    have := cycle_ineq hP hα hrun hA (k := m * (N + 1)) (by positivity)
      (Nat.mul_mod_right m (N + 1)) hy
    have e : m * (N + 1) + m = m * (N + 1 + 1) := by ring
    rw [e] at this
    simp only [hu_def, hb_def, hK]
    linarith
  -- block sums
  have hblock : ∀ M, ∑ k ∈ Finset.range (m * M), α k =
      m * ∑ N ∈ Finset.range M, α (m * N) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
      congr 1
      rw [Finset.sum_congr rfl fun i hi => alpha_const hα (Nat.mul_mod_right m M)
        (Finset.mem_range.1 hi)]
      simp
  have hbs : Tendsto (fun M => ∑ N ∈ Finset.range M, b N) atTop atTop := by
    have e : ∀ M, ∑ N ∈ Finset.range M, b N =
        (∑ k ∈ Finset.range (m * (M + 1)), α k) / m + (-α 0) := by
      intro M
      rw [hblock, Finset.sum_range_succ']
      simp only [hb_def, mul_zero]
      field_simp
      ring
    simp only [e]
    exact tendsto_atTop_add_const_right _ _
      (Tendsto.atTop_div_const hmR (hαsum.comp hidx))
  have hFs_le : ∀ v ∈ P.X, P.Fstar ≤ ((P.F v : ℝ) : EReal) := by
    intro v hv
    unfold Problem.Fstar
    exact iInf₂_le v hv
  constructor
  · apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      have hlt' : (⨅ v ∈ P.X, ((P.F v : ℝ) : EReal)) <
          liminf (fun k => ((P.F (x k) : ℝ) : EReal)) atTop := hlt
      obtain ⟨y, hy⟩ := iInf_lt_iff.1 hlt'
      obtain ⟨hyX, hy'⟩ := iInf_lt_iff.1 hy
      obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hy'
      have hr1' : P.F y < r := EReal.coe_lt_coe_iff.1 hr1
      obtain ⟨K0, hK0'⟩ := (Filter.eventually_lt_of_lt_liminf hr2).exists_forall_of_atTop
      refine desc_false (fun N => ‖u N - y‖ ^ 2) b (fun N => sq_nonneg _) hb0 hbt hbs
        (sub_pos.2 hr1') hK0 K0 fun N hN => ?_
      have h1 := hcyc N y hyX
      have hle : K0 ≤ m * (N + 1) :=
        le_trans hN (le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left (N + 1) hm))
      have h2 : r < P.F (u N) := EReal.coe_lt_coe_iff.1 (hK0' _ hle)
      have h3 := mul_le_mul_of_nonneg_left (show r - P.F y ≤ P.F (u N) - P.F y by linarith)
        (le_of_lt (mul_pos two_pos (hb0 N)))
      linarith
    · refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      exact hFs_le _ (run_mem hrun hk)
  · rintro ⟨y0, hy0X, hy0F⟩ hsq
    have hy0 : y0 ∈ P.Xstar := ⟨hy0X, hy0F⟩
    have hopt : ∀ y ∈ P.Xstar, ∀ v ∈ P.X, P.F y ≤ P.F v := by
      rintro y ⟨_, hyF⟩ v hv
      have := hFs_le v hv
      rw [← hyF] at this
      exact EReal.coe_le_coe_iff.1 this
    have hinj : Function.Injective (fun N : ℕ => m * (N + 1)) := by
      intro a a' h
      have := Nat.eq_of_mul_eq_mul_left hm h
      omega
    have hbsq : Summable (fun N => K * b N ^ 2) :=
      (hsq.comp_injective hinj).mul_left K
    have hFejer : ∀ y ∈ P.Xstar, ∃ ℓ, Tendsto (fun N => ‖u N - y‖ ^ 2) atTop (𝓝 ℓ) := by
      intro y hy
      refine qf_conv _ (fun N => K * b N ^ 2) (fun N => sq_nonneg _) (fun N => by positivity)
        hbsq fun N => ?_
      have h1 := hcyc N y hy.1
      have h2 := hopt y hy (u N) (hmem N)
      have h3 : 0 ≤ 2 * b N * (P.F (u N) - P.F y) :=
        mul_nonneg (by linarith [hb0 N]) (by linarith)
      linarith
    obtain ⟨ℓ0, hℓ0⟩ := hFejer y0 hy0
    obtain ⟨R, hR⟩ := hℓ0.bddAbove_range
    have hball : ∀ N, u N ∈ Metric.closedBall y0 (R + 1) := by
      intro N
      rw [mem_closedBall_iff_norm]
      have := hR ⟨N, rfl⟩
      nlinarith [norm_nonneg (u N - y0), sq_nonneg (‖u N - y0‖ - 1)]
    have hfreq : ∀ j : ℕ, ∃ᶠ N in atTop, P.F (u N) < P.F y0 + 1 / ((j : ℝ) + 1) := by
      intro j
      by_contra hcon
      rw [Filter.not_frequently] at hcon
      obtain ⟨N0, hN0⟩ := hcon.exists_forall_of_atTop
      have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      refine desc_false (fun N => ‖u N - y0‖ ^ 2) b (fun N => sq_nonneg _) hb0 hbt hbs hε hK0 N0
        fun N hN => ?_
      have h1 := hcyc N y0 hy0X
      have h2 := not_lt.1 (hN0 N hN)
      have h3 := mul_le_mul_of_nonneg_left
        (show 1 / ((j : ℝ) + 1) ≤ P.F (u N) - P.F y0 by linarith)
        (le_of_lt (mul_pos two_pos (hb0 N)))
      linarith
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_frequently hfreq
    obtain ⟨xb, -, ψ, hψ, hlim⟩ :=
      (isCompact_closedBall y0 (R + 1)).tendsto_subseq (fun j => hball (φ j))
    have hxbX : xb ∈ P.X :=
      hP.X_closed.mem_of_tendsto hlim (Eventually.of_forall fun j => hmem _)
    have hcf : ∀ i, Continuous (P.f i) := fun i =>
      continuousOn_univ.1 ((hP.f_convex i).continuousOn isOpen_univ)
    have hch : ∀ i, Continuous (P.h i) := fun i =>
      continuousOn_univ.1 ((hP.h_convex i).continuousOn isOpen_univ)
    have hFc : Continuous P.F := by
      have e : P.F = fun v => ∑ i, (P.f i v + P.h i v) := by
        funext v; rfl
      rw [e]
      exact continuous_finset_sum _ fun i _ => (hcf i).add (hch i)
    have hFxb : P.F xb = P.F y0 := by
      have t1 : Tendsto (fun j => P.F (u (φ (ψ j)))) atTop (𝓝 (P.F xb)) :=
        (hFc.tendsto xb).comp hlim
      have t2 : Tendsto (fun j => P.F (u (φ (ψ j)))) atTop (𝓝 (P.F y0)) := by
        have up : Tendsto (fun j : ℕ => P.F y0 + 1 / ((ψ j : ℝ) + 1)) atTop (𝓝 (P.F y0)) := by
          have := tendsto_const_nhds (x := P.F y0) |>.add
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop)
          rw [add_zero] at this
          exact this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds up ?_ ?_
        · intro j
          exact hopt y0 hy0 _ (hmem _)
        · intro j
          exact (hφP (ψ j)).le
      exact tendsto_nhds_unique t1 t2
    have hxbS : xb ∈ P.Xstar := ⟨hxbX, by rw [hFxb]; exact hy0F⟩
    obtain ⟨ℓ, hℓ⟩ := hFejer xb hxbS
    have hsub0 : Tendsto (fun j => ‖u (φ (ψ j)) - xb‖ ^ 2) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim).pow 2
      simpa using this
    have hℓz : ℓ = 0 := tendsto_nhds_unique (hℓ.comp (hφ.comp hψ).tendsto_atTop) hsub0
    rw [hℓz] at hℓ
    have hu : Tendsto u atTop (𝓝 xb) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h := (Real.continuous_sqrt.tendsto 0).comp hℓ
      rw [Real.sqrt_zero] at h
      refine h.congr fun N => ?_
      simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]
    refine ⟨xb, hxbS, ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hq : Tendsto (fun k : ℕ => k / m - 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro B
      refine ⟨(B + 1) * m, fun a ha => ?_⟩
      have : B + 1 ≤ a / m := (Nat.le_div_iff_mul_le hm).2 ha
      omega
    have h1 : Tendsto (fun k => ‖u (k / m - 1) - xb‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hu).comp hq
    have h2 : Tendsto (fun k => 4 * c * m * α k) atTop (𝓝 0) := by
      have := hα0.const_mul (4 * c * m)
      rw [mul_zero] at this
      exact this
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ h3
    filter_upwards [eventually_ge_atTop m] with k hk
    have hq1 : 1 ≤ k / m := (Nat.le_div_iff_mul_le hm).2 (by simpa using hk)
    have hu' : u (k / m - 1) = x (m * (k / m)) := by
      simp only [hu_def]
      congr 2
      omega
    have hk0pos : 0 < m * (k / m) := Nat.mul_pos hm hq1
    have hk0m : m * (k / m) % m = 0 := Nat.mul_mod_right _ _
    have hdr := drift hα hrun hb hk0pos hk0m (k % m) (Nat.mod_lt _ hm).le
    rw [Nat.div_add_mod k m] at hdr
    have hαk : α k = α (m * (k / m)) := hα.2 k
    have hr : ((k % m : ℕ) : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt _ hm).le
    have htri : ‖x k - xb‖ ≤ ‖x k - x (m * (k / m))‖ + ‖x (m * (k / m)) - xb‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hαc : 0 ≤ 4 * α (m * (k / m)) * c := by
      have := hα.1 (m * (k / m))
      positivity
    have hmul := mul_le_mul_of_nonneg_left hr hαc
    rw [hu', hαk]
    nlinarith

end IP6

open IncProx.Cyclic Filter Topology in
theorem solution {n m : ℕ} [NeZero m] (P : Problem n m) (hP : P.Standing) (A : Alg)
    (α : ℕ → ℝ) (hα : CyclicStepsize m α) (x z gF gH : ℕ → Vec n)
    (hrun : IsRun P A cyc α x z gF gH) (c : ℝ) (hA : AssumptionFor P A x z gF gH c)
    (hα0 : Tendsto α atTop (𝓝 0))
    (hαsum : Tendsto (fun N => ∑ k ∈ Finset.range N, α k) atTop atTop) :
    liminf (fun k => ((P.F (x k) : ℝ) : EReal)) atTop = P.Fstar ∧
    (P.Xstar.Nonempty → Summable (fun k => α k ^ 2) →
      ∃ xs ∈ P.Xstar, Tendsto x atTop (𝓝 xs)) := by
  exact IP6.main P hP A α hα x z gF gH hrun c hA hα0 hαsum
