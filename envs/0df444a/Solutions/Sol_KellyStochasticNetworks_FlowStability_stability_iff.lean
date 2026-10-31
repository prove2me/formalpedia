-- Prove2me | solution 1 for KellyStochasticNetworks.FlowStability.stability_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T04:32:04.055206+00:00
-- url     : https://prove2.me/submissions/d6b5f59e-ca97-47f1-85c0-3957a046fe23

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Process
import Definitions.Def_KLSModular_KolmogorovExtension4_KolmogorovExtension
import Theorems.Thm_KellyStochasticNetworks_FlowStability_generator_control
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_isProjectiveMeasureFamily_finiteSetLaw

/-!
Theorem 8.2 of Kelly--Yudovina: the alpha-fair flow-level process is positive recurrent
(equilibrium law plus stationary path law) iff the network is subcritical.

* `AFNec`  : an equilibrium distribution forces `sum_r A_jr rho_r < C_j` (flux balance with
             truncated route counts, positivity of the empty state).
* `AFSuf`  : Foster--Lyapunov drift (milestone `generator_control`) + Cesaro averages of the
             uniformized chain + sequential compactness give an invariant probability law.
* `AFPath` : the transition function forms a conservative kernel semigroup; mixing its
             finite-set laws over the equilibrium law gives a projective family, whose
             Kolmogorov extension realizes the stationary finite-dimensional laws.
-/

section

open scoped ENNReal
open KellyStochasticNetworks

namespace KellyStochasticNetworks.FlowStability.AFC

variable {J R : ℕ}

lemma feas {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) (n : State R) :
    (∀ r, 0 ≤ X n r) ∧ (∀ j, linkFlow D.A (X n) j ≤ D.C j) ∧
    (∀ r, n r = 0 → X n r = 0) ∧ (∀ r, 0 < n r → 0 < X n r) := by
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, -⟩ := hX n
  exact ⟨h1, h2, h3, h4⟩

lemma X_nonneg {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) (r : Fin R) : 0 ≤ X n r := (feas hX n).1 r

lemma X_le_sumC {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) (r : Fin R) : X n r ≤ ∑ j, D.C j := by
  obtain ⟨j, hj⟩ := D.route_nonempty r
  have h1 : X n r ≤ linkFlow D.A (X n) j := by
    unfold linkFlow
    have : X n r = D.A j r * X n r := by rw [hj, one_mul]
    rw [this]
    refine Finset.single_le_sum (f := fun r => D.A j r * X n r) (fun s _ => ?_) (Finset.mem_univ r)
    rcases D.incidence j s with h | h <;> simp [h, X_nonneg hX]
  have h2 : D.C j ≤ ∑ j, D.C j :=
    Finset.single_le_sum (fun i _ => (D.capacity_pos i).le) (Finset.mem_univ j)
  linarith [(feas hX n).2.1 j]

lemma clockRate_pos (D : Network J R) : 0 < clockRate D := by
  unfold clockRate
  have h1 : 0 ≤ ∑ r, D.nu r := Finset.sum_nonneg (fun r _ => (D.arrival_pos r).le)
  have h2 : 0 ≤ ∑ r, D.mu r := Finset.sum_nonneg (fun r _ => (D.service_pos r).le)
  have h3 : 0 ≤ ∑ j, D.C j := Finset.sum_nonneg (fun j _ => (D.capacity_pos j).le)
  nlinarith

/-- total jump rate out of n -/
noncomputable def outRate (D : Network J R) (X : State R → Fin R → ℝ) (n : State R) : ℝ :=
  (∑ r, D.nu r) + (∑ r, if 0 < n r then D.mu r * X n r else 0)

lemma outRate_nonneg {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) : 0 ≤ outRate D X n := by
  unfold outRate
  have h1 : 0 ≤ ∑ r, D.nu r := Finset.sum_nonneg (fun r _ => (D.arrival_pos r).le)
  have h2 : 0 ≤ ∑ r, (if 0 < n r then D.mu r * X n r else 0) :=
    Finset.sum_nonneg (fun r _ => by
      split_ifs
      · exact mul_nonneg (D.service_pos r).le (X_nonneg hX n r)
      · exact le_refl 0)
  linarith

lemma outRate_lt {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) : outRate D X n < clockRate D := by
  unfold outRate clockRate
  have : (∑ r, if 0 < n r then D.mu r * X n r else 0) ≤ (∑ r, D.mu r) * (∑ j, D.C j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun r _ => ?_)
    split_ifs
    · exact mul_le_mul_of_nonneg_left (X_le_sumC hX n r) (D.service_pos r).le
    · exact mul_nonneg (D.service_pos r).le
        (Finset.sum_nonneg (fun j _ => (D.capacity_pos j).le))
  linarith

lemma ofReal_sum_ite_div {ι S : Type*} [DecidableEq S] (s : Finset ι) (b : ι → S) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (c : ℝ) (hc : 0 < c) (m : S) :
    ENNReal.ofReal ((∑ i ∈ s, if m = b i then a i else 0) / c) =
      ∑ i ∈ s, if m = b i then ENNReal.ofReal (a i / c) else 0 := by
  rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  · intro i _
    split_ifs
    · exact div_nonneg (ha i) hc.le
    · simp

lemma tsum_sum_ite_mul {ι S : Type*} [DecidableEq S] (s : Finset ι) (b : ι → S)
    (x : ι → ℝ≥0∞) (f : S → ℝ≥0∞) :
    ∑' m, (∑ i ∈ s, if m = b i then x i else 0) * f m = ∑ i ∈ s, x i * f (b i) := by
  simp_rw [Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp_rw [ite_mul, zero_mul]
  exact tsum_ite_eq (b i) _

/-- the one-step expectation formula for the uniformized kernel -/
lemma step_tsum_mul {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) (f : State R → ℝ≥0∞) :
    ∑' m, step D X n m * f m =
      (∑ r, ENNReal.ofReal (D.nu r / clockRate D) * f (birth n r)) +
      (∑ r, (if 0 < n r then ENNReal.ofReal (D.mu r * X n r / clockRate D) else 0) *
        f (death n r)) +
      ENNReal.ofReal (1 - outRate D X n / clockRate D) * f n := by
  classical
  have hc := clockRate_pos D
  have e1 : ∀ m, ENNReal.ofReal ((∑ r, if m = birth n r then D.nu r else 0) / clockRate D) =
      ∑ r, if m = birth n r then ENNReal.ofReal (D.nu r / clockRate D) else 0 :=
    fun m => ofReal_sum_ite_div _ _ _ (fun r => (D.arrival_pos r).le) _ hc m
  have e2 : ∀ m, ENNReal.ofReal
      ((∑ r, if 0 < n r ∧ m = death n r then D.mu r * X n r else 0) / clockRate D) =
      ∑ r, if m = death n r then
        (if 0 < n r then ENNReal.ofReal (D.mu r * X n r / clockRate D) else 0) else 0 := by
    intro m
    have : (∑ r, if 0 < n r ∧ m = death n r then D.mu r * X n r else 0) =
        ∑ r, if m = death n r then (if 0 < n r then D.mu r * X n r else 0) else 0 := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      by_cases h1 : 0 < n r <;> by_cases h2 : m = death n r <;> simp [h1, h2]
    rw [this, ofReal_sum_ite_div]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      split_ifs <;> simp
    · intro r
      split_ifs
      · exact mul_nonneg (D.service_pos r).le (X_nonneg hX n r)
      · exact le_refl 0
    · exact hc
  have e3 : ∀ m, step D X n m =
      (∑ r, if m = birth n r then ENNReal.ofReal (D.nu r / clockRate D) else 0) +
      (∑ r, if m = death n r then
        (if 0 < n r then ENNReal.ofReal (D.mu r * X n r / clockRate D) else 0) else 0) +
      (if m = n then ENNReal.ofReal (1 - outRate D X n / clockRate D) else 0) := by
    intro m
    unfold step
    rw [e1, e2]
    rfl
  simp_rw [e3, add_mul]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_sum_ite_mul, tsum_sum_ite_mul]
  congr 1
  simp_rw [ite_mul, zero_mul]
  exact tsum_ite_eq n _

lemma step_tsum {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) : ∑' m, step D X n m = 1 := by
  have h := step_tsum_mul hX n (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  have hc := clockRate_pos D
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => div_nonneg (D.arrival_pos r).le hc.le)]
  have : (∑ r, (if 0 < n r then ENNReal.ofReal (D.mu r * X n r / clockRate D) else 0)) =
      ENNReal.ofReal (∑ r, if 0 < n r then D.mu r * X n r / clockRate D else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      split_ifs <;> simp
    · intro r _
      split_ifs
      · exact div_nonneg (mul_nonneg (D.service_pos r).le (X_nonneg hX n r)) hc.le
      · exact le_refl 0
  rw [this]
  have hlt := outRate_lt hX n
  have hnn := outRate_nonneg hX n
  have h1 : 0 ≤ 1 - outRate D X n / clockRate D := by
    rw [sub_nonneg, div_le_one hc]; exact hlt.le
  rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_one]
  · congr 1
    unfold outRate
    rw [← Finset.sum_div]
    have : (∑ r, if 0 < n r then D.mu r * X n r / clockRate D else 0) =
        (∑ r, if 0 < n r then D.mu r * X n r else 0) / clockRate D := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      split_ifs <;> simp
    rw [this]
    field_simp
    ring
  · exact add_nonneg (Finset.sum_nonneg (fun r _ => div_nonneg (D.arrival_pos r).le hc.le))
      (Finset.sum_nonneg (fun r _ => by
        split_ifs
        · exact div_nonneg (mul_nonneg (D.service_pos r).le (X_nonneg hX n r)) hc.le
        · exact le_refl 0))
  · exact h1
  · exact Finset.sum_nonneg (fun r _ => div_nonneg (D.arrival_pos r).le hc.le)
  · exact Finset.sum_nonneg (fun r _ => by
        split_ifs
        · exact div_nonneg (mul_nonneg (D.service_pos r).le (X_nonneg hX n r)) hc.le
        · exact le_refl 0)


lemma stepPower_zero_apply (D : Network J R) (X : State R → Fin R → ℝ) (n m : State R) :
    stepPower D X 0 n m = if n = m then 1 else 0 := rfl

lemma stepPower_succ_apply (D : Network J R) (X : State R → Fin R → ℝ) (k : ℕ) (n m : State R) :
    stepPower D X (k + 1) n m = ∑' z, step D X n z * stepPower D X k z m := rfl

lemma stepPower_add (D : Network J R) (X : State R → Fin R → ℝ) (a b : ℕ) (n m : State R) :
    stepPower D X (a + b) n m = ∑' z, stepPower D X a n z * stepPower D X b z m := by
  induction a generalizing n with
  | zero =>
    simp only [zero_add, stepPower_zero_apply, ite_mul, one_mul, zero_mul]
    rw [tsum_ite_eq']
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, stepPower_succ_apply]
    simp_rw [ih, stepPower_succ_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc]

lemma stepPower_tsum {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (k : ℕ) (n : State R) : ∑' m, stepPower D X k n m = 1 := by
  induction k generalizing n with
  | zero => simp only [stepPower_zero_apply]; rw [tsum_ite_eq']
  | succ k ih =>
    simp_rw [stepPower_succ_apply]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ih, mul_one]
    exact step_tsum hX n

/-- Poisson weight -/
noncomputable def pw (x : ℝ) (k : ℕ) : ℝ := Real.exp (-x) * x ^ k / (Nat.factorial k : ℝ)

lemma pw_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ pw x k := by
  unfold pw; positivity

lemma pw_hasSum (x : ℝ) : HasSum (fun k => pw x k) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-x))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have e : (fun k => pw x k) = fun i => Real.exp (-x) * (x ^ i / (i.factorial : ℝ)) := by
    funext k; unfold pw; ring
  rw [e]; exact h2

lemma pw_tsum_ennreal {x : ℝ} (hx : 0 ≤ x) : ∑' k, ENNReal.ofReal (pw x k) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (pw_nonneg hx) (pw_hasSum x).summable,
    (pw_hasSum x).tsum_eq, ENNReal.ofReal_one]

lemma pw_antidiag (x y : ℝ) (k : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, pw x p.1 * pw y p.2 = pw (x + y) k := by
  unfold pw
  rw [(Commute.all x y).add_pow', Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  subst hp
  have h := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
  have hc : ((p.1 + p.2).choose p.1 : ℝ) = ((p.1 + p.2).choose p.2 : ℝ) := by
    rw [Nat.choose_symm_add]
  have h' : ((p.1 + p.2).choose p.2 : ℝ) * (p.1.factorial : ℝ) * (p.2.factorial : ℝ) =
      ((p.1 + p.2).factorial : ℝ) := by exact_mod_cast h
  rw [nsmul_eq_mul, hc, neg_add, Real.exp_add]
  have h1 : (p.1.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (p.2.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((p.1 + p.2).choose p.2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left p.2 p.1)).ne'
  rw [← h']
  field_simp

lemma tsum_prod_antidiag (F : ℕ × ℕ → ℝ≥0∞) :
    ∑' p, F p = ∑' k, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, F p := by
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq, ENNReal.tsum_sigma']
  congr 1
  funext k
  exact Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal k) (fun p => F p)

lemma transition_eq (D : Network J R) (X : State R → Fin R → ℝ) (t : ℝ) (n m : State R) :
    transition D X t n m = ∑' k, ENNReal.ofReal (pw (clockRate D * t) k) * stepPower D X k n m :=
  rfl

lemma transition_zero (D : Network J R) (X : State R → Fin R → ℝ) (n m : State R) :
    transition D X 0 n m = if n = m then 1 else 0 := by
  rw [transition_eq, tsum_eq_single 0]
  · simp [pw, stepPower_zero_apply]
  · intro k hk
    simp [pw, zero_pow hk]

lemma transition_tsum {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    {t : ℝ} (ht : 0 ≤ t) (n : State R) : ∑' m, transition D X t n m = 1 := by
  simp_rw [transition_eq]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, stepPower_tsum hX, mul_one]
  exact pw_tsum_ennreal (mul_nonneg (clockRate_pos D).le ht)

lemma transition_add (D : Network J R) (X : State R → Fin R → ℝ) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (n m : State R) :
    ∑' z, transition D X s n z * transition D X t z m = transition D X (s + t) n m := by
  have hc := (clockRate_pos D).le
  simp_rw [transition_eq]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  have e : ∀ a b : ℕ, (∑' z, ENNReal.ofReal (pw (clockRate D * s) a) * stepPower D X a n z *
      (ENNReal.ofReal (pw (clockRate D * t) b) * stepPower D X b z m)) =
      ENNReal.ofReal (pw (clockRate D * s) a * pw (clockRate D * t) b) *
        stepPower D X (a + b) n m := by
    intro a b
    rw [stepPower_add, ← ENNReal.tsum_mul_left]
    congr 1
    funext z
    rw [ENNReal.ofReal_mul (pw_nonneg (mul_nonneg hc hs) a)]
    ring
  rw [show (∑' a, ∑' z, ∑' b, ENNReal.ofReal (pw (clockRate D * s) a) * stepPower D X a n z *
      (ENNReal.ofReal (pw (clockRate D * t) b) * stepPower D X b z m)) =
      ∑' a, ∑' b, ∑' z, ENNReal.ofReal (pw (clockRate D * s) a) * stepPower D X a n z *
      (ENNReal.ofReal (pw (clockRate D * t) b) * stepPower D X b z m) by
        congr 1; funext a; exact ENNReal.tsum_comm]
  simp_rw [e]
  rw [← ENNReal.tsum_prod (f := fun a b => ENNReal.ofReal (pw (clockRate D * s) a *
      pw (clockRate D * t) b) * stepPower D X (a + b) n m), tsum_prod_antidiag]
  congr 1
  funext k
  have : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k, ENNReal.ofReal (pw (clockRate D * s) p.1 *
      pw (clockRate D * t) p.2) * stepPower D X (p.1 + p.2) n m =
      ENNReal.ofReal (pw (clockRate D * s) p.1 * pw (clockRate D * t) p.2) *
      stepPower D X k n m := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [hp]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg, pw_antidiag,
    mul_add]
  intro p _
  exact mul_nonneg (pw_nonneg (mul_nonneg hc hs) _) (pw_nonneg (mul_nonneg hc ht) _)

end KellyStochasticNetworks.FlowStability.AFC

end

section

open scoped ENNReal
open KellyStochasticNetworks KellyStochasticNetworks.FlowStability
open KellyStochasticNetworks.FlowStability.AFC

namespace AFNec
variable {J R : ℕ}

lemma stepPower_one (D : Network J R) (X : State R → Fin R → ℝ) (n m : State R) :
    stepPower D X 1 n m = step D X n m := by
  rw [stepPower_succ_apply]
  simp only [stepPower_zero_apply, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq m (fun z => step D X n z)

lemma pi_le_one {R : ℕ} {pi : State R → ℝ≥0∞} (h : ∑' n, pi n = 1) (m : State R) :
    pi m ≤ 1 := h ▸ ENNReal.le_tsum m

lemma sub_inv {D : Network J R} {X : State R → Fin R → ℝ} {pi : State R → ℝ≥0∞}
    (hpi : IsEquilibrium D X pi) (m : State R) :
    ∑' n, pi n * step D X n m ≤ pi m := by
  set a1 := ∑' n, pi n * step D X n m with ha1
  have hpm : pi m ≤ 1 := pi_le_one hpi.1 m
  have hc := clockRate_pos D
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ENNReal.ofReal (Real.exp (-s)) * pi m + ENNReal.ofReal (Real.exp (-s) * s) * a1 ≤ pi m := by
    intro s hs0 hs1
    have ht : 0 ≤ s / clockRate D := div_nonneg hs0.le hc.le
    have hct : clockRate D * (s / clockRate D) = s := by field_simp
    have h := hpi.2 (s / clockRate D) ht m
    have hlow : ∀ n, ENNReal.ofReal (Real.exp (-s)) * (if n = m then 1 else 0) +
        ENNReal.ofReal (Real.exp (-s) * s) * step D X n m ≤
        transition D X (s / clockRate D) n m := by
      intro n
      rw [transition_eq, hct]
      have := ENNReal.sum_le_tsum (f := fun k => ENNReal.ofReal (pw s k) * stepPower D X k n m)
        (Finset.range 2)
      refine le_trans ?_ this
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, stepPower_zero_apply,
        stepPower_one]
      simp [pw]
    calc ENNReal.ofReal (Real.exp (-s)) * pi m + ENNReal.ofReal (Real.exp (-s) * s) * a1
        = ∑' n, pi n * (ENNReal.ofReal (Real.exp (-s)) * (if n = m then 1 else 0) +
            ENNReal.ofReal (Real.exp (-s) * s) * step D X n m) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ha1, ← ENNReal.tsum_mul_left]
          congr 1
          · simp only [mul_ite, mul_one, mul_zero]
            rw [tsum_ite_eq m (fun n => pi n * ENNReal.ofReal (Real.exp (-s)))]
            ring
          · congr 1; funext n; ring
      _ ≤ ∑' n, pi n * transition D X (s / clockRate D) n m :=
          ENNReal.tsum_le_tsum (fun n => mul_le_mul_right (hlow n) _)
      _ = pi m := h
  -- now pass to reals
  have hpm' : pi m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hpm
  have ha1' : a1 ≠ ⊤ := by
    intro htop
    have := key 1 one_pos le_rfl
    rw [htop, ENNReal.mul_top] at this
    · simp at this; exact hpm' this
    · simp [Real.exp_pos]
  set p := (pi m).toReal
  set a := a1.toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hpm; simpa using this
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have keyR : ∀ s : ℝ, 0 < s → s ≤ 1 → a ≤ p + s := by
    intro s hs0 hs1
    have h := key s hs0 hs1
    have h' := ENNReal.toReal_mono hpm' h
    rw [ENNReal.toReal_add (by simp [ENNReal.mul_ne_top, hpm']) (ENNReal.mul_ne_top (by simp) ha1'),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hs0.le)] at h'
    have he : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    have hb := Real.abs_exp_sub_one_sub_id_le (x := s) (by rw [abs_of_pos hs0]; exact hs1)
    have hb' : Real.exp s ≤ 1 + s + s ^ 2 := by
      have := (abs_le.mp hb).2; linarith
    have h2 : p + s * a ≤ Real.exp s * p := by
      have := mul_le_mul_of_nonneg_left h' (Real.exp_pos s).le
      calc p + s * a = Real.exp s * (Real.exp (-s) * p + Real.exp (-s) * s * a) := by
            rw [mul_add, ← mul_assoc, he, ← mul_assoc, ← mul_assoc, he]; ring
        _ ≤ Real.exp s * p := this
    have h3 : s * a ≤ s * ((1 + s) * p) := by nlinarith
    have h4 : a ≤ (1 + s) * p := le_of_mul_le_mul_left h3 hs0
    nlinarith
  have : a ≤ p := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have := keyR (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
    linarith [min_le_left ε 1]
  calc a1 = ENNReal.ofReal a := (ENNReal.ofReal_toReal ha1').symm
    _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal this
    _ = pi m := ENNReal.ofReal_toReal hpm'

lemma step_inv {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    {pi : State R → ℝ≥0∞} (hpi : IsEquilibrium D X pi) (m : State R) :
    ∑' n, pi n * step D X n m = pi m := by
  by_contra hne
  have hlt : ∑' n, pi n * step D X n m < pi m := lt_of_le_of_ne (sub_inv hpi m) hne
  have htot : ∑' m, ∑' n, pi n * step D X n m = 1 := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, step_tsum hX, mul_one]
    exact hpi.1
  have : ∑' m, ∑' n, pi n * step D X n m < ∑' m, pi m :=
    ENNReal.tsum_lt_tsum (by rw [htot]; exact ENNReal.one_ne_top) (fun m => sub_inv hpi m) hlt
  rw [htot, hpi.1] at this
  exact lt_irrefl _ this


lemma step_death_pos {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) (r : Fin R) (hr : 0 < n r) : 0 < step D X n (death n r) := by
  have hc := clockRate_pos D
  unfold step
  refine lt_of_lt_of_le ?_ (le_add_right (le_add_left le_rfl))
  rw [ENNReal.ofReal_pos]
  refine div_pos (lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun r' =>
      if 0 < n r' ∧ death n r = death n r' then D.mu r' * X n r' else 0) (fun r' _ => ?_)
      (Finset.mem_univ r))) hc
  · simp only [hr, true_and, if_true]
    exact mul_pos (D.service_pos r) ((feas hX n).2.2.2 r hr)
  · split_ifs
    · exact mul_nonneg (D.service_pos r').le (X_nonneg hX n r')
    · exact le_rfl

lemma pi_zero_pos {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    {pi : State R → ℝ≥0∞} (hpi : IsEquilibrium D X pi) : 0 < pi 0 := by
  obtain ⟨m, hm⟩ : ∃ m, pi m ≠ 0 := by
    by_contra h
    push Not at h
    have : ∑' n, pi n = 0 := by simp [h]
    rw [hpi.1] at this
    exact one_ne_zero this
  have main : ∀ N : ℕ, ∀ m : State R, (∑ r, m r) = N → 0 < pi m → 0 < pi 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro m hmN hpm
      by_cases h0 : m = 0
      · rw [← h0]; exact hpm
      · obtain ⟨r, hr⟩ : ∃ r, m r ≠ 0 := by
          by_contra h
          push Not at h
          exact h0 (funext h)
        have hr' : 0 < m r := Nat.pos_of_ne_zero hr
        have hlt : (∑ r', death m r r') < N := by
          rw [← hmN]
          refine Finset.sum_lt_sum (fun r' _ => ?_) ⟨r, Finset.mem_univ r, ?_⟩
          · unfold death
            by_cases h : r' = r
            · subst h; simp
            · simp [Function.update_of_ne h]
          · unfold death; simp; omega
        refine ih _ hlt (death m r) rfl ?_
        rw [← step_inv hX hpi (death m r)]
        exact lt_of_lt_of_le (ENNReal.mul_pos hpm.ne' (step_death_pos hX m r hr').ne')
          (ENNReal.le_tsum (f := fun n => pi n * step D X n (death m r)) m)
  exact main _ m rfl (pos_iff_ne_zero.mpr hm)

lemma flux_le {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    {pi : State R → ℝ≥0∞} (hpi : IsEquilibrium D X pi) (r : Fin R) :
    ENNReal.ofReal (D.nu r / clockRate D) ≤
      ∑' n, pi n * ENNReal.ofReal (D.mu r * X n r / clockRate D) := by
  classical
  set a := ENNReal.ofReal (D.nu r / clockRate D) with ha
  let B : State R → ℝ≥0∞ := fun n =>
    if 0 < n r then ENNReal.ofReal (D.mu r * X n r / clockRate D) else 0
  have hB : ∀ n, B n = ENNReal.ofReal (D.mu r * X n r / clockRate D) := by
    intro n
    simp only [B]
    split_ifs with h
    · rfl
    · have : X n r = 0 := (feas hX n).2.2.1 r (by omega)
      simp [this]
  have hK : ∀ K : ℕ, a * ∑' n, pi n * (if n r < K then 1 else 0) ≤ ∑' n, pi n * B n := by
    intro K
    let f : State R → ℝ≥0∞ := fun n => ((min (n r) K : ℕ) : ℝ≥0∞)
    have hf_le : ∀ n, f n ≤ K := fun n => by simp [f]
    -- pointwise identity
    have hid : ∀ n, (∑' m, step D X n m * f m) + (if n r ≤ K then B n else 0) =
        f n + (if n r < K then a else 0) := by
      intro n
      have h1 := step_tsum_mul hX n (fun _ => 1)
      simp only [mul_one] at h1
      rw [step_tsum hX n] at h1
      rw [step_tsum_mul hX n f]
      set A' : Fin R → ℝ≥0∞ := fun r' => ENNReal.ofReal (D.nu r' / clockRate D)
      set B' : Fin R → ℝ≥0∞ := fun r' =>
        if 0 < n r' then ENNReal.ofReal (D.mu r' * X n r' / clockRate D) else 0
      set H := ENNReal.ofReal (1 - outRate D X n / clockRate D)
      have e1 : (∑ r', A' r' * f (birth n r')) =
          (∑ r', A' r') * f n + (if n r < K then a else 0) := by
        rw [Finset.sum_mul]
        have : ∀ r', A' r' * f (birth n r') =
            A' r' * f n + (if r' = r then (if n r < K then a else 0) else 0) := by
          intro r'
          by_cases h : r' = r
          · subst h
            simp only [f, birth, Function.update_self, if_true]
            by_cases hk : n r' < K
            · rw [if_pos hk, show min (n r' + 1) K = min (n r') K + 1 by omega]
              push_cast; ring
            · rw [if_neg hk, show min (n r' + 1) K = min (n r') K by omega]; simp
          · simp only [f, birth, Function.update_of_ne (Ne.symm h), if_neg h, add_zero]
        rw [Finset.sum_congr rfl (fun r' _ => this r'), Finset.sum_add_distrib,
          Finset.sum_ite_eq']
        simp
      have e2 : (∑ r', B' r' * f (death n r')) + (if n r ≤ K then B n else 0) =
          (∑ r', B' r') * f n := by
        rw [Finset.sum_mul]
        have : ∀ r', B' r' * f (death n r') + (if r' = r then (if n r ≤ K then B n else 0)
            else 0) = B' r' * f n := by
          intro r'
          by_cases h : r' = r
          · subst h
            simp only [if_true]
            by_cases hp : 0 < n r'
            · simp only [B', B, if_pos hp, f, death, Function.update_self]
              by_cases hk : n r' ≤ K
              · rw [if_pos hk, show min (n r' - 1) K = min (n r') K - 1 by omega]
                obtain ⟨q, hq⟩ : ∃ q, min (n r') K = q + 1 := ⟨min (n r') K - 1, by omega⟩
                rw [hq, Nat.add_sub_cancel]; push_cast; ring
              · rw [if_neg hk, add_zero, show min (n r' - 1) K = min (n r') K by omega]
            · simp only [B', B, if_neg hp]; simp
          · simp only [f, death, if_neg h, add_zero]
            rw [Function.update_of_ne (Ne.symm h)]
        rw [← Finset.sum_congr rfl (fun r' _ => this r'), Finset.sum_add_distrib,
          Finset.sum_ite_eq']
        simp
      calc (∑ r', A' r' * f (birth n r')) + (∑ r', B' r' * f (death n r')) + H * f n +
            (if n r ≤ K then B n else 0)
          = (∑ r', A' r' * f (birth n r')) +
            ((∑ r', B' r' * f (death n r')) + (if n r ≤ K then B n else 0)) + H * f n := by ring
        _ = ((∑ r', A' r') * f n + (if n r < K then a else 0)) + (∑ r', B' r') * f n +
            H * f n := by rw [e1, e2]
        _ = ((∑ r', A' r') + (∑ r', B' r') + H) * f n + (if n r < K then a else 0) := by ring
        _ = f n + (if n r < K then a else 0) := by rw [← h1, one_mul]
    -- sum against pi
    have hsum : (∑' n, pi n * ∑' m, step D X n m * f m) = ∑' m, pi m * f m := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      congr 1; funext m
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right, step_inv hX hpi m]
    have hfin : (∑' m, pi m * f m) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∑' m, pi m * K) ?_ (ENNReal.tsum_le_tsum
        (fun m => mul_le_mul_right (hf_le m) _))
      rw [ENNReal.tsum_mul_right, hpi.1, one_mul]; exact ENNReal.natCast_ne_top K
    have htot : (∑' m, pi m * f m) + ∑' n, pi n * (if n r ≤ K then B n else 0) =
        (∑' m, pi m * f m) + a * ∑' n, pi n * (if n r < K then 1 else 0) := by
      rw [← hsum, ← ENNReal.tsum_add]
      simp_rw [← mul_add, hid, mul_add, ENNReal.tsum_add, hsum, ← ENNReal.tsum_mul_left]
      congr 2; funext n
      split_ifs <;> ring
    have := (ENNReal.add_right_inj hfin).mp htot
    rw [← this]
    exact ENNReal.tsum_le_tsum (fun n => mul_le_mul_right
      (show (if n r ≤ K then B n else 0) ≤ B n by split_ifs <;> simp) _)
  -- sup over K
  have hfinS : ∀ S : Finset (State R), a * ∑ n ∈ S, pi n ≤ ∑' n, pi n * B n := by
    intro S
    refine le_trans ?_ (hK (S.sup (fun n => n r) + 1))
    refine mul_le_mul_right ?_ _
    refine le_trans ?_ (ENNReal.sum_le_tsum S)
    refine Finset.sum_le_sum (fun n hn => ?_)
    have : n r < S.sup (fun n => n r) + 1 :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun n => n r) hn)
    simp [this]
  have : a * ∑' n, pi n ≤ ∑' n, pi n * B n := by
    rw [ENNReal.tsum_eq_iSup_sum, ENNReal.mul_iSup]
    exact iSup_le hfinS
  rw [hpi.1, mul_one] at this
  simpa [hB] using this

theorem subcritical_of_equilibrium (D : Network J R) (X : State R → Fin R → ℝ)
    (hX : IsAlphaFair D X) (pi : State R → ℝ≥0∞) (hpi : IsEquilibrium D X pi) :
    Subcritical D := by
  intro j
  have hc := clockRate_pos D
  -- per-route bound
  have hroute : ∀ r, ENNReal.ofReal (offeredLoad D r) ≤ ∑' n, pi n * ENNReal.ofReal (X n r) := by
    intro r
    have h := flux_le hX hpi r
    have e1 : ENNReal.ofReal (D.nu r / clockRate D) =
        ENNReal.ofReal (D.mu r / clockRate D) * ENNReal.ofReal (offeredLoad D r) := by
      rw [← ENNReal.ofReal_mul (div_nonneg (D.service_pos r).le hc.le)]
      congr 1; unfold offeredLoad; field_simp [(D.service_pos r).ne']
    have e2 : ∀ n, pi n * ENNReal.ofReal (D.mu r * X n r / clockRate D) =
        ENNReal.ofReal (D.mu r / clockRate D) * (pi n * ENNReal.ofReal (X n r)) := by
      intro n
      rw [show D.mu r * X n r / clockRate D = D.mu r / clockRate D * X n r by ring,
        ENNReal.ofReal_mul (div_nonneg (D.service_pos r).le hc.le)]
      ring
    simp_rw [e2] at h
    rw [ENNReal.tsum_mul_left, e1] at h
    exact (ENNReal.mul_le_mul_iff_right (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact div_pos (D.service_pos r) hc)
      ENNReal.ofReal_ne_top).mp h
  have hA : ∀ r, 0 ≤ D.A j r := fun r => by rcases D.incidence j r with h | h <;> simp [h]
  have hload : ENNReal.ofReal (linkFlow D.A (offeredLoad D) j) ≤
      ∑' n, pi n * ENNReal.ofReal (linkFlow D.A (X n) j) := by
    unfold linkFlow
    have hρ : ∀ r, 0 ≤ offeredLoad D r := fun r =>
      div_nonneg (D.arrival_pos r).le (D.service_pos r).le
    rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg (hA r) (hρ r))]
    have : ∀ n, ENNReal.ofReal (∑ r, D.A j r * X n r) =
        ∑ r, ENNReal.ofReal (D.A j r) * ENNReal.ofReal (X n r) := by
      intro n
      rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg (hA r) (X_nonneg hX n r))]
      exact Finset.sum_congr rfl (fun r _ => ENNReal.ofReal_mul (hA r))
    simp_rw [this, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_le_sum (fun r _ => ?_)
    rw [ENNReal.ofReal_mul (hA r)]
    have : (∑' n, pi n * (ENNReal.ofReal (D.A j r) * ENNReal.ofReal (X n r))) =
        ENNReal.ofReal (D.A j r) * ∑' n, pi n * ENNReal.ofReal (X n r) := by
      rw [← ENNReal.tsum_mul_left]; congr 1; funext n; ring
    rw [this]
    exact mul_le_mul_right (hroute r) _
  -- bound the expectation using the empty state
  have hzero : linkFlow D.A (X 0) j = 0 := by
    unfold linkFlow
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [(feas hX 0).2.2.1 r rfl, mul_zero]
  have hg : ∀ n, ENNReal.ofReal (linkFlow D.A (X n) j) +
      (if n = 0 then ENNReal.ofReal (D.C j) else 0) ≤ ENNReal.ofReal (D.C j) := by
    intro n
    by_cases h : n = 0
    · subst h; simp [hzero]
    · simp only [if_neg h, add_zero]
      exact ENNReal.ofReal_le_ofReal ((feas hX n).2.1 j)
  have hsum : (∑' n, pi n * ENNReal.ofReal (linkFlow D.A (X n) j)) +
      pi 0 * ENNReal.ofReal (D.C j) ≤ ENNReal.ofReal (D.C j) := by
    calc (∑' n, pi n * ENNReal.ofReal (linkFlow D.A (X n) j)) + pi 0 * ENNReal.ofReal (D.C j)
        = ∑' n, pi n * (ENNReal.ofReal (linkFlow D.A (X n) j) +
            (if n = 0 then ENNReal.ofReal (D.C j) else 0)) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add]
          congr 1
          simp only [mul_ite, mul_zero]
          rw [tsum_ite_eq]
      _ ≤ ∑' n, pi n * ENNReal.ofReal (D.C j) :=
          ENNReal.tsum_le_tsum (fun n => mul_le_mul_right (hg n) _)
      _ = ENNReal.ofReal (D.C j) := by rw [ENNReal.tsum_mul_right, hpi.1, one_mul]
  have hpos : 0 < pi 0 * ENNReal.ofReal (D.C j) :=
    ENNReal.mul_pos (pi_zero_pos hX hpi).ne' (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact D.capacity_pos j)
  have hlt : ENNReal.ofReal (linkFlow D.A (offeredLoad D) j) < ENNReal.ofReal (D.C j) := by
    have hE : (∑' n, pi n * ENNReal.ofReal (linkFlow D.A (X n) j)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hsum)
    calc ENNReal.ofReal (linkFlow D.A (offeredLoad D) j)
        ≤ ∑' n, pi n * ENNReal.ofReal (linkFlow D.A (X n) j) := hload
      _ < (∑' n, pi n * ENNReal.ofReal (linkFlow D.A (X n) j)) + pi 0 * ENNReal.ofReal (D.C j) :=
          ENNReal.lt_add_right hE hpos.ne'
      _ ≤ ENNReal.ofReal (D.C j) := hsum
  exact (ENNReal.ofReal_lt_ofReal_iff (D.capacity_pos j)).mp hlt

end AFNec

end

section

open scoped ENNReal
open Filter Topology
open KellyStochasticNetworks KellyStochasticNetworks.FlowStability
open KellyStochasticNetworks.FlowStability.AFC

namespace AFSuf
variable {J R : ℕ}

lemma lyap_nonneg (D : Network J R) (n : State R) : 0 ≤ lyapunov D n := by
  unfold lyapunov
  refine Finset.sum_nonneg (fun r _ => ?_)
  have hρ : 0 < offeredLoad D r := div_pos (D.arrival_pos r) (D.service_pos r)
  have ha := D.alpha_pos
  refine mul_nonneg (mul_nonneg (div_nonneg (D.weight_pos r).le (D.service_pos r).le)
    (Real.rpow_nonneg hρ.le _)) (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_)
  linarith

lemma lyap_zero (D : Network J R) : lyapunov D 0 = 0 := by
  unfold lyapunov
  refine Finset.sum_eq_zero (fun r _ => ?_)
  have : D.alpha + 1 ≠ 0 := by linarith [D.alpha_pos]
  simp [Real.zero_rpow this]

lemma PV_real {D : Network J R} {X : State R → Fin R → ℝ} (n : State R) :
    lyapunov D n + generator D X (lyapunov D) n / clockRate D =
      (∑ r, D.nu r / clockRate D * lyapunov D (birth n r)) +
      (∑ r, if 0 < n r then D.mu r * X n r / clockRate D * lyapunov D (death n r) else 0) +
      (1 - outRate D X n / clockRate D) * lyapunov D n := by
  have hc := (clockRate_pos D).ne'
  set V := lyapunov D
  set c := clockRate D
  have e1 : generator D X V n / c = ∑ r, (D.nu r / c * (V (birth n r) - V n) +
      if 0 < n r then D.mu r * X n r / c * (V (death n r) - V n) else 0) := by
    unfold generator
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split_ifs <;> field_simp <;> simp
  have e2 : outRate D X n / c * V n = ∑ r, (D.nu r / c * V n +
      if 0 < n r then D.mu r * X n r / c * V n else 0) := by
    unfold outRate
    rw [add_div, add_mul, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div,
      Finset.sum_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split_ifs <;> simp
  rw [e1, sub_mul, one_mul, e2, ← Finset.sum_add_distrib]
  have e3 : ∀ r, (D.nu r / c * (V (birth n r) - V n) +
      if 0 < n r then D.mu r * X n r / c * (V (death n r) - V n) else 0) =
      (D.nu r / c * V (birth n r) +
        if 0 < n r then D.mu r * X n r / c * V (death n r) else 0) -
      (D.nu r / c * V n + if 0 < n r then D.mu r * X n r / c * V n else 0) := by
    intro r; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun r _ => e3 r), Finset.sum_sub_distrib]
  ring

lemma PV_nonneg {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) : 0 ≤ lyapunov D n + generator D X (lyapunov D) n / clockRate D := by
  have hc := clockRate_pos D
  rw [PV_real]
  refine add_nonneg (add_nonneg (Finset.sum_nonneg (fun r _ => ?_))
    (Finset.sum_nonneg (fun r _ => ?_))) (mul_nonneg ?_ (lyap_nonneg D n))
  · exact mul_nonneg (div_nonneg (D.arrival_pos r).le hc.le) (lyap_nonneg D _)
  · split_ifs
    · exact mul_nonneg (div_nonneg (mul_nonneg (D.service_pos r).le (X_nonneg hX n r)) hc.le)
        (lyap_nonneg D _)
    · exact le_rfl
  · rw [sub_nonneg, div_le_one hc]; exact (outRate_lt hX n).le

lemma PV_eq {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n : State R) :
    ∑' m, step D X n m * ENNReal.ofReal (lyapunov D m) =
      ENNReal.ofReal (lyapunov D n + generator D X (lyapunov D) n / clockRate D) := by
  have hc := clockRate_pos D
  rw [step_tsum_mul hX n, PV_real]
  have h1 : 0 ≤ 1 - outRate D X n / clockRate D := by
    rw [sub_nonneg, div_le_one hc]; exact (outRate_lt hX n).le
  have t1 : (∑ r, ENNReal.ofReal (D.nu r / clockRate D) * ENNReal.ofReal (lyapunov D (birth n r)))
      = ENNReal.ofReal (∑ r, D.nu r / clockRate D * lyapunov D (birth n r)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg
      (div_nonneg (D.arrival_pos r).le hc.le) (lyap_nonneg D _))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ENNReal.ofReal_mul (div_nonneg (D.arrival_pos r).le hc.le)]
  have t2 : (∑ r, (if 0 < n r then ENNReal.ofReal (D.mu r * X n r / clockRate D) else 0) *
      ENNReal.ofReal (lyapunov D (death n r))) = ENNReal.ofReal
      (∑ r, if 0 < n r then D.mu r * X n r / clockRate D * lyapunov D (death n r) else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      split_ifs
      · rw [ENNReal.ofReal_mul (div_nonneg (mul_nonneg (D.service_pos r).le (X_nonneg hX n r))
          hc.le)]
      · simp
    · intro r _
      split_ifs
      · exact mul_nonneg (div_nonneg (mul_nonneg (D.service_pos r).le (X_nonneg hX n r)) hc.le)
          (lyap_nonneg D _)
      · exact le_rfl
  have s1 : 0 ≤ ∑ r, D.nu r / clockRate D * lyapunov D (birth n r) :=
    Finset.sum_nonneg (fun r _ => mul_nonneg
      (div_nonneg (D.arrival_pos r).le hc.le) (lyap_nonneg D _))
  have s2 : 0 ≤ ∑ r, (if 0 < n r then D.mu r * X n r / clockRate D * lyapunov D (death n r)
      else 0) := Finset.sum_nonneg (fun r _ => by
      split_ifs
      · exact mul_nonneg (div_nonneg (mul_nonneg (D.service_pos r).le (X_nonneg hX n r)) hc.le)
          (lyap_nonneg D _)
      · exact le_rfl)
  have s3 : 0 ≤ (1 - outRate D X n / clockRate D) * lyapunov D n :=
    mul_nonneg h1 (lyap_nonneg D n)
  rw [t1, t2, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
  all_goals linarith

lemma drift_bound {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (hS : Subcritical D) : ∃ ε' : ℝ≥0∞, 0 < ε' ∧ ∃ (F : Finset (State R)) (β : ℝ≥0∞),
      β ≠ ⊤ ∧ ∀ n, (∑' m, step D X n m * ENNReal.ofReal (lyapunov D m)) + ε' ≤
        ENNReal.ofReal (lyapunov D n) + (if n ∈ F then β else 0) := by
  classical
  have hc := clockRate_pos D
  obtain ⟨-, h2⟩ := generator_control D X hX
  obtain ⟨ε, hε, K, b, hb⟩ := h2 hS
  let F : Finset (State R) := (Fintype.piFinset (fun _ : Fin R => Finset.range (K + 1))).filter
    (fun n => (∑ r, n r) ≤ K)
  have hF : ∀ n, n ∈ F ↔ (∑ r, n r) ≤ K := by
    intro n
    simp only [F, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, and_iff_right_iff_imp]
    intro h r
    have := Finset.single_le_sum (f := fun r => n r) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    omega
  refine ⟨ENNReal.ofReal (ε / clockRate D), ENNReal.ofReal_pos.mpr (div_pos hε hc), F,
    ENNReal.ofReal (max b 0 / clockRate D), ENNReal.ofReal_ne_top, fun n => ?_⟩
  rw [PV_eq hX n, ← ENNReal.ofReal_add (PV_nonneg hX n) (div_nonneg hε.le hc.le)]
  have hg := hb n
  have key : lyapunov D n + generator D X (lyapunov D) n / clockRate D + ε / clockRate D ≤
      lyapunov D n + (if n ∈ F then max b 0 / clockRate D else 0) := by
    by_cases h : (∑ r, n r) ≤ K
    · rw [if_pos ((hF n).mpr h)]; rw [if_pos h] at hg
      have : generator D X (lyapunov D) n + ε ≤ max b 0 := by
        have := le_max_left b 0; linarith
      have := div_le_div_of_nonneg_right this hc.le
      rw [add_div] at this; linarith
    · rw [if_neg (fun h' => h ((hF n).mp h'))]; rw [if_neg h] at hg
      have : generator D X (lyapunov D) n + ε ≤ 0 := by linarith
      have := div_le_div_of_nonneg_right this hc.le
      rw [add_div, zero_div] at this; linarith
  refine le_trans (ENNReal.ofReal_le_ofReal key) ?_
  rw [ENNReal.ofReal_add (lyap_nonneg D n) (by split_ifs <;> positivity)]
  split_ifs <;> simp


lemma stepPower_one (D : Network J R) (X : State R → Fin R → ℝ) (n m : State R) :
    stepPower D X 1 n m = step D X n m := by
  rw [stepPower_succ_apply]
  simp only [stepPower_zero_apply, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq m (fun z => step D X n z)

lemma step_le_one {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    (n m : State R) : step D X n m ≤ 1 :=
  step_tsum hX n ▸ ENNReal.le_tsum (f := fun m => step D X n m) m

noncomputable def mu (D : Network J R) (X : State R → Fin R → ℝ) (k : ℕ) (m : State R) :
    ℝ≥0∞ := stepPower D X k 0 m

lemma mu_succ (D : Network J R) (X : State R → Fin R → ℝ) (k : ℕ) (m : State R) :
    mu D X (k + 1) m = ∑' z, mu D X k z * step D X z m := by
  unfold mu; rw [stepPower_add]; simp_rw [stepPower_one]

lemma mu_tsum {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) (k : ℕ) :
    ∑' m, mu D X k m = 1 := stepPower_tsum hX k 0

lemma cesaro {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    {ε' β : ℝ≥0∞} {F : Finset (State R)}
    (hdrift : ∀ n, (∑' m, step D X n m * ENNReal.ofReal (lyapunov D m)) + ε' ≤
        ENNReal.ofReal (lyapunov D n) + (if n ∈ F then β else 0)) (N : ℕ) :
    (∑' m, mu D X N m * ENNReal.ofReal (lyapunov D m)) + (N : ℝ≥0∞) * ε' ≤
      β * ∑ k ∈ Finset.range N, ∑ m ∈ F, mu D X k m := by
  classical
  induction N with
  | zero =>
    simp only [mu, stepPower_zero_apply, Nat.cast_zero, zero_mul, add_zero, Finset.range_zero,
      Finset.sum_empty, mul_zero, ite_mul, one_mul, zero_mul]
    rw [tsum_ite_eq', lyap_zero]; simp
  | succ N ih =>
    have hE : (∑' m, mu D X (N + 1) m * ENNReal.ofReal (lyapunov D m)) =
        ∑' z, mu D X N z * ∑' m, step D X z m * ENNReal.ofReal (lyapunov D m) := by
      simp_rw [mu_succ, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc]
    have h1 : (∑' m, mu D X (N + 1) m * ENNReal.ofReal (lyapunov D m)) + ε' ≤
        (∑' m, mu D X N m * ENNReal.ofReal (lyapunov D m)) + β * ∑ m ∈ F, mu D X N m := by
      rw [hE]
      calc (∑' z, mu D X N z * ∑' m, step D X z m * ENNReal.ofReal (lyapunov D m)) + ε'
          = ∑' z, mu D X N z * ((∑' m, step D X z m * ENNReal.ofReal (lyapunov D m)) + ε') := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, mu_tsum hX, one_mul]
        _ ≤ ∑' z, mu D X N z * (ENNReal.ofReal (lyapunov D z) + (if z ∈ F then β else 0)) :=
            ENNReal.tsum_le_tsum (fun z => mul_le_mul_right (hdrift z) _)
        _ = (∑' m, mu D X N m * ENNReal.ofReal (lyapunov D m)) + β * ∑ m ∈ F, mu D X N m := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add]
            congr 1
            rw [tsum_eq_sum (s := F) (fun z hz => by simp [hz]), Finset.mul_sum]
            refine Finset.sum_congr rfl (fun z hz => ?_)
            simp [hz, mul_comm]
    rw [Finset.sum_range_succ, mul_add]
    calc (∑' m, mu D X (N + 1) m * ENNReal.ofReal (lyapunov D m)) + ((N + 1 : ℕ) : ℝ≥0∞) * ε'
        = ((∑' m, mu D X (N + 1) m * ENNReal.ofReal (lyapunov D m)) + ε') + (N : ℝ≥0∞) * ε' := by
          push_cast; ring
      _ ≤ ((∑' m, mu D X N m * ENNReal.ofReal (lyapunov D m)) + β * ∑ m ∈ F, mu D X N m) +
            (N : ℝ≥0∞) * ε' := add_le_add_left h1 _
      _ = ((∑' m, mu D X N m * ENNReal.ofReal (lyapunov D m)) + (N : ℝ≥0∞) * ε') +
            β * ∑ m ∈ F, mu D X N m := by ring
      _ ≤ β * ∑ k ∈ Finset.range N, ∑ m ∈ F, mu D X k m + β * ∑ m ∈ F, mu D X N m :=
          add_le_add_left ih _

/-- Cesaro averages -/
noncomputable def nu (D : Network J R) (X : State R → Fin R → ℝ) (n : ℕ) (m : State R) :
    ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range (n + 1), mu D X k m

lemma nu_tsum {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) (n : ℕ) :
    ∑' m, nu D X n m = 1 := by
  unfold nu
  rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [mu_tsum hX]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

lemma nu_sub_inv {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) (n : ℕ)
    (m : State R) :
    ∑' z, nu D X n z * step D X z m ≤ nu D X n m + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold nu
  have e : (∑' z, ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (∑ k ∈ Finset.range (n + 1), mu D X k z) *
      step D X z m) = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), mu D X (k + 1) m := by
    simp_rw [mul_assoc, Finset.sum_mul]
    rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [mu_succ]
  rw [e]
  have hle : ∑ k ∈ Finset.range (n + 1), mu D X (k + 1) m ≤
      (∑ k ∈ Finset.range (n + 1), mu D X k m) + 1 := by
    have h2 := Finset.sum_range_succ' (fun k => mu D X k m) (n + 1)
    have h3 := Finset.sum_range_succ (fun k => mu D X k m) (n + 1)
    have hmu : mu D X (n + 1) m ≤ 1 := mu_tsum hX (n + 1) ▸ ENNReal.le_tsum m
    calc ∑ k ∈ Finset.range (n + 1), mu D X (k + 1) m
        ≤ ∑ k ∈ Finset.range (n + 1), mu D X (k + 1) m + mu D X 0 m := le_self_add
      _ = ∑ k ∈ Finset.range (n + 1 + 1), mu D X k m := h2.symm
      _ = ∑ k ∈ Finset.range (n + 1), mu D X k m + mu D X (n + 1) m := h3
      _ ≤ (∑ k ∈ Finset.range (n + 1), mu D X k m) + 1 := add_le_add_right hmu _
  calc ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range (n + 1), mu D X (k + 1) m
      ≤ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((∑ k ∈ Finset.range (n + 1), mu D X k m) + 1) :=
        mul_le_mul_right hle _
    _ = _ := by rw [mul_add, mul_one]

theorem exists_equilibrium_of_subcritical (D : Network J R) (X : State R → Fin R → ℝ)
    (hX : IsAlphaFair D X) (hS : Subcritical D) : ∃ pi, IsEquilibrium D X pi := by
  classical
  obtain ⟨ε', hε', F, β, hβ, hdrift⟩ := drift_bound hX hS
  -- lower bound on the mass of F
  have hlow : ∀ n : ℕ, ε' / β ≤ ∑ m ∈ F, nu D X n m := by
    intro n
    have h := cesaro hX hdrift (n + 1)
    have h' : ((n + 1 : ℕ) : ℝ≥0∞) * ε' ≤ β * ∑ k ∈ Finset.range (n + 1), ∑ m ∈ F, mu D X k m :=
      le_trans le_add_self h
    unfold nu
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h'' : ((n + 1 : ℕ) : ℝ≥0∞) * ε' / β ≤
        ∑ k ∈ Finset.range (n + 1), ∑ m ∈ F, mu D X k m := by
      apply ENNReal.div_le_of_le_mul; exact h'.trans_eq (mul_comm _ _)
    calc ε' / β = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((n + 1 : ℕ) : ℝ≥0∞) * ε' / β) := by
          rw [mul_div_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
      _ ≤ _ := mul_le_mul_right h'' _
  have hδ : 0 < ε' / β := ENNReal.div_pos_iff.mpr ⟨hε'.ne', hβ⟩
  -- subsequence
  obtain ⟨ν, φ, hφ, hlim⟩ := SeqCompactSpace.tendsto_subseq (fun n => nu D X n)
  have hpt : ∀ m, Tendsto (fun n => nu D X (φ n) m) atTop (𝓝 (ν m)) := fun m =>
    tendsto_pi_nhds.mp hlim m
  have hsumS : ∀ (S : Finset (State R)), Tendsto (fun n => ∑ m ∈ S, nu D X (φ n) m) atTop
      (𝓝 (∑ m ∈ S, ν m)) := fun S => tendsto_finsetSum S (fun m _ => hpt m)
  have hνS : ∀ S : Finset (State R), ∑ m ∈ S, ν m ≤ 1 := by
    intro S
    refine le_of_tendsto' (hsumS S) (fun n => ?_)
    rw [← nu_tsum hX (φ n)]
    exact ENNReal.sum_le_tsum S
  have hνtot : ∑' m, ν m ≤ 1 := by
    rw [ENNReal.tsum_eq_iSup_sum]; exact iSup_le hνS
  have hν1 : ∀ m, ν m ≤ 1 := fun m => le_trans (ENNReal.le_tsum m) hνtot
  have hνF : ε' / β ≤ ∑ m ∈ F, ν m := ge_of_tendsto' (hsumS F) (fun n => hlow (φ n))
  -- sub-invariance of the limit
  have hinvN : Tendsto (fun n => ((φ n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero
    exact h1.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
  have hsub : ∀ m, ∑' z, ν z * step D X z m ≤ ν m := by
    intro m
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun S => ?_)
    have hl : Tendsto (fun n => ∑ z ∈ S, nu D X (φ n) z * step D X z m) atTop
        (𝓝 (∑ z ∈ S, ν z * step D X z m)) := tendsto_finsetSum S (fun z _ =>
          ENNReal.Tendsto.mul_const (hpt z) (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top
            (step_le_one hX z m))))
    have hr : Tendsto (fun n => nu D X (φ n) m + ((φ n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop
        (𝓝 (ν m + 0)) := (hpt m).add hinvN
    rw [add_zero] at hr
    refine le_of_tendsto_of_tendsto' hl hr (fun n => ?_)
    exact le_trans (ENNReal.sum_le_tsum S) (nu_sub_inv hX (φ n) m)
  have hinv : ∀ m, ∑' z, ν z * step D X z m = ν m := by
    intro m
    by_contra hne
    have hlt : ∑' z, ν z * step D X z m < ν m := lt_of_le_of_ne (hsub m) hne
    have htot : ∑' m, ∑' z, ν z * step D X z m = ∑' m, ν m := by
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left, step_tsum hX, mul_one]
    have : ∑' m, ∑' z, ν z * step D X z m < ∑' m, ν m :=
      ENNReal.tsum_lt_tsum (by rw [htot]; exact ne_top_of_le_ne_top ENNReal.one_ne_top hνtot)
        (fun m => hsub m) hlt
    rw [htot] at this
    exact lt_irrefl _ this
  -- normalize
  set s := ∑' m, ν m with hs
  have hs0 : s ≠ 0 := by
    intro h0
    have : ∑ m ∈ F, ν m ≤ s := ENNReal.sum_le_tsum F
    rw [h0] at this
    exact (lt_of_lt_of_le hδ (le_trans hνF this)).ne' rfl
  have hstop : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hνtot
  refine ⟨fun m => ν m * s⁻¹, ?_, ?_⟩
  · rw [ENNReal.tsum_mul_right, ← hs, ENNReal.mul_inv_cancel hs0 hstop]
  · -- invariance under the step powers, then under the transition function
    have hstepinv : ∀ m, ∑' z, ν z * s⁻¹ * step D X z m = ν m * s⁻¹ := by
      intro m
      simp_rw [mul_right_comm _ s⁻¹]
      rw [ENNReal.tsum_mul_right, hinv m]
    have hpow : ∀ k m, ∑' n, ν n * s⁻¹ * stepPower D X k n m = ν m * s⁻¹ := by
      intro k
      induction k with
      | zero =>
        intro m
        simp only [stepPower_zero_apply, mul_ite, mul_one, mul_zero]
        exact tsum_ite_eq m (fun n => ν n * s⁻¹)
      | succ k ih =>
        intro m
        simp_rw [stepPower_add, stepPower_one, ← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ih]
        exact hstepinv m
    intro t ht m
    simp_rw [transition_eq, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    have : ∀ k, ∑' n, ν n * s⁻¹ * (ENNReal.ofReal (pw (clockRate D * t) k) *
        stepPower D X k n m) = ENNReal.ofReal (pw (clockRate D * t) k) * (ν m * s⁻¹) := by
      intro k
      rw [← hpow k m, ← ENNReal.tsum_mul_left]
      congr 1; funext n; ring
    simp_rw [this]
    rw [ENNReal.tsum_mul_right, pw_tsum_ennreal (mul_nonneg (clockRate_pos D).le ht), one_mul]

end AFSuf

end

section

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory
open KellyStochasticNetworks KellyStochasticNetworks.FlowStability
open KellyStochasticNetworks.FlowStability.AFC

namespace AFPath
variable {J R : ℕ}

noncomputable def tmeas (D : Network J R) (X : State R → Fin R → ℝ) (t : ℝ) (x : State R) :
    Measure (State R) :=
  Measure.sum (fun m => transition D X t x m • Measure.dirac m)

lemma tmeas_apply (D : Network J R) (X : State R → Fin R → ℝ) (t : ℝ) (x : State R)
    (s : Set (State R)) :
    tmeas D X t x s = ∑' m, transition D X t x m * s.indicator 1 m := by
  unfold tmeas
  rw [Measure.sum_apply _ (Set.to_countable s).measurableSet]
  congr 1; funext m
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma tmeas_singleton (D : Network J R) (X : State R → Fin R → ℝ) (t : ℝ) (x m : State R) :
    tmeas D X t x {m} = transition D X t x m := by
  rw [tmeas_apply, tsum_eq_single m]
  · simp
  · intro b hb; simp [hb]

noncomputable def tker (D : Network J R) (X : State R → Fin R → ℝ) (t : ℝ≥0) :
    Kernel (State R) (State R) :=
  ⟨tmeas D X t, measurable_of_countable _⟩

lemma tker_apply (D : Network J R) (X : State R → Fin R → ℝ) (t : ℝ≥0) (x : State R) :
    tker D X t x = tmeas D X t x := rfl

lemma measurable_transition (D : Network J R) (X : State R → Fin R → ℝ) (m : State R) :
    Measurable (fun p : ℝ≥0 × State R => transition D X (p.1 : ℝ) p.2 m) := by
  refine measurable_from_prod_countable_left (fun y => ?_)
  simp_rw [transition_eq]
  refine Measurable.ennreal_tsum (fun k => Measurable.mul_const ?_ _)
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  unfold pw
  fun_prop

noncomputable def sg {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) :
    MarkovProcess.SubMarkovKernelSemigroup (State R) where
  kernel := tker D X
  measurable_kernel := by
    refine Measure.measurable_of_measurable_coe _ (fun s _ => ?_)
    simp_rw [tker_apply, tmeas_apply]
    exact Measurable.ennreal_tsum (fun m => (measurable_transition D X m).mul_const _)
  kernel_zero := by
    ext1 x
    rw [Kernel.id_apply, tker_apply]
    refine Measure.ext_of_singleton (fun m => ?_)
    rw [tmeas_singleton, NNReal.coe_zero, transition_zero, Measure.dirac_apply]
    by_cases h : x = m <;> simp [h, Set.indicator]
  kernel_add := by
    intro s t
    ext1 x
    refine Measure.ext_of_singleton (fun m => ?_)
    rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton m), tker_apply, tmeas_singleton,
      tker_apply]
    simp_rw [tker_apply, tmeas_singleton]
    unfold tmeas
    rw [lintegral_sum_measure]
    simp_rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [NNReal.coe_add, ← transition_add D X s.coe_nonneg t.coe_nonneg]
  isSubMarkovKernel := by
    intro t x
    rw [tker_apply, tmeas_apply]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    rw [transition_tsum hX t.coe_nonneg]

lemma sg_apply {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) (t : ℝ≥0)
    (x m : State R) : sg hX t x {m} = transition D X t x m := by
  show tker D X t x {m} = _
  rw [tker_apply, tmeas_singleton]

lemma sg_conservative {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) :
    (sg hX).IsConservative := by
  intro t x
  show tker D X t x Set.univ = 1
  rw [tker_apply, tmeas_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [transition_tsum hX t.coe_nonneg]


open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup in
lemma ftk_singleton (P : MarkovProcess.SubMarkovKernelSemigroup (State R))
    (hP : P.IsConservative) : ∀ (m : ℕ) (τ : MarkovProcess.FiniteOrderedTimes (m + 1)) (x : State R)
    (path : Fin (m + 1) → State R),
    finiteTimeKernel P τ x {path} = P (τ 0) x {path 0} *
      ∏ i : Fin m, P (τ i.succ - τ i.castSucc) (path i.castSucc) {path i.succ} := by
  intro m
  induction m with
  | zero =>
    intro τ x path
    have : IsMarkovKernel (P (τ 0)) := hP.isMarkovKernel (τ 0)
    have : IsMarkovKernel (finiteTimeKernel P τ.relativeTail) :=
      hP.isMarkovKernel_finiteTimeKernel P τ.relativeTail
    rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
      Kernel.map_apply' _ measurable_finCons _ (measurableSet_singleton _)]
    have hpre : (fun z : State R × (Fin 0 → State R) =>
        @Fin.cons 0 (fun _ => State R) z.1 z.2) ⁻¹' {path} =
        {path 0} ×ˢ {Fin.tail path} := by
      ext ⟨a, q⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
      constructor
      · intro h; subst h; simp
      · rintro ⟨h1, h2⟩; subst h1; subst h2; exact Fin.cons_self_tail path
    rw [hpre, Kernel.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      lintegral_singleton, Kernel.prodMkLeft_apply]
    simp only [finiteTimeKernel_zero, Kernel.const_apply, Finset.univ_eq_empty,
      Finset.prod_empty, mul_one]
    rw [Measure.dirac_apply]
    have : Fin.tail path = MarkovProcess.FiniteOrderedTimes.emptyPath (State R) :=
      Subsingleton.elim _ _
    simp [this]
  | succ m ih =>
    intro τ x path
    have : IsMarkovKernel (P (τ 0)) := hP.isMarkovKernel (τ 0)
    have : IsMarkovKernel (finiteTimeKernel P τ.relativeTail) :=
      hP.isMarkovKernel_finiteTimeKernel P τ.relativeTail
    rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
      Kernel.map_apply' _ measurable_finCons _ (measurableSet_singleton _)]
    have hpre : (fun z : State R × (Fin (m + 1) → State R) =>
        @Fin.cons (m + 1) (fun _ => State R) z.1 z.2) ⁻¹' {path} =
        {path 0} ×ˢ {Fin.tail path} := by
      ext ⟨a, q⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
      constructor
      · intro h; subst h; simp
      · rintro ⟨h1, h2⟩; subst h1; subst h2; exact Fin.cons_self_tail path
    rw [hpre, Kernel.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      lintegral_singleton, Kernel.prodMkLeft_apply, ih, Fin.prod_univ_succ]
    have h0 : τ.relativeTail 0 = τ (Fin.succ 0) - τ 0 := rfl
    have hi : ∀ i : Fin m, τ.relativeTail i.succ - τ.relativeTail i.castSucc =
        τ i.succ.succ - τ i.succ.castSucc := by
      intro i
      simp only [MarkovProcess.FiniteOrderedTimes.relativeTail_apply]
      rw [tsub_tsub_tsub_cancel_right (τ.monotone (Fin.zero_le _))]
      rfl
    simp only [h0, hi, Fin.tail]
    have e : ∀ i : Fin m, path i.castSucc.succ = path i.succ.castSucc := fun i => rfl
    simp only [e, Fin.castSucc_zero]
    ring


open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup in
lemma fsl_singleton_aux (P : MarkovProcess.SubMarkovKernelSemigroup (State R))
    (I : Finset ℝ≥0) (x : State R) (z : I → State R) :
    ∀ (n : ℕ) (hn : I.card = n) (τ : FiniteOrderedTimes n) (hτ : ∀ i, τ i ∈ I),
    finiteTimeKernel P (finiteSetTimes I) x (orderedPathToFiniteSet I ⁻¹' {z}) =
      finiteTimeKernel P τ x {fun i => z ⟨τ i, hτ i⟩} := by
  intro n hn τ hτ
  subst hn
  have hτe : τ = I.orderEmbOfFin rfl := Finset.orderEmbOfFin_unique' rfl hτ
  subst hτe
  congr 1
  ext path
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    rw [← h]
    simp only [orderedPathToFiniteSet]
    congr 1
    apply (I.orderIsoOfFin rfl).injective
    rw [OrderIso.apply_symm_apply]
    apply Subtype.ext
    rfl
  · intro h
    funext t
    rw [h]
    simp only [orderedPathToFiniteSet]
    congr 1
    apply Subtype.ext
    simp only
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup in
lemma fsl_singleton (P : MarkovProcess.SubMarkovKernelSemigroup (State R))
    (I : Finset ℝ≥0) (x : State R) (z : I → State R) (n : ℕ) (hn : I.card = n)
    (τ : FiniteOrderedTimes n) (hτ : ∀ i, τ i ∈ I) :
    finiteSetLaw P I x {z} = finiteTimeKernel P τ x {fun i => z ⟨τ i, hτ i⟩} := by
  unfold finiteSetLaw
  rw [finiteSetKernel_eq_map, Kernel.map_apply' _ (measurable_orderedPathToFiniteSet I) _
    (measurableSet_singleton _)]
  exact fsl_singleton_aux P I x z n hn τ hτ

/-- The finite-dimensional family of the stationary process. -/
noncomputable def Qfam (P : MarkovProcess.SubMarkovKernelSemigroup (State R))
    (pi : State R → ℝ≥0∞) (I : Finset ℝ≥0) : Measure (I → State R) :=
  Measure.sum (fun x => pi x • MarkovProcess.SubMarkovKernelSemigroup.finiteSetLaw P I x)

lemma Qfam_proj (P : MarkovProcess.SubMarkovKernelSemigroup (State R)) (hP : P.IsConservative)
    (pi : State R → ℝ≥0∞) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => State R) (Qfam P pi) := by
  intro I J hJI
  unfold Qfam
  rw [Measure.map_sum (Finset.measurable_restrict₂ (X := fun _ : ℝ≥0 => State R) hJI).aemeasurable]
  congr 1
  funext x
  rw [Measure.map_smul]
  congr 1
  exact MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProjectiveMeasureFamily_finiteSetLaw
    P hP x I J hJI

lemma Qfam_prob (P : MarkovProcess.SubMarkovKernelSemigroup (State R)) (hP : P.IsConservative)
    (pi : State R → ℝ≥0∞) (hpi : ∑' x, pi x = 1) (I : Finset ℝ≥0) :
    IsProbabilityMeasure (Qfam P pi I) := by
  constructor
  unfold Qfam
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have : IsMarkovKernel (MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P I) :=
    MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteSetKernel P hP I
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [MarkovProcess.SubMarkovKernelSemigroup.finiteSetLaw, measure_univ, mul_one]
  exact hpi


lemma fdd_strict {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    {pi : State R → ℝ≥0∞} (hpi : IsEquilibrium D X pi)
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => State R) (Qfam (sg hX) pi))
    [∀ I, IsFiniteMeasure (Qfam (sg hX) pi I)]
    (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (ht : StrictMono t) (y : Fin (k + 1) → State R) :
    projectiveLimit (Qfam (sg hX) pi) hQ {ω : ℝ≥0 → State R | ∀ i, ω (t i) = y i} =
      pi (y 0) * ∏ i : Fin k, transition D X ((t i.succ : ℝ) - (t i.castSucc : ℝ))
        (y i.castSucc) (y i.succ) := by
  classical
  set I : Finset ℝ≥0 := Finset.univ.image t with hIdef
  have hI : I.card = k + 1 := by
    rw [Finset.card_image_of_injective _ ht.injective]; simp
  let τ : MarkovProcess.FiniteOrderedTimes (k + 1) := OrderEmbedding.ofStrictMono t ht
  have hτ : ∀ i, τ i ∈ I := fun i => Finset.mem_image_of_mem t (Finset.mem_univ i)
  let z : I → State R := fun s => y (Classical.choose (Finset.mem_image.mp s.2))
  have hz : ∀ i, z ⟨t i, hτ i⟩ = y i := by
    intro i
    have h := Classical.choose_spec (Finset.mem_image.mp (hτ i))
    simp only [z]
    congr 1
    exact ht.injective h.2
  have hset : {ω : ℝ≥0 → State R | ∀ i, ω (t i) = y i} =
      cylinder (α := fun _ : ℝ≥0 => State R) I {z} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_cylinder, Set.mem_singleton_iff]
    constructor
    · intro h
      funext s
      obtain ⟨s, hs⟩ := s
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hs
      subst hi
      simp only [Finset.restrict]
      rw [hz, h i]
    · intro h i
      have := congrFun h ⟨t i, hτ i⟩
      simp only [Finset.restrict] at this
      rw [this, hz]
  rw [hset, (isProjectiveLimit_projectiveLimit hQ).measure_cylinder I (measurableSet_singleton _)]
  unfold Qfam
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hzy : (fun i => z ⟨τ i, hτ i⟩) = y := funext hz
  have e : ∀ x, MarkovProcess.SubMarkovKernelSemigroup.finiteSetLaw (sg hX) I x {z} =
      transition D X (t 0) x (y 0) * ∏ i : Fin k, transition D X ((t i.succ : ℝ) -
        (t i.castSucc : ℝ)) (y i.castSucc) (y i.succ) := by
    intro x
    rw [fsl_singleton (sg hX) I x z (k + 1) hI τ hτ, hzy,
      ftk_singleton (sg hX) (sg_conservative hX) k τ x y, sg_apply]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [sg_apply]
    congr 1
    exact NNReal.coe_sub (ht.monotone (Fin.castSucc_lt_succ (i := i)).le)
  simp_rw [e, ← mul_assoc]
  rw [ENNReal.tsum_mul_right, hpi.2 (t 0) (t 0).coe_nonneg (y 0)]

lemma prod_remove {α : Type*} [DecidableEq α] (g : ℝ → α → α → ℝ≥0∞)
    (hg : ∀ a b, g 0 a b = if a = b then 1 else 0) (k : ℕ) (t : Fin (k + 2) → ℝ≥0)
    (y : Fin (k + 2) → α) (i : Fin (k + 1)) (hti : t i.castSucc = t i.succ) :
    ∏ j : Fin (k + 1), g ((t j.succ : ℝ) - t j.castSucc) (y j.castSucc) (y j.succ) =
      if y i.castSucc = y i.succ then
        ∏ j : Fin k, g ((t (i.succ.succAbove j.succ) : ℝ) - t (i.succ.succAbove j.castSucc))
          (y (i.succ.succAbove j.castSucc)) (y (i.succ.succAbove j.succ))
      else 0 := by
  rw [Fin.prod_univ_succAbove _ i, hti, sub_self, hg]
  split_ifs with hy
  · rw [one_mul]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rcases lt_or_ge j.val i.val with h | h
    · have e1 : i.succAbove j = j.castSucc :=
        Fin.succAbove_of_castSucc_lt i j (by rw [Fin.lt_def]; simp; omega)
      have e2 : i.succ.succAbove j.succ = j.succ.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)
      have e3 : i.succ.succAbove j.castSucc = j.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)
      have e4 : j.castSucc.succ = j.succ.castSucc := Fin.ext (by simp)
      rw [e1, e2, e3, e4]
    · have e1 : i.succAbove j = j.succ :=
        Fin.succAbove_of_le_castSucc i j (by rw [Fin.le_def]; simp; omega)
      have e2 : i.succ.succAbove j.succ = j.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)
      rw [e1, e2]
      rcases eq_or_lt_of_le h with h' | h'
      · have e3 : i.succ.succAbove j.castSucc = i.castSucc := by
          rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
          exact Fin.ext (by simp; omega)
        have e4 : j.succ.castSucc = i.succ := Fin.ext (by simp; omega)
        rw [e3, e4, hti, hy]
      · have e3 : i.succ.succAbove j.castSucc = j.castSucc.succ :=
          Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)
        have e4 : j.castSucc.succ = j.succ.castSucc := Fin.ext (by simp)
        rw [e3, e4]
  · rw [zero_mul]

lemma set_remove {α : Type*} [DecidableEq α] (k : ℕ) (t : Fin (k + 2) → ℝ≥0) (y : Fin (k + 2) → α)
    (i : Fin (k + 1)) (hti : t i.castSucc = t i.succ) :
    {ω : ℝ≥0 → α | ∀ j, ω (t j) = y j} =
      if y i.castSucc = y i.succ then
        {ω : ℝ≥0 → α | ∀ j : Fin (k + 1), ω (t (i.succ.succAbove j)) = y (i.succ.succAbove j)}
      else ∅ := by
  have hcs : i.succ.succAbove i = i.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp)
  split_ifs with hy
  · ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h j; exact h _
    · intro h m
      by_cases hm : m = i.succ
      · subst hm
        have := h i
        rw [hcs, hti] at this
        rw [this, hy]
      · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
        exact h m'
  · ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    apply hy
    rw [← h i.castSucc, ← h i.succ, hti]


lemma fdd_mono {D : Network J R} {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X)
    {pi : State R → ℝ≥0∞} (hpi : IsEquilibrium D X pi)
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => State R) (Qfam (sg hX) pi))
    [∀ I, IsFiniteMeasure (Qfam (sg hX) pi I)] :
    ∀ (k : ℕ) (t : Fin (k + 1) → ℝ≥0), Monotone t → ∀ y : Fin (k + 1) → State R,
    projectiveLimit (Qfam (sg hX) pi) hQ {ω : ℝ≥0 → State R | ∀ i, ω (t i) = y i} =
      pi (y 0) * ∏ i : Fin k, transition D X ((t i.succ : ℝ) - (t i.castSucc : ℝ))
        (y i.castSucc) (y i.succ) := by
  intro k
  induction k with
  | zero =>
    intro t _ y
    refine fdd_strict hX hpi hQ 0 t (fun a b hab => ?_) y
    exfalso
    rw [Fin.lt_def] at hab
    have ha := a.2; have hb := b.2
    omega
  | succ k ih =>
    intro t ht y
    by_cases hs : StrictMono t
    · exact fdd_strict hX hpi hQ (k + 1) t hs y
    · rw [Fin.strictMono_iff_lt_succ] at hs
      push Not at hs
      obtain ⟨i, hi⟩ := hs
      have hti : t i.castSucc = t i.succ :=
        le_antisymm (ht (Fin.castSucc_lt_succ (i := i)).le) hi
      rw [set_remove k t y i hti,
        prod_remove (transition D X) (transition_zero D X) k t y i hti]
      split_ifs with hy
      · have hmono : Monotone (t ∘ i.succ.succAbove) :=
          ht.comp (Fin.strictMono_succAbove _).monotone
        have := ih (t ∘ i.succ.succAbove) hmono (y ∘ i.succ.succAbove)
        simp only [Function.comp] at this
        rw [this, Fin.succ_succAbove_zero]
      · simp

theorem exists_stationaryPathLaw (D : Network J R) (X : State R → Fin R → ℝ)
    (hX : IsAlphaFair D X) (pi : State R → ℝ≥0∞) (hpi : IsEquilibrium D X pi) :
    ∃ P : Measure (Path R), IsStationaryPathLaw D X pi P := by
  have hQ := Qfam_proj (sg hX) (sg_conservative hX) pi
  have hprob : ∀ I, IsProbabilityMeasure (Qfam (sg hX) pi I) :=
    Qfam_prob (sg hX) (sg_conservative hX) pi hpi.1
  refine ⟨projectiveLimit (Qfam (sg hX) pi) hQ, isProbabilityMeasure_projectiveLimit hQ, ?_⟩
  intro k t ht y
  exact fdd_mono hX hpi hQ k t ht y

end AFPath

end

open KellyStochasticNetworks.FlowStability in
theorem solution {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X) :
    PositiveRecurrent D X ↔ Subcritical D := by
  constructor
  · rintro ⟨pi, hpi, -⟩
    exact AFNec.subcritical_of_equilibrium D X hX pi hpi
  · intro hS
    obtain ⟨pi, hpi⟩ := AFSuf.exists_equilibrium_of_subcritical D X hX hS
    obtain ⟨P, hP⟩ := AFPath.exists_stationaryPathLaw D X hX pi hpi
    exact ⟨pi, hpi, P, hP⟩
