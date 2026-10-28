-- Prove2me | solution 1 for OAI.SharpTerminalLeave.sharp_terminal_leave
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:00:44.417616+00:00
-- url     : https://prove2.me/submissions/ddb9efaf-6868-4498-be82-7eb1a29eea0b

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000
import Theorems.Thm_OAI_SharpTerminalLeave_main_l2_prefix_failure_bound
import Theorems.Thm_OAI_SharpTerminalLeave_prefix_good_history

section
-- module Solutions.OAIQ4_Tr.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_LogStepSandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave

lemma log_step_sandwich {p q h : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : p = q+h) :
    h/p ≤ Real.log p-Real.log q ∧ Real.log p-Real.log q ≤ h/q := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have hu := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at hl
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)] at hu
  have he₁ : q/p-1 = -(h/p) := by field_simp; linarith only [hs]
  have he₂ : p/q-1 = h/q := by field_simp; linarith only [hs]
  rw [he₁] at hl
  rw [he₂] at hu
  exact ⟨by linarith only [hl],hu⟩

theorem density_log_sum_bounds (p : ℕ → ℝ) (h : ℝ) (T : ℕ)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, h/p i) ≤ Real.log (p 0)-Real.log (p T) ∧
    Real.log (p 0)-Real.log (p T) ≤
      (∑ i ∈ Finset.range T, h/p i)+(h/p T-h/p 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
    obtain ⟨hl,hu⟩ := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    obtain ⟨sl,su⟩ := log_step_sandwich (hp T (by omega)) (hp (T+1) le_rfl) (hs T (by omega))
    rw [Finset.sum_range_succ]
    constructor <;> linarith only [hl,hu,sl,su]

lemma inverse_square_grid_step {a p q h : ℝ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hh : 0 ≤ h) (hs : p = q+h) :
    2*h/(a*p^3) ≤ 1/(a*q^2)-1/(a*p^2) := by
  have hpq : q ≤ p := by linarith only [hs,hh]
  have hc : 2*q^2 ≤ p*(p+q) := by nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (by linarith : 0 ≤ p+2*q)]
  have hm := mul_le_mul_of_nonneg_left hc hh
  have he : p^2-q^2 = h*(p+q) := by rw [hs]; ring
  apply (div_le_iff₀ (mul_pos ha (pow_pos hp 3))).mpr
  have hd : (1/(a*q^2)-1/(a*p^2))*(a*p^3) = (p^2-q^2)*p/q^2 := by
    field_simp
  rw [hd,he]
  apply (le_div_iff₀ (pow_pos hq 2)).mpr
  nlinarith only [hm]

theorem inverse_square_grid_sum (p : ℕ → ℝ) (a h : ℝ) (T : ℕ)
    (ha : 0 < a) (hh : 0 ≤ h) (hp : ∀ i ≤ T, 0 < p i)
    (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, 2*h/(a*p i^3)) ≤ 1/(a*p T^2)-1/(a*p 0^2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hi := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    have hstep := inverse_square_grid_step ha (hp T (by omega)) (hp (T+1) le_rfl) hh (hs T (by omega))
    rw [Finset.sum_range_succ]
    linarith only [hi,hstep]

theorem density_survival_exponent_bound (p : ℕ → ℝ) (a h b η : ℝ) (T : ℕ)
    (ha : 0 < a) (hh : 0 ≤ h) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+h)
    (hp0 : p 0 ≤ 1) :
    (∑ i ∈ Finset.range T, (-b*(h/p i)+2*b*η*(h/p i)+b^2*(2*h/(a*p i^3)))) ≤
      b*Real.log (p T)+b*(1-p 0)/p 0+b*h/p T+
        2*b*η*(-Real.log (p T))+b^2/(a*p T^2) := by
  obtain ⟨hloglo,hloghi⟩ := density_log_sum_bounds p h T hp hs
  have hinv := inverse_square_grid_sum p a h T ha hh hp hs
  have hln0 : Real.log (p 0) ≤ 0 := Real.log_nonpos (hp 0 (Nat.zero_le _)).le hp0
  have hlninit : -Real.log (p 0) ≤ (1-p 0)/p 0 := by
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr (hp 0 (Nat.zero_le _)))
    rw [Real.log_inv] at hi
    have he : (p 0)⁻¹-1 = (1-p 0)/p 0 := by
      field_simp [ne_of_gt (hp 0 (Nat.zero_le _))]
    rwa [he] at hi
  have h₁ := mul_le_mul_of_nonneg_left hloghi hb
  have h₂ := mul_le_mul_of_nonneg_left hloglo (show 0 ≤ 2*b*η by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hinv (sq_nonneg b)
  have h₄ := mul_le_mul_of_nonneg_left hlninit hb
  have h₅ := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2*b*η by positivity) hln0
  have hpzero := hp 0 (Nat.zero_le _)
  have h₆ : 0 ≤ b*h/p 0 := by positivity
  have h₇ : 0 ≤ b^2/(a*p 0^2) := by positivity
  have he : (∑ i ∈ Finset.range T, (-b*(h/p i)+2*b*η*(h/p i)+b^2*(2*h/(a*p i^3)))) =
      -b*(∑ i ∈ Finset.range T, h/p i)+2*b*η*(∑ i ∈ Finset.range T, h/p i)+
        b^2*(∑ i ∈ Finset.range T, 2*h/(a*p i^3)) := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [he]
  simp only [mul_sub,mul_add] at h₁ h₂ h₃
  simp only [div_eq_mul_inv] at h₁ h₂ h₃ h₄ h₆ h₇ ⊢
  nlinarith only [h₁,h₂,h₃,h₄,h₅,h₆,h₇]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a + g a) = pmfMean p f + pmfMean p g := by
  simp only [pmfMean, mul_add, Finset.sum_add_distrib]

theorem pmfMean_sub {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a - g a) = pmfMean p f - pmfMean p g := by
  simp only [pmfMean, mul_sub, Finset.sum_sub_distrib]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_const_mul {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfMean p (fun a => c * f a) = c * pmfMean p f := by
  simpa only [mul_comm] using pmfMean_mul_const p f c

theorem pmfMean_nonneg {α : Type*} [Fintype α] (p : PMF α) {f : α → ℝ}
    (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ pmfMean p f := by
  apply Finset.sum_nonneg
  intro a _
  by_cases ha : a ∈ p.support
  · exact mul_nonneg ENNReal.toReal_nonneg (h a ha)
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) : pmfMean p f ≤ pmfMean p g := by
  have hh := pmfMean_nonneg p (fun a ha => sub_nonneg.mpr (h a ha))
  rwa [pmfMean_sub, sub_nonneg] at hh

theorem pmfMean_sq_sub {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => (f a - c) ^ 2) =
      pmfMean p (fun a => f a ^ 2) - 2 * c * pmfMean p f + c ^ 2 := by
  have hpoly : (fun a => (f a - c) ^ 2) =
      (fun a => (f a ^ 2 - (2 * c) * f a) + c ^ 2) := by
    funext a
    ring
  rw [hpoly, pmfMean_add, pmfMean_sub, pmfMean_const_mul, pmfMean_const]

theorem pmfMean_sq_le {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    (pmfMean p f) ^ 2 ≤ pmfMean p (fun a => f a ^ 2) := by
  have h := pmfMean_nonneg p
    (fun a (_ : a ∈ p.support) => sq_nonneg (f a - pmfMean p f))
  rw [pmfMean_sq_sub] at h
  nlinarith

theorem pmfMean_markov_sq {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    pmfMean p (fun a => if ε < |f a| then 1 else 0) ≤
      pmfMean p (fun a => f a ^ 2) / ε ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [← pmfMean_mul_const]
  apply pmfMean_mono
  intro a _
  split_ifs with ha
  · simp only [one_mul]
    exact sq_le_sq.mpr (by rw [abs_of_pos hε]; exact le_of_lt ha)
  · simp only [zero_mul]
    exact sq_nonneg _

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_MarkovLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_exp_le {α : Type*} [Fintype α] (p : PMF α)
    (X : α → ℝ) (c v lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ a ∈ p.support, |X a| ≤ c)
    (hmean : pmfMean p X ≤ 0) (hvar : pmfMean p (fun a => X a ^ 2) ≤ v) :
    pmfMean p (fun a => Real.exp (lam * X a)) ≤ Real.exp (lam ^ 2 * v) := by
  have hpt (a : α) (ha : a ∈ p.support) :
      Real.exp (lam * X a) ≤ 1 + lam * X a + lam ^ 2 * X a ^ 2 := by
    have hb : |lam * X a| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlam]
      exact (mul_le_mul_of_nonneg_left (hbounded a ha) hlam).trans hclam
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hb)).2
    nlinarith
  calc
    _ ≤ pmfMean p (fun a => (1 + lam * X a) + lam ^ 2 * X a ^ 2) :=
      pmfMean_mono p hpt
    _ = 1 + lam * pmfMean p X + lam ^ 2 * pmfMean p (fun a => X a ^ 2) := by
      rw [pmfMean_add, pmfMean_add, pmfMean_const, pmfMean_const_mul,
        pmfMean_const_mul]
    _ ≤ 1 + lam ^ 2 * v := by
      have hs := mul_le_mul_of_nonneg_left hmean hlam
      have hv := mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
      nlinarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (lam ^ 2 * v)

theorem markovMean_potential_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (Z : ℕ → α → ℝ)
    (hstep : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (Z (k + 1)) ≤ Z k a) (k : ℕ) :
    pmfMean (markovLaw initial K k) (Z k) ≤ pmfMean initial (Z 0) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [markovLaw, pmfMean_bind]
    exact (pmfMean_mono _ (hstep k)).trans ih

theorem markovMean_exp_compensated_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c lam : ℝ)
    (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) :
    pmfMean (markovLaw initial K k)
      (fun a => Real.exp (lam * X k a - lam ^ 2 * V k a)) ≤
      pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) := by
  apply markovMean_potential_le initial K
    (fun k a => Real.exp (lam * X k a - lam ^ 2 * V k a))
  intro j a ha
  have hmgf := pmfMean_exp_le (K j a) (fun b => X (j + 1) b - X j a)
    c (incrementVar j a) lam hlam hclam (hbounded j a ha) (hmean j a ha) (hvar j a ha)
  have heq : pmfMean (K j a) (fun b => Real.exp (lam * X (j + 1) b - lam ^ 2 * V (j + 1) b)) =
      Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        pmfMean (K j a) (fun b => Real.exp (lam * (X (j + 1) b - X j a))) := by
    rw [← pmfMean_const_mul]
    apply pmfMean_congr
    intro b hb
    rw [hcounter j a ha b hb, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        Real.exp (lam ^ 2 * incrementVar j a) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pmfMean_compensated_tail {α : Type*} [Fintype α] (p : PMF α)
    (X V : α → ℝ) (lam r v : ℝ) (hlam : 0 ≤ lam)
    (hmgf : pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) ≤ 1) :
    pmfMean p (fun a => if r ≤ X a ∧ V a ≤ v then 1 else 0) ≤
      Real.exp (-lam * r + lam ^ 2 * v) := by
  classical
  have hevent (a : α) :
      (if r ≤ X a ∧ V a ≤ v then (1 : ℝ) else 0) ≤
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v) := by
    split_ifs with ha
    · rw [← Real.exp_add, Real.one_le_exp_iff]
      have hx := mul_le_mul_of_nonneg_left ha.1 hlam
      have hv := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg lam)
      linarith
    · positivity
  calc
    _ ≤ pmfMean p (fun a =>
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v)) :=
      pmfMean_mono p (fun a _ => hevent a)
    _ = pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) *
        Real.exp (-lam * r + lam ^ 2 * v) := pmfMean_mul_const _ _ _
    _ ≤ 1 * Real.exp (-lam * r + lam ^ 2 * v) :=
      mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = _ := one_mul _

theorem finite_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c : ℝ) (hc : 0 < c)
    (hinitial : ∀ a ∈ initial.support, X 0 a ≤ 0 ∧ 0 ≤ V 0 a)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) (r v : ℝ) (hr : 0 < r) (hv : 0 ≤ v) :
    pmfMean (markovLaw initial K k)
      (fun a => if r ≤ X k a ∧ V k a ≤ v then 1 else 0) ≤
      Real.exp (-r ^ 2 / (4 * (v + c * r))) := by
  classical
  let A : ℝ := v + c * r
  have hA : 0 < A := by dsimp [A]; positivity
  let lam : ℝ := r / (2 * A)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hclam : lam * c ≤ 1 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_pos hc hr]
  have hmgf := markovMean_exp_compensated_le initial K X V incrementVar c lam hlam hclam
    hbounded hmean hvar hcounter k
  have hi : pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) ≤ 1 := by
    rw [← pmfMean_const initial 1]
    apply pmfMean_mono
    intro a ha
    apply Real.exp_le_one_iff.mpr
    obtain ⟨hx, hv⟩ := hinitial a ha
    have hx' := mul_le_mul_of_nonneg_left hx hlam
    have hv' := mul_nonneg (sq_nonneg lam) hv
    linarith
  have hhalf : lam * v ≤ r / 2 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_nonneg hc.le (sq_nonneg r)]
  have hexponent : -lam * r + lam ^ 2 * v ≤ -r ^ 2 / (4 * (v + c * r)) := by
    have hmul := mul_le_mul_of_nonneg_left hhalf hlam
    calc
      _ ≤ -lam * r / 2 := by nlinarith
      _ = _ := by
        dsimp [lam]
        change -(r / (2 * A)) * r / 2 = -r ^ 2 / (4 * A)
        field_simp
        ring
  exact (pmfMean_compensated_tail _ (X k) (V k) lam r v hlam (hmgf.trans hi)).trans
    (Real.exp_le_exp.mpr hexponent)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem historyLaw_marginal {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) (hk : k ≤ T) :
    (historyLaw initial K T k).map (fun ω => ω (historyIndex T k)) =
      markovLaw initial K k := by
  induction k with
  | zero =>
    simp only [historyLaw,markovLaw,historyInitial,PMF.map_comp]
    change initial.map id = initial
    exact PMF.map_id initial
  | succ k ih =>
    have hkt : k < T := by omega
    have hkm : k ≤ T := by omega
    simp only [historyLaw,markovLaw,PMF.map_bind]
    have ih' := ih hkm
    change (historyLaw initial K T k).bind _ = (markovLaw initial K k).bind (K k)
    rw [← ih',PMF.bind_map]
    congr 1
    funext ω
    simp only [historyKernel,ite_eq_left hkt,PMF.map_comp,Function.comp_def,
      Function.update_self]
    exact PMF.map_id _

theorem historyCounter_update {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyCounter v T (k + 1) (Function.update ω (historyIndex T (k + 1)) b) =
      historyCounter v T k ω + v k (ω (historyIndex T k)) := by
  unfold historyCounter
  rw [Nat.min_eq_left (by omega : k + 1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (historyIndex_ne_succ (Finset.mem_range.mp hj).le hk)]
  · rw [Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

theorem historyLaw_current_support {α : Type*} (initial : PMF α)
    (K : ℕ → α → PMF α) (T k : ℕ) (hk : k ≤ T)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ω (historyIndex T k) ∈ (markovLaw initial K k).support := by
  rw [← historyLaw_marginal initial K T k hk]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨ω,hω,rfl⟩

theorem historyCounter_frozen {α : Type*} (v : ℕ → α → ℝ) (T k : ℕ) (hk : T ≤ k)
    (ω : History α T) : historyCounter v T (k + 1) ω = historyCounter v T k ω := by
  simp only [historyCounter,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k + 1)]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TerminalLaw
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem triangle_edge_card {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) : (t.powersetCard 2).card = 3 := by
  rw [Finset.card_powersetCard, (mem_triangles.mp ht).1]
  decide

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_TriangleDrift
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : β → α → ℝ) :
    pmfMean p (fun a => ∑ b, f b a) = ∑ b, pmfMean p (f b) := by
  simp only [pmfMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem step_mean {n : ℕ} (G : Graph n) (f : Graph n → ℝ)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) f =
      (∑ t ∈ triangles G, f (G \ t.powersetCard 2)) / ((triangles G).card : ℝ) := by
  rw [step, dite_eq_left hG, pmfMean_map, pmfMean_uniformOfFinset]

theorem intact_delete {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (t : Finset (Fin n)) :
    intact F (G \ t.powersetCard 2) =
      1 - if ¬ Disjoint F (t.powersetCard 2) then 1 else 0 := by
  classical
  simp only [intact, Finset.subset_sdiff, hF, true_and]
  split_ifs <;> simp_all

theorem step_mean_intact {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) (intact F) =
      1 - ((hittingTriangles G F).card : ℝ) / ((triangles G).card : ℝ) := by
  classical
  rw [step_mean G (intact F) hG]
  simp_rw [intact_delete hF]
  rw [Finset.sum_sub_distrib]
  have hb : (∑ t ∈ triangles G, if ¬ Disjoint F (t.powersetCard 2) then (1 : ℝ) else 0) =
      ((hittingTriangles G F).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [hittingTriangles]
  rw [hb]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [sub_div, div_self (by exact_mod_cast hG.card_pos.ne')]

theorem step_mean_intact_of_not_subset {n : ℕ} {G F : Graph n}
    (hF : ¬ F ⊆ G) : pmfMean (step G) (intact F) = 0 := by
  rw [← pmfMean_const (step G) 0]
  apply pmfMean_congr
  intro H hH
  have hFH : ¬ F ⊆ H := fun h => hF (h.trans (step_support_subset hH))
  simp [intact, hFH]

theorem three_le_card_union {α : Type*} [DecidableEq α]
    {e f : Finset α} (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f) :
    3 ≤ (e ∪ f).card := by
  have hi : (e ∩ f).card < 2 := by
    by_contra h
    have hge : 2 ≤ (e ∩ f).card := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hfq : e ∩ f = f := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    exact hef (heq.symm.trans hfq)
  have h := Finset.card_union_add_card_inter e f
  omega

theorem triangle_eq_of_two_edges {α : Type*} [DecidableEq α]
    {t u e f : Finset α} (ht : t.card = 3) (hu : u.card = 3)
    (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f)
    (het : e ⊆ t) (hft : f ⊆ t) (heu : e ⊆ u) (hfu : f ⊆ u) : t = u := by
  have hm := three_le_card_union he hf hef
  have ht' : e ∪ f = t := Finset.eq_of_subset_of_card_le
    (Finset.union_subset het hft) (by omega)
  have hu' : e ∪ f = u := Finset.eq_of_subset_of_card_le
    (Finset.union_subset heu hfu) (by omega)
  exact ht'.symm.trans hu'

theorem sum_card_le_card_biUnion_add_pair_overlaps {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α) (F : α → Finset β) :
    (∑ a ∈ s, (F a).card) ≤ (s.biUnion F).card +
      ∑ a ∈ s, ∑ b ∈ s.erase a, ((F a) ∩ F b).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>

    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    have hi : ((F a) ∩ s.biUnion F).card ≤ ∑ b ∈ s, ((F a) ∩ F b).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    have hcard := Finset.card_union_add_card_inter (F a) (s.biUnion F)
    have hsum : (∑ x ∈ s, ∑ b ∈ s.erase x, ((F x) ∩ F b).card) ≤
        ∑ x ∈ s, ∑ b ∈ (insert a s).erase x, ((F x) ∩ F b).card := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.erase_subset_erase x (Finset.subset_insert a s)
      · intro i _ _; exact Nat.zero_le _
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    omega

theorem hittingTriangles_eq_biUnion {n : ℕ} (G F : Graph n) :
    hittingTriangles G F = F.biUnion (incidentTriangles G) := by
  classical
  ext t
  simp only [hittingTriangles, Finset.mem_filter, Finset.mem_biUnion,
    incidentTriangles, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨ht, e, heF, het⟩
    exact ⟨e, heF, ht, het⟩
  · rintro ⟨e, heF, ht, het⟩
    exact ⟨ht, e, heF, het⟩

theorem incident_pair_card_le_one {n : ℕ} (G : Graph n)
    {e f : Finset (Fin n)} (hef : e ≠ f) :
    ((incidentTriangles G e) ∩ incidentTriangles G f).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht u hu
  simp only [incidentTriangles, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_powersetCard] at ht hu
  exact triangle_eq_of_two_edges (mem_triangles.mp ht.1.1).1
    (mem_triangles.mp hu.1.1).1 ht.1.2.2 ht.2.2.2 hef
    ht.1.2.1 ht.2.2.1 hu.1.2.1 hu.2.2.1

theorem hittingTriangles_card_le_degree_sum {n : ℕ} (G F : Graph n) :
    (hittingTriangles G F).card ≤ ∑ e ∈ F, triangleDegree G e := by
  rw [hittingTriangles_eq_biUnion]
  exact Finset.card_biUnion_le

theorem degree_sum_le_hittingTriangles_add {n : ℕ} (G F : Graph n) :
    (∑ e ∈ F, triangleDegree G e) ≤ (hittingTriangles G F).card + F.card ^ 2 := by
  rw [hittingTriangles_eq_biUnion]
  refine (sum_card_le_card_biUnion_add_pair_overlaps F (incidentTriangles G)).trans ?_
  apply Nat.add_le_add_left
  calc
    (∑ e ∈ F, ∑ f ∈ F.erase e, ((incidentTriangles G e) ∩ incidentTriangles G f).card)
        ≤ ∑ _e ∈ F, F.card := by
          apply Finset.sum_le_sum
          intro e _
          calc
            (∑ f ∈ F.erase e, ((incidentTriangles G e) ∩ incidentTriangles G f).card)
                ≤ ∑ _f ∈ F.erase e, 1 := by
                  apply Finset.sum_le_sum
                  intro f hf
                  exact incident_pair_card_le_one G (Finset.ne_of_mem_erase hf).symm
            _ = (F.erase e).card := by simp
            _ ≤ F.card := Finset.card_le_card (Finset.erase_subset e F)
    _ = F.card ^ 2 := by simp [pow_two]

theorem hittingTriangles_degree_error {n : ℕ} (G F : Graph n) (D δ : ℝ)
    (h : ∀ e ∈ F, |(triangleDegree G e : ℝ) - D| ≤ δ) :
    |((hittingTriangles G F).card : ℝ) - (F.card : ℝ) * D| ≤
      (F.card : ℝ) * δ + (F.card : ℝ) ^ 2 := by
  have hsumlo : (F.card : ℝ) * (D - δ) ≤ ∑ e ∈ F, (triangleDegree G e : ℝ) := by
    calc
      _ = ∑ _e ∈ F, (D - δ) := by simp [mul_sub]
      _ ≤ _ := Finset.sum_le_sum fun e he => by
        have hh := (abs_le.mp (h e he)).1
        linarith
  have hsumhi : (∑ e ∈ F, (triangleDegree G e : ℝ)) ≤ (F.card : ℝ) * (D + δ) := by
    calc
      _ ≤ ∑ _e ∈ F, (D + δ) := Finset.sum_le_sum fun e he => by
        have hh := (abs_le.mp (h e he)).2
        linarith
      _ = _ := by simp [mul_add]
  have hhitlo : (∑ e ∈ F, (triangleDegree G e : ℝ)) ≤
      ((hittingTriangles G F).card : ℝ) + (F.card : ℝ) ^ 2 := by
    exact_mod_cast degree_sum_le_hittingTriangles_add G F
  have hhithi : ((hittingTriangles G F).card : ℝ) ≤
      ∑ e ∈ F, (triangleDegree G e : ℝ) := by
    exact_mod_cast hittingTriangles_card_le_degree_sum G F
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (F.card : ℝ)]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryAlive
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma historyAlive_update {α : Type*} (safe : ℕ → α → Prop) (T j : ℕ)
    (hj : j < T) (ω : History α T) (b : α) :
    historyAlive safe T (j+1) (Function.update ω (historyIndex T (j+1)) b) ↔
      historyAlive safe T j ω ∧ safe j (ω (historyIndex T j)) := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hh := h i (by omega)
      rwa [Function.update_of_ne (historyIndex_ne_succ hi.le hj)] at hh
    · have hh := h j (by omega)
      rwa [Function.update_of_ne (historyIndex_ne_succ le_rfl hj)] at hh
  · rintro ⟨h,hj'⟩ i hi
    rw [Function.update_of_ne (historyIndex_ne_succ (by omega) hj)]
    rcases lt_or_eq_of_le (show i ≤ j by omega) with hi' | rfl
    · exact h i hi'
    · exact hj'

theorem history_alive_mean_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (safe : ℕ → α → Prop)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (T : ℕ)
    (hstep : ∀ i < T, ∀ a, safe i a → pmfMean (K i a) f ≤ r i * f a)
    (j : ℕ) (hj : j ≤ T) :
    pmfMean (historyLaw initial K T j)
      (fun ω => if historyAlive safe T j ω then f (ω (historyIndex T j)) else 0) ≤
      (∏ i ∈ Finset.range j, r i) * pmfMean initial f := by
  classical
  induction j with
  | zero =>
    simp [historyLaw,markovLaw,historyInitial,pmfMean_map,historyAlive]
  | succ j ih =>
    have hjT : j < T := by omega
    have ih' := ih hjT.le
    change pmfMean ((historyLaw initial K T j).bind (historyKernel K T j)) _ ≤ _
    rw [pmfMean_bind,Finset.prod_range_succ]
    calc
      _ ≤ pmfMean (historyLaw initial K T j)
          (fun ω => r j * (if historyAlive safe T j ω then f (ω (historyIndex T j)) else 0)) := by
        apply pmfMean_mono
        intro ω _
        simp only [historyKernel,ite_eq_left hjT,pmfMean_map,historyAlive_update safe T j hjT,
          Function.update_self]
        by_cases ha : historyAlive safe T j ω
        · by_cases hs : safe j (ω (historyIndex T j))
          · simp only [ha,hs,and_self,ite_true]
            exact hstep j hjT _ hs
          · simp only [ha,hs,and_false,ite_false,ite_true,pmfMean_const]
            exact mul_nonneg (hr j) (hf _)
        · simp only [ha,false_and,ite_false,pmfMean_const,mul_zero,le_refl]
      _ = r j * pmfMean (historyLaw initial K T j)
          (fun ω => if historyAlive safe T j ω then f (ω (historyIndex T j)) else 0) :=
        pmfMean_const_mul _ _ _
      _ ≤ r j * ((∏ i ∈ Finset.range j, r i) * pmfMean initial f) :=
        mul_le_mul_of_nonneg_left ih' (hr j)
      _ = _ := by ring

lemma intact_nonnegative {n : ℕ} (F G : Graph n) : 0 ≤ intact F G := by
  classical
  unfold intact
  split_ifs <;> norm_num

theorem triangle_intact_exponential_bound {n : ℕ} (G F : Graph n) (D δ : ℝ)
    (hQ : (triangles G).Nonempty)
    (hdeg : ∀ e ∈ G, |(triangleDegree G e : ℝ)-D| ≤ δ) :
    pmfMean (step G) (intact F) ≤
      Real.exp (-((F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2))/(triangles G).card) *
        intact F G := by
  classical
  by_cases hF : F ⊆ G
  · have he := hittingTriangles_degree_error G F D δ (fun e he => hdeg e (hF he))
    have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
    rw [step_mean_intact hF hQ]
    simp only [intact,hF,ite_true,mul_one]
    have hl : (F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2) ≤
        (hittingTriangles G F).card := by linarith [(abs_le.mp he).1]
    calc
      _ ≤ 1-((F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2))/(triangles G).card :=
        sub_le_sub_left (div_le_div_of_nonneg_right hl hq.le) 1
      _ ≤ _ := by
        have hh := Real.add_one_le_exp
          (-(((F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2))/(triangles G).card))
        convert hh using 1 <;> congr 1 <;> ring
  · rw [step_mean_intact_of_not_subset hF]
    simp [intact,hF]

theorem triangle_killed_survival {n : ℕ} (initial : PMF (Graph n))
    (safe : ℕ → Graph n → Prop) (F : Graph n) (rate : ℕ → ℝ) (T j : ℕ) (hj : j ≤ T)
    (hstep : ∀ i < T, ∀ G, safe i G →
      pmfMean (step G) (intact F) ≤ Real.exp (rate i) * intact F G) :
    pmfMean (historyLaw initial (fun _ => step) T j)
      (fun ω => if historyAlive safe T j ω then intact F (ω (historyIndex T j)) else 0) ≤
      Real.exp (∑ i ∈ Finset.range j, rate i) * pmfMean initial (intact F) := by
  classical
  have h := history_alive_mean_le initial (fun _ => step) safe (intact F)
    (intact_nonnegative F) (fun i => Real.exp (rate i)) (fun i => (Real.exp_pos _).le)
    T hstep j hj
  simpa only [← Real.exp_sum] using h

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleDegreeMean
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma triangle_incidence_swap {n : ℕ} (G : Graph n) (f : Finset (Fin n) → ℝ) :
    (∑ t ∈ triangles G, ∑ e ∈ t.powersetCard 2, f e) =
      ∑ e ∈ G, (triangleDegree G e : ℝ) * f e := by
  classical
  calc
    _ = ∑ t ∈ triangles G, ∑ e ∈ G, if e ∈ t.powersetCard 2 then f e else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun he => ⟨(mem_triangles.mp ht).2 he,he⟩, fun he => he.2⟩
    _ = ∑ e ∈ G, ∑ t ∈ triangles G, if e ∈ t.powersetCard 2 then f e else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      simp [triangleDegree, incidentTriangles, mul_comm]

lemma triangle_degree_sum {n : ℕ} (G : Graph n) :
    (∑ e ∈ G, (triangleDegree G e : ℝ)) = 3 * (triangles G).card := by
  have h := triangle_incidence_swap G (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  calc
    _ = ∑ t ∈ triangles G, ((t.powersetCard 2).card : ℝ) := h.symm
    _ = ∑ _t ∈ triangles G, (3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [triangle_edge_card ht]
      norm_num
    _ = _ := by simp; ring

end SharpTerminalLeave
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_DensityEdgeSafe
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

lemma triangle_count_from_edge_degrees {n : ℕ} (G : Graph n) (D δ : ℝ)
    (hd : ∀ e ∈ G, |(triangleDegree G e : ℝ)-D| ≤ δ) :
    |3*(triangles G).card-(G.card : ℝ)*D| ≤ (G.card : ℝ)*δ := by
  have he : 3*(triangles G).card-(G.card : ℝ)*D =
      ∑ e ∈ G, ((triangleDegree G e : ℝ)-D) := by
    rw [Finset.sum_sub_distrib,triangle_degree_sum]
    simp
  rw [he]
  calc
    _ ≤ ∑ e ∈ G, |(triangleDegree G e : ℝ)-D| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G, δ := Finset.sum_le_sum (fun e he => hd e he)
    _ = _ := by simp

lemma densityEdgeSafe_triangle_bounds {n : ℕ} {p η : ℝ} {G : Graph n}
    (h : densityEdgeSafe n p η G) :
    (n : ℝ)^3*p^3/6*(1-η) ≤ (triangles G).card ∧
      (triangles G).card ≤ (n : ℝ)^3*p^3/6*(1+η) := by
  have hc := triangle_count_from_edge_degrees G (n*p^2) (η*(n*p^2)) h.2.2
  rw [h.2.1] at hc
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  constructor <;> nlinarith only [hl,hu]

lemma densityEdgeSafe_triangle_positive {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : η ≤ 1/2) (h : densityEdgeSafe n p η G) :
    (triangles G).Nonempty := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := (densityEdgeSafe_triangle_bounds h).1
  have hfac : 0 < 1-η := by linarith
  have hpos : (0 : ℝ) < (triangles G).card :=
    lt_of_lt_of_le (by positivity) hq
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

theorem densityEdgeSafe_intact_step {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (_hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) (F : Graph n) :
    pmfMean (step G) (intact F) ≤ Real.exp
      (-((F.card : ℝ)*(6/(n : ℝ)^2/p))+2*(F.card : ℝ)*η*(6/(n : ℝ)^2/p)+
        (F.card : ℝ)^2*(2*(6/(n : ℝ)^2)/(n*p^3))) * intact F G := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
  obtain ⟨hlo,hhi⟩ := densityEdgeSafe_triangle_bounds h
  let Q₀ : ℝ := (n : ℝ)^3*p^3/6
  let lam : ℝ := 6/(n : ℝ)^2/p
  let D : ℝ := n*p^2
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hlamQ : lam*Q₀ = D := by dsimp [lam,Q₀,D]; field_simp
  have hQl : Q₀/2 ≤ (triangles G).card := by
    have hm := mul_le_mul_of_nonneg_left hη1 hQ₀.le
    dsimp only [Q₀] at hm ⊢
    nlinarith only [hlo,hm]
  have hrec : 1/(triangles G).card ≤ 2*(6/(n : ℝ)^2)/(n*p^3) := by
    have hr : 1/(triangles G).card ≤ 2/Q₀ := by
      apply (div_le_div_iff₀ hq hQ₀).mpr
      linarith only [hQl]
    have he : 2/Q₀ = 2*(6/(n : ℝ)^2)/(n*p^3) := by dsimp [Q₀]; field_simp
    rwa [he] at hr
  have hlin : lam*(1-2*η) ≤ D*(1-η)/(triangles G).card := by
    apply (le_div_iff₀ hq).mpr
    have hh : lam*(triangles G).card ≤ D*(1+η) := by
      have hmul := mul_le_mul_of_nonneg_left hhi hlam.le
      change lam*(triangles G).card ≤ lam*(Q₀*(1+η)) at hmul
      rwa [← mul_assoc,hlamQ] at hmul
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ 1-2*η by linarith)
    have he : (1+η)*(1-2*η) ≤ 1-η := by nlinarith [sq_nonneg η]
    have he' := mul_le_mul_of_nonneg_left he hD.le
    nlinarith only [hm,he']
  have hexp : -((F.card : ℝ)*D-((F.card : ℝ)*(η*D)+(F.card : ℝ)^2))/(triangles G).card ≤
      -((F.card : ℝ)*lam)+2*(F.card : ℝ)*η*lam+
        (F.card : ℝ)^2*(2*(6/(n : ℝ)^2)/(n*p^3)) := by
    have ha := mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg F.card)
    have hb := mul_le_mul_of_nonneg_left hrec (sq_nonneg (F.card : ℝ))
    simp only [div_eq_mul_inv] at ha hb ⊢
    nlinarith only [ha,hb]
  have hb := triangle_intact_exponential_bound G F D (η*D) hQ h.2.2
  exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (intact_nonnegative F G))

theorem density_killed_survival {n : ℕ} (initial : PMF (Graph n))
    (p : ℕ → ℝ) (η : ℝ) (T j : ℕ) (hj : j ≤ T) (hn : 0 < n)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+6/(n : ℝ)^2)
    (hp0 : p 0 ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1/2) (F : Graph n) :
    pmfMean (historyLaw initial (fun _ => step) T j)
      (fun ω => if historyAlive (fun i => densityEdgeSafe n (p i) η) T j ω then
        intact F (ω (historyIndex T j)) else 0) ≤
      p j^F.card * Real.exp
        ((F.card : ℝ)*(1-p 0)/p 0+(F.card : ℝ)*(6/(n : ℝ)^2)/p j+
          2*(F.card : ℝ)*η*(-Real.log (p j))+(F.card : ℝ)^2/(n*p j^2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let b : ℝ := F.card
  let h : ℝ := 6/(n : ℝ)^2
  let rate : ℕ → ℝ := fun i => -b*(h/p i)+2*b*η*(h/p i)+b^2*(2*h/(n*p i^3))
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hk := triangle_killed_survival initial (fun i => densityEdgeSafe n (p i) η) F rate T j hj
    (fun i hi G hG => by
      simpa only [rate,b,h,neg_mul] using densityEdgeSafe_intact_step hn (hp i hi.le) hη hη1 hG F)
  have hsumb := density_survival_exponent_bound p n h b η j hnR hh hb hη
    (fun i hi => hp i (hi.trans hj)) (fun i hi => hs i (by omega)) hp0
  have hi : pmfMean initial (intact F) ≤ 1 := by
    calc
      _ ≤ pmfMean initial (fun _ => (1 : ℝ)) := by
        apply pmfMean_mono
        intro G _
        unfold intact
        split_ifs <;> norm_num
      _ = 1 := pmfMean_const _ _
  apply hk.trans
  calc
    _ ≤ Real.exp (∑ i ∈ Finset.range j, rate i) := by
      nlinarith only [mul_le_mul_of_nonneg_left hi (Real.exp_pos (∑ i ∈ Finset.range j, rate i)).le]
    _ ≤ Real.exp (b*Real.log (p j)+b*(1-p 0)/p 0+b*h/p j+
        2*b*η*(-Real.log (p j))+b^2/(n*p j^2)) := Real.exp_le_exp.mpr hsumb
    _ = _ := by
      have he : Real.exp (b*Real.log (p j)) = p j^F.card := by
        dsimp only [b]
        rw [Real.exp_nat_mul,Real.exp_log (hp j hj)]
      rw [show b*Real.log (p j)+b*(1-p 0)/p 0+b*h/p j+
          2*b*η*(-Real.log (p j))+b^2/(n*p j^2) =
          b*Real.log (p j)+(b*(1-p 0)/p 0+b*h/p j+
          2*b*η*(-Real.log (p j))+b^2/(n*p j^2)) by ring,Real.exp_add,he]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_RootedTemplates
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem imageEdges_simple {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n)
    {e : Finset (Fin n)} (he : e ∈ imageEdges T φ) : e.card = 2 := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  simpa using T.simple f hf

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighbors
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem commonNeighbors_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (hw : w ∈ commonNeighbors G u v) : u ≠ w ∧ v ≠ w := by
  obtain ⟨hu,hv⟩ := (mem_commonNeighbors G u v w).mp hw
  constructor
  · intro h
    have hc := mem_completeGraph.mp (hG hu)
    simp [h] at hc
  · intro h
    have hc := mem_completeGraph.mp (hG hv)
    simp [h] at hc

theorem currentCodegree_copyCount {n : ℕ} (G : Graph n) (u v : Fin n) :
    (currentCodegree G u v : ℝ) = copyCount (wedgeEdges u v) G := by
  simp only [copyCount, intact, wedgeEdges_subset]
  rw [← Finset.sum_filter]
  simp [currentCodegree, commonNeighbors]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefixDensity_bounds (n : ℕ) (hn : 0 < n)
    (ht : 0 ≤ prefixTargetTime n) :
    prefixTargetDensity n ≤ prefixDensity n ∧
      prefixDensity n < prefixTargetDensity n + 6 / (n : ℝ)^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have hf : (prefixTime n : ℝ) ≤ prefixTargetTime n := Nat.floor_le ht
  have hg : prefixTargetTime n < (prefixTime n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : prefixTargetTime n * 6 =
      (n : ℝ)^2 * (1 - 1 / (n : ℝ) - prefixTargetDensity n) := by
    unfold prefixTargetTime
    ring
  have hp : prefixDensity n * (n : ℝ)^2 =
      (1 - 1 / (n : ℝ)) * (n : ℝ)^2 - 6 * prefixTime n := by
    unfold prefixDensity
    field_simp
  constructor
  · apply (le_of_mul_le_mul_right (a := (n : ℝ)^2) _ hn2)
    nlinarith
  · apply (lt_of_mul_lt_mul_right (a := (n : ℝ)^2) _ (le_of_lt hn2))
    have he : (6 / (n : ℝ)^2) * (n : ℝ)^2 = 6 := div_mul_cancel₀ _ (ne_of_gt hn2)
    nlinarith

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_OneAddLogRpow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Asymptotics

lemma one_add_log_rpow_isLittleO (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => (1 + Real.log x) ^ C) =o[atTop] fun x => x ^ δ := by
  let C' := max C 1
  have hC' : 0 < C' := lt_max_iff.mpr (Or.inr zero_lt_one)
  have hq : 0 < δ / C' := div_pos hδ hC'
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (δ / C') := by
    apply (isLittleO_const_left_of_ne one_ne_zero).mpr
    apply (tendsto_rpow_atTop hq).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hx _)).symm
  have hs := hc.add (isLittleO_log_rpow_atTop hq)
  calc
    (fun x : ℝ => (1 + Real.log x) ^ C) =O[atTop]
        fun x => (1 + Real.log x) ^ C' := by
      apply IsBigO.of_norm_eventuallyLE
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx
      simp only [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Real.log x) C)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    _ =o[atTop] fun x => (x ^ (δ / C')) ^ C' :=
      hs.rpow hC' ((eventually_ge_atTop (0 : ℝ)).mono fun x hx => Real.rpow_nonneg hx _)
    _ =ᶠ[atTop] fun x => x ^ δ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_mul hx,div_mul_cancel₀ _ hC'.ne']

 theorem prefixTemplateFactor_subpower (C : ℝ) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ b * (n : ℝ) ^ δ := by
  have h := ((one_add_log_rpow_isLittleO C hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hb
  filter_upwards [h,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hb0 : 0 ≤ 1 + Real.log (n : ℝ) := by linarith
  simpa only [Function.comp_apply,Real.norm_of_nonneg (Real.rpow_nonneg hb0 C),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ),prefixTemplateFactor] using hn

lemma prefixTargetDensity_eq (n : ℕ) :
    prefixTargetDensity n = (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  unfold prefixTargetDensity prefixEpsilon
  congr 1
  norm_num

lemma prefixTargetDensity_tendsto : Tendsto prefixTargetDensity atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => prefixTargetDensity n) atTop (𝓝 0)
  simp_rw [prefixTargetDensity_eq]
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999 / 2000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixTargetTime_eventually_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ prefixTargetTime n := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [prefixTargetDensity_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    hi.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hp hi
  unfold prefixTargetTime
  exact mul_nonneg (by positivity) (by linarith)

theorem prefixDensity_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (-(999 / 2000 : ℝ)) ≤ prefixDensity n ∧
      prefixDensity n ≤ 2 * (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  filter_upwards [prefixTargetTime_eventually_nonneg,eventually_ge_atTop (6 : ℕ)] with n ht hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl,hu⟩ := prefixDensity_bounds n (by omega) ht
  rw [prefixTargetDensity_eq] at hl hu
  refine ⟨hl,?_⟩
  have h1 : 6 / (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2) hn0).mpr
    nlinarith
  have h2 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith

lemma prefix_target_D_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(999 / 2000 : ℝ))) ^ 2 =
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnR]
  congr 1
  norm_num

theorem prefixD_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (1 / 1000 : ℝ) ≤ prefixD n ∧
      prefixD n ≤ 4 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hp hn
  have hn0 : 0 < n := by omega
  have hq : 0 ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpl : 0 ≤ prefixDensity n := hq.trans hp.1
  rw [← prefix_target_D_identity n hn0]
  unfold prefixD
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hp.1 2) (Nat.cast_nonneg n)
  · have hsq := pow_le_pow_left₀ hpl hp.2 2
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hsq)]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_HistoryLawPathSupport
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem copyCount_nonneg {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) : 0 ≤ copyCount required G := by
  apply Finset.sum_nonneg
  intro a _
  unfold intact
  split <;> norm_num

theorem historyNoise_succ_same {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ)
    (T j : ℕ) (hj : j < T) (ω : History α T) :
    historyNoise K f T (j+1) ω =
      historyNoise K f T j ω + historyIncrement K f T j ω := by
  simp only [historyNoise,Nat.min_eq_left (by omega : j+1 ≤ T),
    Nat.min_eq_left hj.le,Finset.sum_range_succ]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_HistoryLawPastMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem historyLaw_past_mean {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (T j k : ℕ) (hjk : j ≤ k)
    (f : History α T → ℝ)
    (hf : ∀ ω π, (∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) → f ω = f π) :
    pmfMean (historyLaw initial K T k) f =
      pmfMean (historyLaw initial K T j) f := by
  classical
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | @succ k hjk ih =>
    change pmfMean ((historyLaw initial K T k).bind (historyKernel K T k)) f = _
    rw [pmfMean_bind]
    have he (ω : History α T) : pmfMean (historyKernel K T k ω) f = f ω := by
      by_cases hk : k < T
      · rw [historyKernel,ite_eq_left hk,pmfMean_map]
        have hu (b : α) : f (Function.update ω (historyIndex T (k+1)) b) = f ω := by
          apply hf
          intro i hi
          apply Function.update_of_ne
          intro hh
          have hval := congrArg Fin.val hh
          simp only [historyIndex,Nat.min_eq_left (by omega : k+1 ≤ T)] at hval
          have : i.val ≤ j := hi.trans (Nat.min_le_left _ _)
          omega
        simp_rw [hu]
        exact pmfMean_const _ _
      · rw [historyKernel,ite_eq_right hk,pmfMean_pure]
    simp_rw [he]
    exact ih

lemma historyCounter_past {α : Type*} (v : ℕ → α → ℝ)
    (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyCounter v T j ω = historyCounter v T j π := by
  unfold historyCounter
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  rw [h _ hsc]

lemma pmfMean_finset_sum {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (f : J → α → ℝ) :
    pmfMean p (fun a => ∑ j ∈ s, f j a) = ∑ j ∈ s, pmfMean p (f j) := by
  simp only [pmfMean,Finset.mul_sum]
  exact Finset.sum_comm

open Classical in

theorem pmfMean_event_union {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (P : J → α → Prop) :
    pmfMean p (fun a => if ∃ j ∈ s, P j a then 1 else 0) ≤
      ∑ j ∈ s, pmfMean p (fun a => if P j a then 1 else 0) := by
  classical
  rw [← pmfMean_finset_sum]
  apply pmfMean_mono
  intro a _
  by_cases h : ∃ j ∈ s, P j a
  · obtain ⟨j,hj,hP⟩ := h
    rw [ite_eq_left ⟨j,hj,hP⟩]
    have hh := Finset.single_le_sum (f := fun j => (if P j a then (1 : ℝ) else 0))
      (fun _ _ => by positivity) hj
    simpa only [ite_eq_left hP] using hh
  · rw [ite_eq_right h]
    positivity

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma historyAdditive_update {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyAdditive g T (k+1) (Function.update ω (historyIndex T (k+1)) b) =
      historyAdditive g T k ω + g k (ω (historyIndex T k)) b := by
  unfold historyAdditive
  rw [Nat.min_eq_left (by omega : k+1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    rw [Function.update_of_ne (historyIndex_ne_succ hjk.le hk),
       Function.update_of_ne (historyIndex_ne_succ (by omega : j+1 ≤ k) hk)]
  · rw [Function.update_self,Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

lemma historyAdditive_frozen {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : T ≤ k) (ω : History α T) :
    historyAdditive g T (k+1) ω = historyAdditive g T k ω := by
  simp only [historyAdditive,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k+1)]

theorem history_additive_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  apply finite_freedman (historyInitial initial T) (historyKernel K T)
    (historyAdditive g T) (historyCounter v T) (historyCounterRate v T) c hc
  · intro ω _
    simp only [historyAdditive_zero,historyCounter_zero,le_refl,and_self]
  · intro j ω hω π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hbounded j hj _ (historyLaw_current_support initial K T j hj.le ω hω) b hb
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,abs_zero]
      exact hc.le
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact (hmean j hj _ (historyLaw_current_support initial K T j hj.le ω hω)).le
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self]
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map,historyCounterRate,ite_eq_left hj]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hvar j hj _ (historyLaw_current_support initial K T j hj.le ω hω)
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,
        historyCounterRate,ite_eq_right hj,zero_pow (by decide : 2 ≠ 0)]
  · intro j ω _ π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyCounter_update v T j hj,historyCounterRate,ite_eq_left hj]
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyCounter_frozen v T j (Nat.le_of_not_gt hj),
        historyCounterRate,ite_eq_right hj,add_zero]
  · exact hr
  · exact hV

lemma historyAdditive_past {α : Type*} (g : ℕ → α → α → ℝ)
    (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyAdditive g T j ω = historyAdditive g T j π := by
  unfold historyAdditive
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  have hsn : (historyIndex T (s+1)).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (by omega)
  rw [h _ hsc,h _ hsn]

theorem history_additive_freedman_maximal {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T) (Finset.range (T+1))
    (fun j ω => r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0)) ≤ (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (T+1), Real.exp (-r^2/(4*(V+c*r))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
        rw [historyLaw_past_mean initial K T j T hjT _ (by
          intro ω π h
          rw [historyAdditive_past g T j ω π h,historyCounter_past v T j ω π h])]
        exact history_additive_freedman initial K g v T c hc hbounded hmean hvar j r V hr hV
      _ = _ := by simp
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range,Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_PmfMeanNeg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma pmfMean_neg {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    pmfMean p (fun a => -f a) = -pmfMean p f := by
  simp only [pmfMean,mul_neg,Finset.sum_neg_distrib]

lemma historyAdditive_neg {α : Type*} (g : ℕ → α → α → ℝ)
    (T j : ℕ) (ω : History α T) :
    historyAdditive (fun k a b => -g k a b) T j ω = -historyAdditive g T j ω := by
  simp only [historyAdditive,Finset.sum_neg_distrib]

theorem history_additive_freedman_two_sided {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hp := history_additive_freedman_maximal initial K g v T c hc hbounded hmean hvar r V hr hV
  have hn := history_additive_freedman_maximal initial K (fun k a b => -g k a b) v T c hc
    (by intro k hk a ha b hb; simpa only [abs_neg] using hbounded k hk a ha b hb)
    (by intro k hk a ha; rw [pmfMean_neg,hmean k hk a ha,neg_zero])
    (by intro k hk a ha; simpa only [neg_sq] using hvar k hk a ha) r V hr hV
  have hcov : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧ historyCounter v T j ω ≤ V
        then 1 else 0) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0) +
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) := by
    rw [← pmfMean_add]
    apply pmfMean_mono
    intro ω _
    by_cases h : ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧ historyCounter v T j ω ≤ V
    · obtain ⟨j,hj,hx,hv⟩ := h
      rw [ite_eq_left ⟨j,hj,hx,hv⟩]
      rcases le_total 0 (historyAdditive g T j ω) with hx0 | hx0
      · rw [abs_of_nonneg hx0] at hx
        rw [ite_eq_left ⟨j,hj,hx,hv⟩]
        split_ifs <;> norm_num
      · rw [abs_of_nonpos hx0] at hx
        have hneg : r ≤ historyAdditive (fun k a b => -g k a b) T j ω := by
          rwa [historyAdditive_neg]
        have hnegE : ∃ j ≤ T, r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V := ⟨j,hj,hneg,hv⟩
        rw [ite_eq_left hnegE]
        split_ifs <;> norm_num
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  exact hcov.trans (by nlinarith [hp,hn])

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowersetCardTriple
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma powersetCard_triple {α : Type*} [DecidableEq α] {u v w : α}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u,v,w} : Finset α).powersetCard 2 = {{u,v},{u,w},{v,w}} := by
  have h2 : ({v,w}:Finset α).powersetCard 2 = {{v,w}} := by
    rw [← Finset.card_pair hvw]
    exact Finset.powersetCard_self _
  rw [Finset.powersetCard_succ_insert (by simp [huv,huw]) 1, h2]
  simp only [Finset.powersetCard_one, Finset.map_insert, Finset.map_singleton, Finset.image_insert,
    Finset.image_singleton, Function.Embedding.coeFn_mk]
  ext s
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triangle_closure_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    {u,v,w} ∈ triangles G ↔ {u,v} ∈ G := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  obtain ⟨huwG,hvwG⟩ := (mem_commonNeighbors G u v w).mp hw
  rw [mem_triangles, powersetCard_triple huv huw hvw]
  simp [huv,huw,hvw,Finset.insert_subset_iff,Finset.singleton_subset_iff,huwG,hvwG]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeVarianceRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_centered_sq_le {α : Type*} [Fintype α]
    (p : PMF α) (f : α → ℝ) (a : ℝ) :
    pmfMean p (fun b => (f b - pmfMean p f)^2) ≤
      pmfMean p (fun b => (f b - a)^2) := by
  rw [pmfMean_sq_sub,pmfMean_sq_sub]
  nlinarith [sq_nonneg (pmfMean p f - a)]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CopyEdgeLoad
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma intact_nonneg {n : ℕ} (F G : Graph n) : 0 ≤ intact F G := by
  unfold intact
  split <;> norm_num

lemma intact_mono {n : ℕ} (F : Graph n) {G H : Graph n} (h : G ⊆ H) :
    intact F G ≤ intact F H := by
  unfold intact
  by_cases hF : F ⊆ G
  · rw [ite_eq_left hF,ite_eq_left (hF.trans h)]
  · rw [ite_eq_right hF]
    split <;> norm_num

lemma copyCount_mono {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) {G H : Graph n} (h : G ⊆ H) :
    copyCount required G ≤ copyCount required H := by
  apply Finset.sum_le_sum
  intro a _
  exact intact_mono (required a) h

lemma intact_deleted_loss_le {n : ℕ} (F G E : Graph n) :
    intact F G - intact F (G \ E) ≤
      ∑ e ∈ E, if e ∈ F then intact F G else 0 := by
  classical
  by_cases hF : F ⊆ G
  · by_cases hFE : F ⊆ G \ E
    · rw [intact,ite_eq_left hF,intact,ite_eq_left hFE,sub_self]
      apply Finset.sum_nonneg
      intro e _
      split <;> positivity
    · obtain ⟨e,heF,heGE⟩ := Finset.not_subset.mp hFE
      have heE : e ∈ E := by
        by_contra he
        exact heGE (Finset.mem_sdiff.mpr ⟨hF heF,he⟩)
      have hh := Finset.single_le_sum
        (f := fun e => if e ∈ F then intact F G else 0)
        (fun _ _ => by split; exact intact_nonneg _ _; exact le_rfl) heE
      simpa only [ite_eq_left heF,intact,ite_eq_left hF,ite_eq_right hFE,sub_zero] using hh
  · have hFE : ¬ F ⊆ G \ E := fun h => hF (h.trans Finset.sdiff_subset)
    simp only [intact,ite_eq_right hF,ite_eq_right hFE,sub_self,ite_self,Finset.sum_const_zero,le_refl]

theorem copyCount_deleted_loss_le {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G E : Graph n) :
    copyCount required G - copyCount required (G \ E) ≤
      ∑ e ∈ E, copyEdgeLoad required G e := by
  classical
  unfold copyCount
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, ∑ e ∈ E, if e ∈ required a then intact (required a) G else 0 := by
      apply Finset.sum_le_sum
      intro a _
      exact intact_deleted_loss_le _ _ _
    _ = _ := Finset.sum_comm

theorem copyCount_step_loss_range {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G H : Graph n) (L : ℝ) (hL : 0 ≤ L)
    (hload : ∀ e ∈ G, copyEdgeLoad required G e ≤ L)
    (hH : H ∈ (step G).support) :
    0 ≤ copyCount required G - copyCount required H ∧
      copyCount required G - copyCount required H ≤ 3*L := by
  constructor
  · exact sub_nonneg.mpr (copyCount_mono required (step_support_subset hH))
  · by_cases hG : (triangles G).Nonempty
    · obtain ⟨t,ht,rfl⟩ := (step_support_active hG).mp hH
      calc
        _ ≤ ∑ e ∈ t.powersetCard 2, copyEdgeLoad required G e :=
          copyCount_deleted_loss_le required G _
        _ ≤ ∑ _e ∈ t.powersetCard 2, L := Finset.sum_le_sum
          (fun e he => hload e ((mem_triangles.mp ht).2 he))
        _ = 3*L := by simp only [Finset.sum_const,nsmul_eq_mul,triangle_edge_card ht]; norm_num
    · simp only [step,dite_eq_right hG,PMF.mem_support_pure_iff] at hH
      subst H
      simpa only [sub_self] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hL

theorem pmf_centered_of_loss_range {α : Type*} [Fintype α] (p : PMF α)
    (f : α → ℝ) (a R : ℝ)
    (h : ∀ b ∈ p.support, 0 ≤ a-f b ∧ a-f b ≤ R) :
    ∀ b ∈ p.support, |f b-pmfMean p f| ≤ R := by
  have hlo : a-R ≤ pmfMean p f := by
    rw [← pmfMean_const p (a-R)]
    apply pmfMean_mono
    intro b hb
    have := (h b hb).2
    linarith
  have hhi : pmfMean p f ≤ a := by
    rw [← pmfMean_const p a]
    apply pmfMean_mono
    intro b hb
    have := (h b hb).1
    linarith
  intro b hb
  obtain ⟨h₁,h₂⟩ := h b hb
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem pmf_variance_of_loss_range {α : Type*} [Fintype α] (p : PMF α)
    (f : α → ℝ) (a R : ℝ)
    (h : ∀ b ∈ p.support, 0 ≤ a-f b ∧ a-f b ≤ R) :
    pmfMean p (fun b => (f b-pmfMean p f)^2) ≤ R*(a-pmfMean p f) := by
  apply (pmfMean_centered_sq_le p f a).trans
  calc
    _ ≤ pmfMean p (fun b => R*(a-f b)) := by
      apply pmfMean_mono
      intro b hb
      obtain ⟨h₁,h₂⟩ := h b hb
      nlinarith [mul_nonneg h₁ (sub_nonneg.mpr h₂)]
    _ = _ := by rw [pmfMean_const_mul,pmfMean_sub,pmfMean_const]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RelativeSafeCopyIncrement
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem triangle_relative_safe_template_freedman {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hs : ∀ j < T, 0 < s (j+1)) (hL : ∀ j < T, 0 ≤ L j)
    (hjump : ∀ j < T, 3*L j / s (j+1) ≤ c)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T,
        r ≤ |historyAdditive (relativeSafeCopyIncrement required L s) T j ω| ∧
        historyCounter (relativeSafeCopyVarianceRate required L s) T j ω ≤ V
        then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  apply history_additive_freedman_two_sided (PMF.pure G) (fun _ => step)
    (relativeSafeCopyIncrement required L s) (relativeSafeCopyVarianceRate required L s)
    T c hc
  · intro j hj H _ J hJ
    by_cases hsafe : copyLoadSafe required (L j) H
    · simp only [relativeSafeCopyIncrement,ite_eq_left hsafe,abs_div,abs_of_pos (hs j hj)]
      exact (div_le_div_of_nonneg_right
        (pmf_centered_of_loss_range (step H) (copyCount required) (copyCount required H)
          (3*L j) (fun A hA => copyCount_step_loss_range required H A (L j)
            (hL j hj) hsafe hA) J hJ) (hs j hj).le).trans (hjump j hj)
    · simp only [relativeSafeCopyIncrement,ite_eq_right hsafe,abs_zero]
      exact hc.le
  · intro j _ H _
    change pmfMean (step H) (fun J => relativeSafeCopyIncrement required L s j H J) = 0
    by_cases hsafe : copyLoadSafe required (L j) H
    · simp only [relativeSafeCopyIncrement,ite_eq_left hsafe,div_eq_mul_inv]
      rw [pmfMean_mul_const,pmfMean_sub,pmfMean_const,sub_self,zero_mul]
    · simp only [relativeSafeCopyIncrement,ite_eq_right hsafe,pmfMean_const]
  · intro j hj H _
    by_cases hsafe : copyLoadSafe required (L j) H
    · simp only [relativeSafeCopyIncrement,relativeSafeCopyVarianceRate,ite_eq_left hsafe,
        div_eq_mul_inv,mul_pow,inv_pow]
      rw [pmfMean_mul_const]
      change _ ≤ (3*L j*(copyCount required H - pmfMean (step H) (copyCount required))) *
        ((s (j+1))^2)⁻¹
      exact mul_le_mul_of_nonneg_right
        (pmf_variance_of_loss_range (step H) (copyCount required) (copyCount required H)
          (3*L j) (fun A hA => copyCount_step_loss_range required H A (L j)
            (hL j hj) hsafe hA)) (inv_nonneg.mpr (sq_nonneg _))
    · simp only [relativeSafeCopyIncrement,relativeSafeCopyVarianceRate,ite_eq_right hsafe,
        zero_pow (by decide : 2 ≠ 0),pmfMean_const,le_refl]
  · exact hr
  · exact hV

lemma relativeSafeCopyNoise_eq {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (T j : ℕ) (ω : History (Graph n) T)
    (hsafe : pastRelativeCopyLoadsSafe required L T j ω) :
    historyAdditive (relativeSafeCopyIncrement required L s) T j ω =
      historyNoise (fun _ => step) (fun k H => copyCount required H / s k) T j ω := by
  classical
  unfold historyAdditive historyNoise
  apply Finset.sum_congr rfl
  intro k hk
  simp only [historyIncrement,relativeSafeCopyIncrement,
    ite_eq_left (hsafe k (Finset.mem_range.mp hk)),div_eq_mul_inv,pmfMean_mul_const,sub_mul]

lemma relativeSafeCopyCounter_eq {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (T j : ℕ) (ω : History (Graph n) T)
    (hsafe : pastRelativeCopyLoadsSafe required L T j ω) :
    historyCounter (relativeSafeCopyVarianceRate required L s) T j ω =
      historyCounter (relativeCopyVarianceRate required L s) T j ω := by
  classical
  unfold historyCounter
  apply Finset.sum_congr rfl
  intro k hk
  simp only [relativeSafeCopyVarianceRate,ite_eq_left (hsafe k (Finset.mem_range.mp hk))]

open Classical in

theorem triangle_relative_template_before_load_exit {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hs : ∀ j < T, 0 < s (j+1)) (hL : ∀ j < T, 0 ≤ L j)
    (hjump : ∀ j < T, 3*L j / s (j+1) ≤ c)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
        r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H / s k) T j ω| ∧
        historyCounter (relativeCopyVarianceRate required L s) T j ω ≤ V then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  apply le_trans _ (triangle_relative_safe_template_freedman required G T L s c hc hs hL
    hjump r V hr hV)
  apply pmfMean_mono
  intro ω _
  by_cases h : ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
      r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H / s k) T j ω| ∧
      historyCounter (relativeCopyVarianceRate required L s) T j ω ≤ V
  · obtain ⟨j,hj,hsafe,hn,hv⟩ := h
    have h' : ∃ j ≤ T,
        r ≤ |historyAdditive (relativeSafeCopyIncrement required L s) T j ω| ∧
        historyCounter (relativeSafeCopyVarianceRate required L s) T j ω ≤ V := by
      refine ⟨j,hj,?_,?_⟩
      · rwa [relativeSafeCopyNoise_eq required L s T j ω hsafe]
      · rwa [relativeSafeCopyCounter_eq required L s T j ω hsafe]
    rw [ite_eq_left ⟨j,hj,hsafe,hn,hv⟩,ite_eq_left h']
  · rw [ite_eq_right h]
    split <;> norm_num

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RelativeScaleBudget
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem history_relative_loss_counter {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : α → ℝ) (s : ℕ → ℝ)
    (T j : ℕ) (hj : j ≤ T) (ω : History α T) :
    historyCounter (fun k a => (f a-pmfMean (K k a) f)/s (k+1)) T j ω =
      f (ω (historyIndex T 0))/s 0 - f (ω (historyIndex T j))/s j +
      (∑ k ∈ Finset.range j, f (ω (historyIndex T k)) * (1/s (k+1)-1/s k)) +
      historyNoise K (fun k a => f a/s k) T j ω := by
  unfold historyCounter historyNoise historyIncrement
  simp only [Nat.min_eq_left hj,div_eq_mul_inv,pmfMean_mul_const]
  have he : (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T k))-pmfMean (K k (ω (historyIndex T k))) f) * (s (k+1))⁻¹) =
    (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T k)) * (s k)⁻¹-
        f (ω (historyIndex T (k+1))) * (s (k+1))⁻¹)) +
    (∑ k ∈ Finset.range j,
      f (ω (historyIndex T k)) * (1*(s (k+1))⁻¹-1*(s k)⁻¹)) +
    (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T (k+1))) * (s (k+1))⁻¹-
        pmfMean (K k (ω (historyIndex T k))) f * (s (k+1))⁻¹)) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,Finset.sum_range_sub']

lemma relativeScaleBudget_nonneg (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ j ≤ T, 0 < s j) (hdec : ∀ j < T, s (j+1) ≤ s j) :
    0 ≤ relativeScaleBudget s T := by
  apply Finset.sum_nonneg
  intro j hj
  have hjT := Finset.mem_range.mp hj
  exact sub_nonneg.mpr ((one_le_div (hs (j+1) (by omega))).mpr
    (hdec j (Finset.mem_range.mp hj)))

lemma relativeScaleBudget_mono (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ j ≤ T, 0 < s j) (hdec : ∀ j < T, s (j+1) ≤ s j)
    {j : ℕ} (hj : j ≤ T) : relativeScaleBudget s j ≤ relativeScaleBudget s T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
  intro k hk _
  exact sub_nonneg.mpr ((one_le_div (hs (k+1) (by have := Finset.mem_range.mp hk; omega))).mpr
    (hdec k (Finset.mem_range.mp hk)))

theorem relativeCopyCounter_le {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (T j : ℕ) (hj : j ≤ T) (L s : ℕ → ℝ)
    (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hjump : ∀ k < T, 3*L k/s (k+1) ≤ c)
    (ω : History (Graph n) T)
    (hcount : ∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) :
    historyCounter (relativeCopyVarianceRate required L s) T j ω ≤
      c*(copyCount required (ω (historyIndex T 0))/s 0 + B*relativeScaleBudget s T +
        historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω) := by
  have hsum : historyCounter (relativeCopyVarianceRate required L s) T j ω ≤
      c*historyCounter (fun k H =>
        (copyCount required H-pmfMean (step H) (copyCount required))/s (k+1)) T j ω := by
    unfold historyCounter
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkj : k < j := by simpa only [Nat.min_eq_left hj,Finset.mem_range] using hk
    have hkT : k < T := hkj.trans_le hj
    have ht : 0 ≤ copyCount required (ω (historyIndex T k))-
        pmfMean (step (ω (historyIndex T k))) (copyCount required) := by
      apply sub_nonneg.mpr
      rw [← pmfMean_const (step (ω (historyIndex T k)))
        (copyCount required (ω (historyIndex T k)))]
      apply pmfMean_mono
      intro H hH
      exact copyCount_mono required (step_support_subset hH)
    calc
      _ = (3*L k/s (k+1))*
          ((copyCount required (ω (historyIndex T k))-
          pmfMean (step (ω (historyIndex T k))) (copyCount required))/s (k+1)) := by
        unfold relativeCopyVarianceRate copyVarianceRate
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hjump k hkT)
        (div_nonneg ht (hs (k+1) (by omega)).le)
  apply hsum.trans
  rw [history_relative_loss_counter _ _ _ _ _ hj]
  apply mul_le_mul_of_nonneg_left _ hc
  have hnon : 0 ≤ copyCount required (ω (historyIndex T j))/s j :=
    div_nonneg (copyCount_nonneg _ _) (hs j hj).le
  have hbudget : (∑ k ∈ Finset.range j,
      copyCount required (ω (historyIndex T k)) * (1/s (k+1)-1/s k)) ≤
        B*relativeScaleBudget s T := by
    calc
      _ ≤ B*relativeScaleBudget s j := by
        unfold relativeScaleBudget
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        have hkj := Finset.mem_range.mp hk
        have hkT : k < T := hkj.trans_le hj
        have hsk := hs k (by omega)
        have hsk1 := hs (k+1) (by omega)
        calc
          _ ≤ (B*s k)*(1/s (k+1)-1/s k) := by
            apply mul_le_mul_of_nonneg_right (hcount k hkj)
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hsk1 (hdec k hkT))
          _ = _ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (relativeScaleBudget_mono s T hs hdec hj) hB
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_RelativeScaleBudgetLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem relativeScaleBudget_le_log (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ k ≤ T, 0 < s k)
    (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hratio : ∀ k < T, s k ≤ 2*s (k+1)) :
    relativeScaleBudget s T ≤ 2*Real.log (s 0/s T) := by
  have hsingle {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) : r-1 ≤ 2*Real.log r := by
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one h1
    have hi : 0 ≤ 1-r⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hr).mpr h1)
    calc
      r-1 = r*(1-r⁻¹) := by field_simp
      _ ≤ 2*(1-r⁻¹) := mul_le_mul_of_nonneg_right h2 hi
      _ ≤ 2*Real.log r := mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos hr) (by norm_num)
  have htel : (∑ k ∈ Finset.range T, Real.log (s k/s (k+1))) =
      Real.log (s 0/s T) := by
    calc
      _ = ∑ k ∈ Finset.range T, (Real.log (s k)-Real.log (s (k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkT := Finset.mem_range.mp hk
        exact Real.log_div (ne_of_gt (hs k (by omega)))
          (ne_of_gt (hs (k+1) (by omega)))
      _ = Real.log (s 0)-Real.log (s T) := by rw [Finset.sum_range_sub']
      _ = Real.log (s 0/s T) := (Real.log_div
        (ne_of_gt (hs 0 (Nat.zero_le T))) (ne_of_gt (hs T le_rfl))).symm
  rw [← htel,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkT := Finset.mem_range.mp hk
  exact hsingle ((one_le_div (hs (k+1) (by omega))).mpr (hdec k hkT))
    ((div_le_iff₀ (hs (k+1) (by omega))).mpr (hratio k hkT))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EarlyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyDensity_antitone (n : ℕ) : Antitone (earlyDensity n) := by
  intro i j hij
  unfold earlyDensity
  have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact sub_le_sub_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (by norm_num)) (sq_nonneg (n : ℝ))) _

lemma earlyDensity_succ (n i : ℕ) :
    earlyDensity n i = earlyDensity n (i+1)+6/(n : ℝ)^2 := by
  unfold earlyDensity
  push_cast
  ring

lemma prefixDensity_eventually_inverse_lower : ∀ᶠ n : ℕ in atTop,
    1/(n : ℝ) ≤ prefixDensity n := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  apply le_trans _ hn.1
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)

theorem earlyTemplateScale_regular (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n (i+1) ≤ earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1)) := by
  have hi : Tendsto (fun n : ℕ => 6/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (1+6/(n : ℝ))^b) atTop (𝓝 1) := by
    simpa only [add_zero,one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).add hi).pow b
  filter_upwards [prefixDensity_eventually_inverse_lower,
    hlim.eventually_le_const (by norm_num : (1 : ℝ) < 2),
    eventually_ge_atTop (1 : ℕ)] with n hp hratio hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow : ∀ i ≤ prefixTime n, 1/(n : ℝ) ≤ earlyDensity n i := by
    intro i hi
    exact hp.trans (earlyDensity_antitone n hi)
  have hpos : ∀ i ≤ prefixTime n, 0 < earlyDensity n i := by
    intro i hi
    exact lt_of_lt_of_le (by positivity) (hlow i hi)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    exact mul_pos (pow_pos hn0 _) (pow_pos (hpos i hi) _)
  · intro i hi
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos (i+1) (by omega)).le
      (earlyDensity_antitone n (Nat.le_succ i)) b) (by positivity)
  · intro i hi
    have hp1 : 0 < earlyDensity n (i+1) := hpos (i+1) (by omega)
    have hstep : earlyDensity n i ≤ earlyDensity n (i+1)*(1+6/(n : ℝ)) := by
      rw [earlyDensity_succ n i]
      have hh := hlow (i+1) (by omega)
      have hhmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 6/(n : ℝ) by positivity)
      have he : (6/(n : ℝ))*(1/(n : ℝ)) = 6/(n : ℝ)^2 := by ring
      rw [he] at hhmul
      nlinarith only [hhmul]
    have hpw := pow_le_pow_left₀ (hpos i (by omega)).le hstep b
    rw [mul_pow] at hpw
    unfold earlyTemplateScale
    calc
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*(1+6/(n : ℝ))^b) :=
        mul_le_mul_of_nonneg_left hpw (by positivity)
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio (by positivity))
          (by positivity)
      _ = _ := by ring

theorem earlyTemplateScale_log_budget (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    relativeScaleBudget (earlyTemplateScale a b n) (prefixTime n) ≤
      2*(b : ℝ)*Real.log n := by
  filter_upwards [earlyTemplateScale_regular a b,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hreg hlow hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hlow
  have hscale : earlyTemplateScale a b n 0/earlyTemplateScale a b n (prefixTime n) ≤
      (n : ℝ)^b := by
    unfold earlyTemplateScale
    rw [earlyDensity_prefix,mul_div_mul_left _ _ (ne_of_gt (pow_pos hn0 a)),← div_pow]
    apply pow_le_pow_left₀ (div_nonneg (by
      have hh := (earlyDensity_antitone n (Nat.zero_le (prefixTime n)))
      change prefixDensity n ≤ earlyDensity n 0 at hh
      linarith) hp.le)
    apply (div_le_iff₀ hp).mpr
    have hp' := (div_le_iff₀ hn0).mp hlow
    have hzero : earlyDensity n 0 ≤ 1 := by unfold earlyDensity; simp
    nlinarith only [hp',hzero]
  have hlog := Real.log_le_log
    (div_pos (hreg.1 0 (Nat.zero_le _)) (hreg.1 (prefixTime n) le_rfl)) hscale
  rw [Real.log_pow] at hlog
  exact (relativeScaleBudget_le_log (earlyTemplateScale a b n) (prefixTime n)
    hreg.1 hreg.2.1 hreg.2.2).trans (by nlinarith only [hlog])

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EarlyDensityOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyDensity_le_one (n i : ℕ) : earlyDensity n i ≤ 1 := by
  unfold earlyDensity
  have h₁ : 0 ≤ 1/(n : ℝ) := by positivity
  have h₂ : 0 ≤ 6*(i : ℝ)/(n : ℝ)^2 := by positivity
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_FixedEndpointPairInjective
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma fixedEndpoint_pair_injective {n : ℕ} (u : Fin n) :
    Function.Injective (fun w : Fin n => ({u,w} : Finset (Fin n))) := by
  intro a b h
  change ({u,a} : Finset (Fin n)) = {u,b} at h
  have ha : a = u ∨ a = b := by
    have hh : a ∈ ({u,b} : Finset (Fin n)) := by rw [← h]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hb : b = u ∨ b = a := by
    have hh : b ∈ ({u,a} : Finset (Fin n)) := by rw [h]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  aesop

theorem wedge_copyEdgeLoad_le_two {n : ℕ} (u v : Fin n) (G : Graph n)
    (e : Finset (Fin n)) : copyEdgeLoad (wedgeEdges u v) G e ≤ 2 := by
  classical
  let A (x : Fin n) := Finset.univ.filter (fun w : Fin n => e = ({x,w} : Finset (Fin n)))
  have hA (x : Fin n) : (A x).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply fixedEndpoint_pair_injective x
    exact ((Finset.mem_filter.mp ha).2).symm.trans (Finset.mem_filter.mp hb).2
  have hf : Finset.univ.filter (fun w : Fin n => e ∈ wedgeEdges u v w) = A u ∪ A v := by
    ext w
    simp [A,wedgeEdges]
  have hc : (Finset.univ.filter (fun w : Fin n => e ∈ wedgeEdges u v w)).card ≤ 2 := by
    rw [hf]
    exact (Finset.card_union_le _ _).trans (by have := hA u; have := hA v; omega)
  unfold copyEdgeLoad
  calc
    _ ≤ ∑ w : Fin n, if e ∈ wedgeEdges u v w then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro w _
      by_cases h : e ∈ wedgeEdges u v w
      · rw [ite_eq_left h,ite_eq_left h]
        unfold intact
        split <;> norm_num
      · rw [ite_eq_right h,ite_eq_right h]
    _ = ((Finset.univ.filter (fun w : Fin n => e ∈ wedgeEdges u v w)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ 2 := by exact_mod_cast hc

lemma wedge_copyLoadSafe {n : ℕ} (u v : Fin n) (G : Graph n) :
    copyLoadSafe (wedgeEdges u v) 2 G := by
  intro e _
  exact wedge_copyEdgeLoad_le_two u v G e

lemma wedge_pastRelativeCopyLoadsSafe {n : ℕ} (u v : Fin n) (T j : ℕ)
    (ω : History (Graph n) T) :
    pastRelativeCopyLoadsSafe (wedgeEdges u v) (fun _ => 2) T j ω := by
  intro k _
  exact wedge_copyLoadSafe u v _

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IncidentTriangleThird
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma incidentTriangle_third {n : ℕ} {G : Graph n} {u v : Fin n}
    (huv : u ≠ v) {t : Finset (Fin n)} (ht : t ∈ incidentTriangles G {u,v}) :
    ∃ w ∈ commonNeighbors G u v, t = {u,v,w} ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨ht,hpair⟩ := Finset.mem_filter.mp ht
  obtain ⟨htcard,htG⟩ := mem_triangles.mp ht
  have hsub : ({u,v} : Finset (Fin n)) ⊆ t := (Finset.mem_powersetCard.mp hpair).1
  have hc : (t \ {u,v}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, htcard, Finset.card_pair huv]
  obtain ⟨w,heq⟩ := Finset.card_eq_one.mp hc
  have hw : w ∈ t \ {u,v} := by rw [heq]; simp
  obtain ⟨hwt,hwuv⟩ := Finset.mem_sdiff.mp hw
  have huw : u ≠ w := by intro h; apply hwuv; simp [h]
  have hvw : v ≠ w := by intro h; apply hwuv; simp [h]
  have htriple : t = {u,v,w} := by
    have hu := Finset.sdiff_union_of_subset hsub
    rw [heq] at hu
    rw [← hu]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hcw : w ∈ commonNeighbors G u v := by
    apply (mem_commonNeighbors G u v w).mpr
    constructor
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair huw⟩
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair hvw⟩
  exact ⟨w,hcw,htriple,huw,hvw⟩

lemma incidentTriangles_eq_image {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    incidentTriangles G {u,v} = (commonNeighbors G u v).image (fun w => {u,v,w}) := by
  have huv : u ≠ v := by
    intro h
    have hh := mem_completeGraph.mp (hG he)
    simp [h] at hh
  ext t
  constructor
  · intro ht
    obtain ⟨w,hw,rfl,_,_⟩ := incidentTriangle_third huv ht
    exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
  · intro ht
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨(triangle_closure_iff hG huv hw).mpr he,?_⟩
    exact Finset.mem_powersetCard.mpr ⟨by simp,Finset.card_pair huv⟩

theorem triangleDegree_eq_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    triangleDegree G {u,v} = currentCodegree G u v := by
  unfold triangleDegree currentCodegree
  rw [incidentTriangles_eq_image hG he]
  apply Finset.card_image_of_injOn
  intro a ha b _ hab
  change ({u,v,a} : Finset (Fin n)) = {u,v,b} at hab
  have ha' : a ∈ ({u,v,b} : Finset (Fin n)) := by rw [← hab]; simp
  have hnea := commonNeighbors_ne hG ha
  simpa [hnea.1.symm,hnea.2.symm] using ha'

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedFailure_eq_one_sub (p : PMF (Bool × Bool)) :
    markedFailure p = 1 - markedSuccess p := by
  unfold markedFailure markedSuccess
  rw [← pmfMean_const p 1, ← pmfMean_sub]
  apply pmfMean_congr
  intro z _
  cases z.1 <;> simp

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProspectiveFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedGood_bind {α : Type*} [Fintype α] (π : PMF α)
    (p : α → PMF (Bool × Bool)) :
    markedGood (π.bind p) = pmfMean π (fun a => markedGood (p a)) :=
  pmfMean_bind π p _

@[simp] theorem markedGood_no_marks (p : PMF Bool) :
    markedGood (p.map (fun b => (b,true))) = 1 := by
  rw [markedGood,pmfMean_map]
  simp only [↓reduceIte,pmfMean_const]

@[simp] theorem markedSuccess_no_marks (p : PMF Bool) :
    markedSuccess (p.map (fun b => (b,true))) = (p true).toReal := by
  rw [markedSuccess,pmfMean_map]
  simp [pmfMean]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixDTendstoTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma prefixD_tendsto_atTop : Tendsto prefixD atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show ∀ᶠ n : ℕ in atTop, (n : ℝ)^(1/1000 : ℝ) ≤ prefixD n from
      prefixD_eventual_envelope.mono (fun _ h => h.1))
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/1000)).comp
    tendsto_natCast_atTop_atTop

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_MainProbabilityPrefixFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma expectation_normalizedLeave (n : ℕ) :
    expectation n (normalizedLeave n) =
      expectation n (fun H => (H.card : ℝ))/normalization n := by
  change pmfMean (terminalLaw n) (fun graph => (graph.card : ℝ)/normalization n) =
    pmfMean (terminalLaw n) (fun graph => (graph.card : ℝ))/normalization n
  simp only [div_eq_mul_inv,pmfMean_mul_const]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleLiftCount
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma intact_union {n : ℕ} (F E G : Graph n) :
    intact (F ∪ E) G = intact F G * intact E G := by
  classical
  unfold intact
  by_cases hF : F ⊆ G <;> by_cases hE : E ⊆ G <;>
    simp [hF,hE,Finset.union_subset_iff]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighborsComplete
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma commonNeighbors_complete {n : ℕ} (u v : Fin n) :
    commonNeighbors (completeGraph n) u v = Finset.univ \ {u,v} := by
  ext w
  simp only [mem_commonNeighbors,mem_completeGraph,Finset.mem_sdiff,
    Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_and]
  by_cases hu : u = w <;> by_cases hv : v = w <;>
    simp [hu,hv,eq_comm]

lemma currentCodegree_complete {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    currentCodegree (completeGraph n) u v = n-2 := by
  rw [currentCodegree,commonNeighbors_complete]
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ]
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_pair huv]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RelativeCopyNoiseFirst
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem relativeCopyNoise_first_crossing {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hL : ∀ k < T, 0 ≤ L k) (hjump : ∀ k < T, 3*L k/s (k+1) ≤ c)
    (r : ℝ) (hr : 0 < r) (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure G) (fun _ => step) T T).support)
    (j : ℕ) (hj : j ≤ T) (hloads : pastRelativeCopyLoadsSafe required L T j ω)
    (hcounts : ∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k)
    (hcross : r ≤ |historyNoise (fun _ => step)
      (fun k H => copyCount required H/s k) T j ω|) :
    ∃ m ≤ T, pastRelativeCopyLoadsSafe required L T m ω ∧
      r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T m ω| ∧
      historyCounter (relativeCopyVarianceRate required L s) T m ω ≤
        c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c) := by
  classical
  let f := fun k H => copyCount required H/s k
  let P : ℕ → Prop := fun m => r ≤ |historyNoise (fun _ => step) f T m ω|
  have hex : ∃ m, P m := ⟨j,hcross⟩
  let m := Nat.find hex
  have hmj : m ≤ j := Nat.find_min' hex hcross
  have hmT : m ≤ T := hmj.trans hj
  have hm : P m := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    have : r ≤ (0 : ℝ) := by simpa [P,he] using hm
    linarith
  obtain ⟨k,he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  have hkm : k < m := by omega
  have hkT : k < T := hkm.trans_le hmT
  have hprev : |historyNoise (fun _ => step) f T k ω| < r := by
    exact lt_of_not_ge (Nat.find_min hex hkm)
  have hsafe : pastRelativeCopyLoadsSafe required L T m ω := by
    intro a ha
    apply hloads a
    exact lt_of_lt_of_le ha (min_le_min_right T hmj)
  obtain ⟨hinit,hpath⟩ := historyLaw_path_support (PMF.pure G) (fun _ => step) T T le_rfl ω hω
  have hG : ω (historyIndex T 0) = G := by
    simpa only [PMF.mem_support_pure_iff] using hinit
  have hload : copyLoadSafe required (L k) (ω (historyIndex T k)) := by
    apply hsafe k
    simpa [Nat.min_eq_left hmT] using hkm
  have hinc : |historyIncrement (fun _ => step) f T k ω| ≤ c := by
    unfold historyIncrement
    simp only [f,div_eq_mul_inv,pmfMean_mul_const,← sub_mul,abs_mul,
      abs_of_pos (inv_pos.mpr (hs (k+1) (by omega)))]
    have hh := pmf_centered_of_loss_range (step (ω (historyIndex T k))) (copyCount required)
      (copyCount required (ω (historyIndex T k))) (3*L k)
      (fun H hH => copyCount_step_loss_range required _ H (L k) (hL k hkT) hload hH)
      _ (hpath k hkT)
    exact (mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (hs (k+1) (by omega)).le)).trans
      (by simpa only [div_eq_mul_inv] using hjump k hkT)
  have hM : historyNoise (fun _ => step) f T m ω ≤ r+c := by
    rw [he,historyNoise_succ_same _ _ T k hkT]
    have hp := le_abs_self (historyNoise (fun _ => step) f T k ω)
    have hi := le_abs_self (historyIncrement (fun _ => step) f T k ω)
    linarith
  refine ⟨m,hmT,hsafe,hm,?_⟩
  have hv := relativeCopyCounter_le required T m hmT L s c B hc.le hB hs hdec hjump ω
    (fun a ha => hcounts a (ha.trans_le hmj))
  rw [hG] at hv
  exact hv.trans (mul_le_mul_of_nonneg_left (by dsimp [f] at hM; linarith) hc.le)

open Classical in

theorem triangle_relative_template_self_bounded_tail {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hL : ∀ k < T, 0 ≤ L k) (hjump : ∀ k < T, 3*L k/s (k+1) ≤ c)
    (r : ℝ) (hr : 0 < r) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
        (∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) ∧
        r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω|
        then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp
        (-r^2/(4*(c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c)+c*r))) := by
  have hs' : ∀ k < T, 0 < s (k+1) := fun k hk => hs (k+1) (by omega)
  have hV : 0 ≤ c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c) := by
    have hz := hs 0 (Nat.zero_le T)
    have hn := copyCount_nonneg required G
    have hb := relativeScaleBudget_nonneg s T hs hdec
    positivity
  apply le_trans _ (triangle_relative_template_before_load_exit required G T L s c hc hs' hL
    hjump r (c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c)) hr hV)
  apply pmfMean_mono
  intro ω hω
  by_cases hex : ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
      (∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) ∧
      r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω|
  · obtain ⟨j,hj,hloads,hcounts,hcross⟩ := hex
    have hh := relativeCopyNoise_first_crossing required G T L s c B hc hB hs hdec hL hjump
      r hr ω hω j hj hloads hcounts hcross
    rw [ite_eq_left ⟨j,hj,hloads,hcounts,hcross⟩,ite_eq_left hh]
  · rw [ite_eq_right hex]
    split <;> norm_num

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeNoiseRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem codegree_noise_exponent_lower : ∀ᶠ n : ℕ in atTop,
    (n : ℝ)^(1/2500 : ℝ) ≤ codegreeNoiseRadius n^2/codegreeNoiseDenominator n := by
  have hlog := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2500)).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1/384)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^(1/2500 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2500)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixD_eventual_envelope,prefixD_tendsto_atTop.eventually_ge_atTop 6,
    hlog,hpow.eventually_ge_atTop 336,eventually_ge_atTop (1 : ℕ)] with n hD hD6 hl hn336 hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hD0 : 0 < prefixD n := by linarith
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hc0 : 0 < 6/prefixD n := by positivity
  have hc1 : 6/prefixD n ≤ 1 := (div_le_one hD0).mpr hD6
  have hr0 : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hr1 : codegreeNoiseRadius n ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hc : 6/prefixD n ≤ 6*(n : ℝ)^(-1/1000 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6)
      (Real.rpow_pos_of_pos hn0 (1/1000 : ℝ)) hD.1
    calc
      _ ≤ 6/(n : ℝ)^(1/1000 : ℝ) := hh
      _ = _ := by
        rw [show (-1/1000 : ℝ) = -(1/1000 : ℝ) by norm_num,Real.rpow_neg hn0.le]
        rfl
  have hr2 : codegreeNoiseRadius n^2 = (n : ℝ)^(-1/5000 : ℝ) := by
    unfold codegreeNoiseRadius
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hd0 : 0 < codegreeNoiseDenominator n := by unfold codegreeNoiseDenominator; positivity
  have hd : codegreeNoiseDenominator n ≤ (n : ℝ)^(-1/1000 : ℝ)*(24*(7+8*Real.log n)) := by
    unfold codegreeNoiseDenominator
    calc
      _ = 4*(6/prefixD n)*(4+8*Real.log n+codegreeNoiseRadius n+6/prefixD n+codegreeNoiseRadius n) := by ring
      _ ≤ 4*(6/prefixD n)*(7+8*Real.log n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hr1,hc1]
      _ ≤ 4*(6*(n : ℝ)^(-1/1000 : ℝ))*(7+8*Real.log n) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hsmall : 24*(7+8*Real.log (n : ℝ)) ≤ (n : ℝ)^(1/2500 : ℝ) := by
    dsimp at hl
    rw [abs_of_nonneg hln,abs_of_nonneg (Real.rpow_nonneg hn0.le (1/2500 : ℝ))] at hl
    linarith only [hl,hn336]
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hsmall
    (Real.rpow_nonneg hn0.le (-1/1000 : ℝ)))
  apply (le_div_iff₀ hd0).mpr
  have hh := mul_le_mul_of_nonneg_left hd' (Real.rpow_nonneg hn0.le (1/2500 : ℝ))
  rw [← Real.rpow_add hn0,← Real.rpow_add hn0] at hh
  rw [hr2]
  convert hh using 1; norm_num

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma earlyTriangleScale_regular : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n (i+1) ≤ earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1)) ∧
    relativeScaleBudget (earlyTriangleScale n) (prefixTime n) ≤ 6*Real.log n := by
  filter_upwards [earlyTemplateScale_regular 3 3,earlyTemplateScale_log_budget 3 3] with n hr hb
  refine ⟨fun i hi => div_pos (hr.1 i hi) (by norm_num),?_,?_,?_⟩
  · intro i hi
    exact div_le_div_of_nonneg_right (hr.2.1 i hi) (by norm_num)
  · intro i hi
    have hh := div_le_div_of_nonneg_right (hr.2.2 i hi) (by norm_num : (0 : ℝ) ≤ 6)
    simpa only [earlyTriangleScale,mul_div_assoc] using hh
  · convert hb using 1
    · unfold relativeScaleBudget earlyTriangleScale
      congr 1
      ext i
      ring
    · norm_num

lemma triangleDegree_complete {n : ℕ} (e : Finset (Fin n)) (he : e ∈ completeGraph n) :
    triangleDegree (completeGraph n) e = n-2 := by
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp he)
  rw [triangleDegree_eq_codegree (Finset.Subset.refl _) he,currentCodegree_complete u v huv]

lemma triangleCount_complete_formula {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ) = (n : ℝ)*(n-1)*(n-2)/6 := by
  have hh := triangle_degree_sum (completeGraph n)
  have he : (∑ e ∈ completeGraph n, (triangleDegree (completeGraph n) e : ℝ)) =
      ((completeGraph n).card : ℝ)*(n-2) := by
    calc
      _ = ∑ _e ∈ completeGraph n, ((n-2 : ℕ) : ℝ) := Finset.sum_congr rfl (fun e he => by rw [triangleDegree_complete e he])
      _ = _ := by simp [Nat.cast_sub hn]; ring
  rw [he,card_completeGraph,Nat.cast_choose_two] at hh
  nlinarith only [hh]

lemma initial_triangle_relative_error {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ)/earlyTriangleScale n 0-1 = -1/((n : ℝ)-1)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  have hs : earlyTriangleScale n 0 = ((n : ℝ)-1)^3/6 := by
    unfold earlyTriangleScale earlyTemplateScale earlyDensity
    simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero]
    field_simp
  rw [triangleCount_complete_formula hn,hs]
  field_simp
  ring

lemma initial_triangle_ratio_le_two {n : ℕ} (hn : 2 ≤ n) :
    copyCount (triangleRequired (n := n)) (completeGraph n)/earlyTriangleScale n 0 ≤ 2 := by
  rw [triangle_copyCount]
  have hh := initial_triangle_relative_error hn
  have hz : 0 ≤ 1/((n : ℝ)-1)^2 := by positivity
  rw [neg_div] at hh
  linarith

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeRelativeNoiseTail
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Classical in

theorem codegree_relative_noise_tail {n : ℕ} (u v : Fin n) (G : Graph n)
    (T : ℕ) (s : ℕ → ℝ) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hjump : ∀ k < T, 6/s (k+1) ≤ c) (r : ℝ) (hr : 0 < r) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T,
        (∀ k < j, (currentCodegree (ω (historyIndex T k)) u v : ℝ) ≤ B*s k) ∧
        r ≤ |historyNoise (fun _ => step)
          (fun k H => (currentCodegree H u v : ℝ)/s k) T j ω| then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp
        (-r^2/(4*(c*((currentCodegree G u v : ℝ)/s 0+B*relativeScaleBudget s T+r+c)+c*r))) := by
  have ht := triangle_relative_template_self_bounded_tail (wedgeEdges u v) G T
    (fun _ => 2) s c B hc hB hs hdec (fun _ _ => by norm_num)
    (fun k hk => by simpa only [show (3 : ℝ)*2 = 6 by norm_num] using hjump k hk) r hr
  simp_rw [← currentCodegree_copyCount] at ht
  apply le_trans _ ht
  apply pmfMean_mono
  intro ω _
  by_cases hex : ∃ j ≤ T,
      (∀ k < j, (currentCodegree (ω (historyIndex T k)) u v : ℝ) ≤ B*s k) ∧
      r ≤ |historyNoise (fun _ => step)
        (fun k H => (currentCodegree H u v : ℝ)/s k) T j ω|
  · obtain ⟨j,hj,hcounts,hcross⟩ := hex
    rw [ite_eq_left ⟨j,hj,hcounts,hcross⟩,
      ite_eq_left ⟨j,hj,wedge_pastRelativeCopyLoadsSafe u v T j ω,hcounts,hcross⟩]
  · rw [ite_eq_right hex]
    split <;> norm_num

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeVertexCount
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma codegree_le_vertex_count {n : ℕ} (G : Graph n) (u v : Fin n) :
    currentCodegree G u v ≤ n := by
  unfold currentCodegree
  exact (Finset.card_le_univ _).trans (by simp)

lemma earlyCodegreeScale_ge_prefixD (n i : ℕ) (hi : i ≤ prefixTime n)
    (hp : 0 ≤ prefixDensity n) : prefixD n ≤ earlyTemplateScale 1 2 n i := by
  unfold earlyTemplateScale prefixD
  rw [pow_one]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp (earlyDensity_antitone n hi) 2) (Nat.cast_nonneg n)

lemma initial_codegree_relative_le_four {n : ℕ} (hn : 2 ≤ n) (u v : Fin n) :
    (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0 ≤ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1/2 : ℝ) ≤ earlyDensity n 0 := by
    have hh : 1/(n : ℝ) ≤ 1/2 := (div_le_iff₀ hn0).mpr (by linarith)
    simp only [earlyDensity,Nat.cast_zero,mul_zero,zero_div,sub_zero]
    linarith
  have hs : (n : ℝ)/4 ≤ earlyTemplateScale 1 2 n 0 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hp 2)
      hn0.le
    unfold earlyTemplateScale
    norm_num only [pow_one,div_pow,one_pow] at hh ⊢
    nlinarith only [hh]
  apply (div_le_iff₀ (lt_of_lt_of_le (by positivity) hs)).mpr
  have hh : (currentCodegree (completeGraph n) u v : ℝ) ≤ n := by
    exact_mod_cast codegree_le_vertex_count (completeGraph n) u v
  linarith

open Classical in

theorem prefix_codegree_relative_noise_bound : ∀ᶠ n : ℕ in atTop,
    ∀ u v : Fin n, ∀ r : ℝ, 0 < r →
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n))
      (fun ω => if ∃ j ≤ prefixTime n,
        (∀ k < j, (currentCodegree (ω (historyIndex (prefixTime n) k)) u v : ℝ) ≤
          2*earlyTemplateScale 1 2 n k) ∧
        r ≤ |historyNoise (fun _ => step)
          (fun k H => (currentCodegree H u v : ℝ)/earlyTemplateScale 1 2 n k)
          (prefixTime n) j ω| then 1 else 0) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp
        (-r^2/(4*((6/prefixD n)*(4+8*Real.log n+r+6/prefixD n)+(6/prefixD n)*r))) := by
  filter_upwards [earlyTemplateScale_regular 1 2,earlyTemplateScale_log_budget 1 2,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (2 : ℕ)] with n hreg hbudget hp hn
  intro u v r hr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hp
  have hD : 0 < prefixD n := by unfold prefixD; positivity
  have hc : 0 < 6/prefixD n := by positivity
  have hjump : ∀ k < prefixTime n, 6/earlyTemplateScale 1 2 n (k+1) ≤ 6/prefixD n := by
    intro k hk
    exact div_le_div_of_nonneg_left (by norm_num) hD
      (earlyCodegreeScale_ge_prefixD n (k+1) (by omega) hpp.le)
  have ht := codegree_relative_noise_tail u v (completeGraph n) (prefixTime n)
    (earlyTemplateScale 1 2 n) (6/prefixD n) 2 hc (by norm_num)
    hreg.1 hreg.2.1 hjump r hr
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div]
  apply neg_le_neg
  have hinit := initial_codegree_relative_le_four hn u v
  have hz := relativeScaleBudget_nonneg (earlyTemplateScale 1 2 n) (prefixTime n)
    hreg.1 hreg.2.1
  have hi0 : 0 ≤ (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0 :=
    div_nonneg (Nat.cast_nonneg _) (hreg.1 0 (Nat.zero_le _)).le
  have hd0 : 0 < 4*((6/prefixD n)*
      ((currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0+
        2*relativeScaleBudget (earlyTemplateScale 1 2 n) (prefixTime n)+r+6/prefixD n)+
        (6/prefixD n)*r) := by positivity
  apply div_le_div_of_nonneg_left (sq_nonneg r) hd0
  have hh := mul_le_mul_of_nonneg_left (show
      (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0+
        2*relativeScaleBudget (earlyTemplateScale 1 2 n) (prefixTime n)+r+6/prefixD n ≤
        4+8*Real.log n+r+6/prefixD n by norm_num at hbudget; linarith)
    hc.le
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeRadius
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter
open Classical

namespace SharpTerminalLeave

lemma early_density_positive {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) {i : ℕ} (hi : i ≤ prefixTime n) :
    0 < earlyDensity n i := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (hp.trans (earlyDensity_antitone n hi))

lemma early_density_log_bound {n i : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i ≤ prefixTime n) :
    -Real.log (earlyDensity n i) ≤ Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : Real.log (1/(n : ℝ)) ≤ Real.log (earlyDensity n i) :=
    Real.log_le_log (by positivity) (hp.trans (earlyDensity_antitone n hi))
  rw [one_div,Real.log_inv] at hh
  linarith

lemma early_density_survival_budget {n i : ℕ} (hn : 2 ≤ n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i ≤ prefixTime n)
    {b η : ℝ} (hb : 0 ≤ b) (hη : 0 ≤ η) :
    b*(1-earlyDensity n 0)/earlyDensity n 0+b*(6/(n : ℝ)^2)/earlyDensity n i+
      2*b*η*(-Real.log (earlyDensity n i))+b^2/(n*earlyDensity n i^2) ≤
        8*b/(n : ℝ)+2*b*η*Real.log n+b^2/prefixD n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hp0 : 0 < earlyDensity n 0 := early_density_positive (by omega) hp (Nat.zero_le _)
  have hpi := early_density_positive (by omega) hp hi
  have hpT : 0 < prefixDensity n := early_density_positive (by omega) hp le_rfl
  have hlow : 1/(n : ℝ) ≤ earlyDensity n i := hp.trans (earlyDensity_antitone n hi)
  have hab : b*(1-earlyDensity n 0)/earlyDensity n 0 ≤ 2*b/(n : ℝ) := by
    have hz : earlyDensity n 0 = 1-1/(n : ℝ) := by simp [earlyDensity]
    have hhalf : (1 : ℝ)/2 ≤ earlyDensity n 0 := by
      rw [hz]
      have hinv : 1/(n : ℝ) ≤ 1/2 := (div_le_div_iff₀ hn0 (by norm_num)).mpr (by linarith)
      linarith
    apply (div_le_iff₀ hp0).mpr
    rw [hz]
    have hm := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*b/(n : ℝ) by positivity)
    rw [hz] at hm
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]
  have hdisc : b*(6/(n : ℝ)^2)/earlyDensity n i ≤ 6*b/(n : ℝ) := by
    calc
      _ ≤ b*(6/(n : ℝ)^2)/(1/(n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
      _ = _ := by field_simp
  have hlog : 2*b*η*(-Real.log (earlyDensity n i)) ≤ 2*b*η*Real.log n :=
    mul_le_mul_of_nonneg_left (early_density_log_bound (by omega) hp hi) (by positivity)
  have hlast : b^2/(n*earlyDensity n i^2) ≤ b^2/prefixD n := by
    apply div_le_div_of_nonneg_left (sq_nonneg b) (by unfold prefixD; positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hpT.le (earlyDensity_antitone n hi) 2) hn0.le
  simp only [div_eq_mul_inv] at hab hdisc hlog hlast ⊢
  linarith only [hab,hdisc,hlog,hlast]

lemma prefix_survival_budget_small : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeRadius n ∧ prefixEdgeRadius n ≤ 1/2 ∧
    ∀ b : ℝ, 0 ≤ b → b ≤ (n : ℝ)^(1/200000 : ℝ) →
      8*b/(n : ℝ)+2*b*prefixEdgeRadius n*Real.log n+b^2/prefixD n ≤ 1 := by
  have hlim : Tendsto (fun n : ℕ =>
      8*(n : ℝ)^(-1/2 : ℝ)+2*(n : ℝ)^(-1/100000 : ℝ)+(n : ℝ)^(-1/2000 : ℝ))
      atTop (nhds 0) := by
    have ha := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
    have hb := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100000)).comp tendsto_natCast_atTop_atTop
    have hc := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2000)).comp tendsto_natCast_atTop_atTop
    convert ((ha.const_mul 8).add (hb.const_mul 2)).add hc using 1 <;> norm_num
  have hrad : Tendsto prefixEdgeRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-1/40000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/40000)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hrad.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/200000) zero_lt_one,
    prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hlim hrad hlog hD hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlog' : Real.log (n : ℝ) ≤ (n : ℝ)^(1/200000 : ℝ) := by
    simp only [prefixTemplateFactor,Real.rpow_one,one_mul] at hlog
    linarith
  refine ⟨Real.rpow_nonneg hn0.le _,hrad,?_⟩
  intro b hb hbhigh
  have hfirst : b/(n : ℝ) ≤ (n : ℝ)^(-1/2 : ℝ) := by
    calc
      _ ≤ (n : ℝ)^(1/200000 : ℝ)/(n : ℝ) := div_le_div_of_nonneg_right hbhigh hn0.le
      _ = (n : ℝ)^((1/200000 : ℝ)-1) := by rw [Real.rpow_sub hn0,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hmiddle : b*prefixEdgeRadius n*Real.log n ≤ (n : ℝ)^(-1/100000 : ℝ) := by
    calc
      _ ≤ ((n : ℝ)^(1/200000 : ℝ)*(n : ℝ)^(-1/40000 : ℝ))*(n : ℝ)^(1/200000 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbhigh (Real.rpow_nonneg hn0.le _))
          hlog' hlog0 (by positivity)
      _ = (n : ℝ)^((1/200000 : ℝ)-1/40000+1/200000) := by
        rw [← Real.rpow_add hn0,← Real.rpow_add hn0]; congr 1; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hlast : b^2/prefixD n ≤ (n : ℝ)^(-1/2000 : ℝ) := by
    calc
      _ ≤ ((n : ℝ)^(1/200000 : ℝ))^2/(n : ℝ)^(1/1000 : ℝ) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ hb hbhigh 2) (by positivity) hD.1
      _ = (n : ℝ)^((1/200000 : ℝ)*2-1/1000) := by
        rw [← Real.rpow_mul_natCast hn0.le,Real.rpow_sub hn0]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  simp only [div_eq_mul_inv] at hfirst hlast ⊢
  nlinarith only [hlim,hfirst,hmiddle,hlast]

theorem prefix_killed_survival : ∀ᶠ n : ℕ in atTop,
    ∀ j ≤ prefixTime n, ∀ F : Graph n, (F.card : ℝ) ≤ (n : ℝ)^(1/200000 : ℝ) →
      pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) j)
        (fun ω => if historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
          (prefixTime n) j ω then intact F (ω (historyIndex (prefixTime n) j)) else 0) ≤
      Real.exp 1 * earlyDensity n j^F.card := by
  filter_upwards [prefix_survival_budget_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (2 : ℕ)] with n hbudget hp hn
  intro j hj F hF
  have hk := density_killed_survival (PMF.pure (completeGraph n)) (earlyDensity n)
    (prefixEdgeRadius n) (prefixTime n) j hj (by omega)
    (fun i hi => early_density_positive (by omega) hp hi)
    (fun i _ => earlyDensity_succ n i) (earlyDensity_le_one n 0) hbudget.1 hbudget.2.1 F
  apply hk.trans
  rw [mul_comm (Real.exp 1)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (early_density_positive (by omega) hp hj).le _)
  apply Real.exp_le_exp.mpr
  exact (early_density_survival_budget hn hp hj (Nat.cast_nonneg _) hbudget.1).trans
    (hbudget.2.2 F.card (Nat.cast_nonneg _) hF)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_FallingFactorialNormalizedProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma fallingFactorial_normalized_product (r a n : ℕ) (hn : r+a ≤ n) (hn0 : 0 < n) :
    ((n-r).descFactorial a : ℝ)/(n : ℝ)^a =
      ∏ i ∈ Finset.range a, (1-((r+i : ℕ) : ℝ)/(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  have hh : (n : ℝ)^a = ∏ _i ∈ Finset.range a, (n : ℝ) := by simp
  rw [hh,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hri : r+i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [Nat.sub_sub,Nat.cast_sub hri]
  field_simp

theorem fallingFactorial_normalized_error (r a n : ℕ) (hn : r+a ≤ n) (hn0 : 0 < n) :
    |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-1| ≤
      (a : ℝ)*(r+a : ℕ)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [fallingFactorial_normalized_product r a n hn hn0]
  let f := fun i : ℕ => 1-((r+i : ℕ) : ℝ)/(n : ℝ)
  have hf : ∀ i ∈ Finset.range a, f i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    have hri : r+i ≤ n := by have := Finset.mem_range.mp hi; omega
    have h0 : 0 ≤ ((r+i : ℕ) : ℝ)/(n : ℝ) := by positivity
    have h1 : ((r+i : ℕ) : ℝ)/(n : ℝ) ≤ 1 := by
      apply (div_le_one hnR).mpr
      exact_mod_cast hri
    exact ⟨by dsimp [f]; linarith,by dsimp [f]; linarith⟩
  have hh := abs_prod_sub_prod_le_sum (Finset.range a) f (fun _ => 1) hf
    (fun _ _ => ⟨zero_le_one,le_rfl⟩)
  simp only [Finset.prod_const_one] at hh
  apply hh.trans
  calc
    (∑ i ∈ Finset.range a, |f i-1|) =
        ∑ i ∈ Finset.range a, ((r+i : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      have h0 : 0 ≤ ((r+i : ℕ) : ℝ)/(n : ℝ) := by positivity
      rw [show 1-((r+i : ℕ) : ℝ)/(n : ℝ)-1 = -(((r+i : ℕ) : ℝ)/(n : ℝ)) by ring,
        abs_neg,abs_of_nonneg h0]
    _ ≤ ∑ _i ∈ Finset.range a, ((r+a : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ hnR.le
      exact_mod_cast (by have := Finset.mem_range.mp hi; omega : r+i ≤ r+a)
    _ = _ := by simp; ring

theorem initialDensity_power_error (b n : ℕ) (hn : 1 ≤ n) :
    |(1-1/(n : ℝ))^b-1| ≤ (b : ℝ)/(n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 ≤ 1-1/(n : ℝ) := by
    have : 1/(n : ℝ) ≤ 1 := by apply (div_le_one (by linarith)).mpr; exact hnR
    linarith
  have hp1 : 1-1/(n : ℝ) ≤ 1 := by
    have : 0 ≤ 1/(n : ℝ) := by positivity
    linarith
  have hh := abs_prod_sub_prod_le_sum (Finset.range b) (fun _ => 1-1/(n : ℝ))
    (fun _ => 1) (fun _ _ => ⟨hp0,hp1⟩) (fun _ _ => ⟨zero_le_one,le_rfl⟩)
  simpa only [Finset.prod_const,Finset.card_range,one_pow,
    show 1-1/(n : ℝ)-1 = -(1/(n : ℝ)) by ring,abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1/(n : ℝ)),Finset.sum_const,
    nsmul_eq_mul,mul_one_div] using hh

theorem initialRootedScaling_error (r a b n : ℕ) (hn : r+a ≤ n) (hn2 : 2 ≤ n) :
    |((n-r).descFactorial a : ℝ) /
      ((n : ℝ)^a * (1-1/(n : ℝ))^b)-1| ≤
      (2 : ℝ)^b * ((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : 0 < n := by omega
  have hnR0 : (0 : ℝ) < n := by linarith
  have hp : (1/2 : ℝ) ≤ 1-1/(n : ℝ) := by
    have hh : 1/(n : ℝ) ≤ 1/2 := (div_le_div_iff₀ hnR0 (by norm_num)).mpr (by linarith)
    linarith
  have hp0 : 0 < (1-1/(n : ℝ))^b := pow_pos (by linarith) _
  have hi : 1/(1-1/(n : ℝ))^b ≤ (2 : ℝ)^b := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hp b
    have hh2 : (1/2 : ℝ)^b = 1/(2 : ℝ)^b := by rw [div_pow,one_pow]
    rw [hh2] at hh
    exact (div_le_iff₀ hp0).mpr (by
      have ht : (0 : ℝ) < (2 : ℝ)^b := by positivity
      have hmul := (div_le_iff₀ ht).mp hh
      simpa only [mul_comm] using hmul)
  have hf := fallingFactorial_normalized_error r a n hn hn0
  have ht := initialDensity_power_error b n (by omega)
  have he : |((n-r).descFactorial a : ℝ) /
      ((n : ℝ)^a*(1-1/(n : ℝ))^b)-1| =
      |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b| /
        (1-1/(n : ℝ))^b := by
    calc
      _ = |(((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b) /
          (1-1/(n : ℝ))^b| := by
        rw [sub_div,div_self (ne_of_gt hp0),div_div]
      _ = _ := by rw [abs_div,abs_of_pos hp0]
  rw [he,div_eq_mul_inv]
  have he2 : |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b| ≤
      ((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ) := by
    calc
      _ ≤ |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-1| +
          |(1-1/(n : ℝ))^b-1| := by
        simpa only [abs_sub_comm (1 : ℝ)] using
          (abs_sub_le (((n-r).descFactorial a : ℝ)/(n : ℝ)^a) 1 ((1-1/(n : ℝ))^b))
      _ ≤ (a : ℝ)*(r+a : ℕ)/(n : ℝ)+(b : ℝ)/(n : ℝ) := add_le_add hf ht
      _ = _ := by ring
  calc
    _ ≤ (((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ)) * (2 : ℝ)^b :=
      mul_le_mul he2 (by simpa only [one_div] using hi) (inv_nonneg.mpr hp0.le)
        (by positivity)
    _ = _ := by ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedInjectionEquivFree
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem card_rootedInjection {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    Fintype.card (RootedInjection T ψ) =
      (n-T.roots.card).descFactorial (k-T.roots.card) := by
  classical
  rw [Fintype.card_congr (rootedInjectionEquivFree T ψ),Fintype.card_embedding_eq]
  have hfree : Fintype.card {v : Fin k // v ∉ T.roots} = k-T.roots.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      (Fintype.card_subtype_compl (fun v : Fin k => v ∈ T.roots))
  have htarget : Fintype.card {w : Fin n // w ∉ Set.range ψ} = n-T.roots.card := by
    calc
      _ = Fintype.card (↑((Set.range ψ)ᶜ)) := Fintype.card_congr (Equiv.refl _)
      _ = n-T.roots.card := by
        rw [Fintype.card_compl_set,Fintype.card_range,Fintype.card_fin,Fintype.card_coe]
  rw [hfree,htarget]

theorem rootedCount_completeGraph {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    rootedCount T ψ (completeGraph n) =
      ((n-T.roots.card).descFactorial (k-T.roots.card) : ℝ) := by
  classical
  unfold rootedCount copyCount
  have hcontains : ∀ φ : RootedInjection T ψ, imageEdges T φ.val ⊆ completeGraph n := by
    intro φ e he
    exact mem_completeGraph.mpr (imageEdges_simple T φ.val he)
  simp only [intact,ite_eq_left (hcontains _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,card_rootedInjection]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedTemplateEdgesCard
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma rootedTemplate_edges_card_le_sq {k : ℕ} (T : RootedTemplate k) :
    T.edges.card ≤ k^2 := by
  have hh : T.edges ⊆ completeGraph k := by
    intro e he
    exact mem_completeGraph.mpr (T.simple e he)
  exact (Finset.card_le_card hh).trans (by rw [card_completeGraph]; exact Nat.choose_le_pow k 2)

theorem rootedCount_initial_uniform_error (H : ℕ) {k n : ℕ} (hk : k ≤ H)
    (hn : H ≤ n) (hn2 : 2 ≤ n) (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    |rootedCount T ψ (completeGraph n) /
      rootedScaling T n (1-1/(n : ℝ))-1| ≤
      (2 : ℝ)^(H^2) * (2*(H : ℝ)^2)/(n : ℝ) := by
  have hr : T.roots.card ≤ k := by simpa using Finset.card_le_univ T.roots
  have hs : T.roots.card+(k-T.roots.card) = k := Nat.add_sub_of_le hr
  have hb : T.edges.card ≤ H^2 := (rootedTemplate_edges_card_le_sq T).trans
    (Nat.pow_le_pow_left hk 2)
  rw [rootedCount_completeGraph]
  unfold rootedScaling
  have hh := initialRootedScaling_error T.roots.card (k-T.roots.card) T.edges.card n
    (by rw [hs]; exact hk.trans hn) hn2
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
  · rw [hs]
    have ha : (k-T.roots.card : ℕ) ≤ H := (Nat.sub_le _ _).trans hk
    have haR : ((k-T.roots.card : ℕ) : ℝ) ≤ H := by exact_mod_cast ha
    have hkR : (k : ℝ) ≤ H := by exact_mod_cast hk
    have hbR : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by exact_mod_cast hb
    have hmul := mul_le_mul haR hkR (Nat.cast_nonneg k) (Nat.cast_nonneg H)
    nlinarith only [hmul,hbR]
  · positivity
  · positivity

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_BalancedJump
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma earlyTemplateScale_uniform_regular (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ a ≤ H, ∀ b ≤ H^2,
      (∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale a b n (i+1) ≤ earlyTemplateScale a b n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1)) ∧
      relativeScaleBudget (earlyTemplateScale a b n) (prefixTime n) ≤ 2*(b : ℝ)*Real.log n := by
  have hh : ∀ z : Fin (H+1) × Fin (H^2+1), ∀ᶠ n : ℕ in atTop,
      (∀ i ≤ prefixTime n, 0 < earlyTemplateScale z.1.val z.2.val n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale z.1.val z.2.val n (i+1) ≤ earlyTemplateScale z.1.val z.2.val n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale z.1.val z.2.val n i ≤ 2*earlyTemplateScale z.1.val z.2.val n (i+1)) ∧
      relativeScaleBudget (earlyTemplateScale z.1.val z.2.val n) (prefixTime n) ≤ 2*(z.2.val : ℝ)*Real.log n := by
    intro z
    filter_upwards [earlyTemplateScale_regular z.1.val z.2.val,
      earlyTemplateScale_log_budget z.1.val z.2.val] with n hr hb
    exact ⟨hr.1,hr.2.1,hr.2.2,hb⟩
  filter_upwards [Filter.eventually_all.mpr hh] with n hn
  intro a ha b hb
  exact hn (⟨a,by omega⟩,⟨b,by omega⟩)

lemma balanced_jump_budget (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    24*(H : ℝ)^2*(1+Real.log (n : ℝ))^(3*H+2)/prefixD n ≤ balancedJump n := by
  have hc : 0 < 1/(24*(H : ℝ)^2+1) := by positivity
  filter_upwards [prefixTemplateFactor_subpower ((3*H+2 : ℕ) : ℝ) (by norm_num : (0 : ℝ) < 1/2000) hc,
    prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hb hd hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ 1+Real.log (n : ℝ) := by have := Real.log_nonneg hn1; linarith
  have hb' : (1+Real.log (n : ℝ))^(3*H+2 : ℕ) ≤
      1/(24*(H : ℝ)^2+1)*(n : ℝ)^(1/2000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_natCast] using hb
  have hcoef : 24*(H : ℝ)^2/(24*(H : ℝ)^2+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr; linarith
  have hnum : 24*(H : ℝ)^2*(1+Real.log (n : ℝ))^(3*H+2) ≤ (n : ℝ)^(1/2000 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 24*(H : ℝ)^2 by positivity)
    have he := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hn0.le (1/2000 : ℝ))
    ring_nf at hh he ⊢
    exact hh.trans he
  calc
    _ ≤ (n : ℝ)^(1/2000 : ℝ)/(n : ℝ)^(1/1000 : ℝ) :=
      div_le_div₀ (by positivity) hnum (by positivity) hd.1
    _ = _ := by unfold balancedJump; rw [← Real.rpow_sub hn0]; norm_num

lemma rooted_initial_ratio_le_two (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      rootedCount T ψ (completeGraph n)/rootedScaling T n (earlyDensity n 0) ≤ 2 := by
  let C : ℝ := (2 : ℝ)^(H^2)*(2*(H : ℝ)^2)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop C,
    eventually_ge_atTop H,eventually_ge_atTop (2 : ℕ)] with n hC hn hn2
  intro k hk T ψ
  have hh := rootedCount_initial_uniform_error H hk hn hn2 T ψ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdiv : C/(n : ℝ) ≤ 1 := (div_le_one hnR).mpr hC
  have he : earlyDensity n 0 = 1-1/(n : ℝ) := by simp [earlyDensity]
  rw [he]
  have hp := (abs_le.mp hh).2
  change _ ≤ C/(n : ℝ) at hp
  linarith only [hp,hdiv]

lemma balanced_noise_exponent_budget (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    (Real.log (n : ℝ))^2/4 ≤ codegreeNoiseRadius n^2/
      (4*(balancedJump n*(2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n)+
        balancedJump n*codegreeNoiseRadius n)) := by
  let C : ℝ := 20+16*(H : ℝ)^2
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/10000) (one_div_pos.mpr hC),
    prefixTemplateFactor_subpower 2 (by norm_num : (0 : ℝ) < 1/5000) (by norm_num : (0 : ℝ) < 4),
    eventually_ge_atTop (1 : ℕ)] with n hp hl hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hr : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hc : 0 < balancedJump n := Real.rpow_pos_of_pos hn0 _
  have hr1 : codegreeNoiseRadius n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hc1 : balancedJump n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  let d := 4*(balancedJump n*(2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n)+
    balancedJump n*codegreeNoiseRadius n)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hd : d ≤ (n : ℝ)^(-1/2500 : ℝ) := by
    have hp' : 1+Real.log (n : ℝ) ≤ (1/C)*(n : ℝ)^(1/10000 : ℝ) := by
      simpa only [prefixTemplateFactor,Real.rpow_one] using hp
    have hh := mul_le_mul_of_nonneg_left hp' hC.le
    simp only [← mul_assoc,mul_one_div_cancel hC.ne',one_mul] at hh
    have hbracket : 4*(2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n+codegreeNoiseRadius n) ≤
        C*(1+Real.log (n : ℝ)) := by dsimp [C]; nlinarith only [hr1,hc1,hlog,sq_nonneg (H : ℝ)]
    have hm := mul_le_mul_of_nonneg_left (hbracket.trans hh) hc.le
    have he : balancedJump n*(n : ℝ)^(1/10000 : ℝ) = (n : ℝ)^(-1/2500 : ℝ) := by
      unfold balancedJump; rw [← Real.rpow_add hn0]; norm_num
    rw [he] at hm
    dsimp only [d]
    nlinarith only [hm]
  have hr2 : codegreeNoiseRadius n^2 = (n : ℝ)^(-1/5000 : ℝ) := by
    unfold codegreeNoiseRadius
    rw [← Real.rpow_mul_natCast hn0.le]; norm_num
  have hratio : (n : ℝ)^(1/5000 : ℝ) ≤ codegreeNoiseRadius n^2/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hn0.le (1/5000 : ℝ))
    rw [← Real.rpow_add hn0] at hh
    rw [hr2]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hl' : (1+Real.log (n : ℝ))^2 ≤ 4*(n : ℝ)^(1/5000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_two] using hl
  exact (show (Real.log (n : ℝ))^2/4 ≤ (n : ℝ)^(1/5000 : ℝ) by nlinarith only [hl',hlog]).trans hratio

theorem prefix_balanced_noise_single (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if RelativeNoiseExit (fun φ : RootedInjection T ψ => imageEdges T φ.val)
        (balancedLoad H T n) (earlyTemplateScale (k-T.roots.card) T.edges.card n) 2
        (codegreeNoiseRadius n) (prefixTime n) ω then 1 else 0) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
  filter_upwards [earlyTemplateScale_uniform_regular H,balanced_jump_budget H,
    rooted_initial_ratio_le_two H,balanced_noise_exponent_budget H,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (1 : ℕ)] with n hreg hjump hinit hexp hp hn
  intro k hk T ψ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hln : 0 ≤ 1+Real.log (n : ℝ) := by have := Real.log_nonneg hn1; linarith
  have hb : T.edges.card ≤ H^2 := (rootedTemplate_edges_card_le_sq T).trans (Nat.pow_le_pow_left hk 2)
  have hbR : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by exact_mod_cast hb
  have hr := hreg (k-T.roots.card) ((Nat.sub_le _ _).trans hk) T.edges.card hb
  let s := earlyTemplateScale (k-T.roots.card) T.edges.card n
  have hD : 0 < prefixD n := by unfold prefixD; have hh : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hp; positivity
  have hc : 0 < balancedJump n := Real.rpow_pos_of_pos hn0 _
  have hnoise : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hL : ∀ i < prefixTime n, 0 ≤ balancedLoad H T n i := by
    intro i hi
    have hpi := early_density_positive (by omega) hp hi.le
    unfold balancedLoad rootedScaling
    positivity
  have hJ : ∀ i < prefixTime n, 3*balancedLoad H T n i/s (i+1) ≤ balancedJump n := by
    intro i hi
    have hsi := hr.1 (i+1) (by omega)
    have hpi := early_density_positive (by omega) hp hi.le
    have hDi : prefixD n ≤ (n : ℝ)*earlyDensity n i^2 := by
      simpa only [earlyTemplateScale,pow_one] using earlyCodegreeScale_ge_prefixD n i hi.le (le_trans (by positivity) hp)
    have hratio := hr.2.2.1 i hi
    have hcoeff : 0 ≤ 12*(T.edges.card : ℝ)*(1+Real.log (n : ℝ))^(3*H+2)/((n : ℝ)*earlyDensity n i^2) := by positivity
    have hm := mul_le_mul_of_nonneg_left hratio hcoeff
    have hstep : 3*balancedLoad H T n i/s (i+1) ≤
        24*(T.edges.card : ℝ)*(1+Real.log (n : ℝ))^(3*H+2)/((n : ℝ)*earlyDensity n i^2) := by
      apply (div_le_iff₀ hsi).mpr
      dsimp only [balancedLoad,rootedScaling,s,earlyTemplateScale] at hm ⊢
      convert hm using 1 <;> ring
    apply hstep.trans (_root_.le_trans _ hjump)
    apply div_le_div₀ (by positivity) _ hD hDi
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbR (by norm_num)) (by positivity)
  have ht := triangle_relative_template_self_bounded_tail
    (fun φ : RootedInjection T ψ => imageEdges T φ.val) (completeGraph n) (prefixTime n)
    (balancedLoad H T n) s (balancedJump n) 2 hc (by norm_num) hr.1 hr.2.1 hL hJ
    (codegreeNoiseRadius n) hnoise
  refine (show _ ≤ 2*(prefixTime n+1 : ℝ)*Real.exp
    (-codegreeNoiseRadius n^2/(4*(balancedJump n*(copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (completeGraph n)/s 0+2*relativeScaleBudget s (prefixTime n)+codegreeNoiseRadius n+balancedJump n)+
      balancedJump n*codegreeNoiseRadius n))) from ?_).trans ?_
  · convert ht using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (pmfMean _)
    funext ω
    unfold RelativeNoiseExit
    split_ifs <;> rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div]
  apply neg_le_neg
  apply hexp.trans
  apply div_le_div_of_nonneg_left (sq_nonneg _)
  · have hscale : 0 ≤ copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) (completeGraph n)/s 0 :=
      div_nonneg (copyCount_nonneg _ _) (hr.1 0 (Nat.zero_le _)).le
    have hbudget := relativeScaleBudget_nonneg s (prefixTime n) hr.1 hr.2.1
    positivity
  · have hi := hinit k hk T ψ
    change copyCount _ (completeGraph n)/s 0 ≤ 2 at hi
    have hbgt : relativeScaleBudget s (prefixTime n) ≤ 2*(H : ℝ)^2*Real.log n :=
      hr.2.2.2.trans (by nlinarith only [mul_le_mul_of_nonneg_right hbR (Real.log_nonneg hn1)])
    have hh := mul_le_mul_of_nonneg_left (show copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) (completeGraph n)/s 0+
        2*relativeScaleBudget s (prefixTime n)+codegreeNoiseRadius n+balancedJump n ≤
        2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n by linarith only [hi,hbgt]) hc.le
    linarith only [hh]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_OverlapVertices
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical

namespace SharpTerminalLeave

lemma overlapVertices_contains_roots {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (W : Finset (Fin n))
    (hW : ∀ v, ψ v ∈ W) (φ : RootedInjection T ψ) :
    T.roots ⊆ overlapVertices W φ.val := by
  intro v hv
  rw [mem_overlapVertices,φ.property ⟨v,hv⟩]
  exact hW ⟨v,hv⟩

theorem rooted_overlap_fiber_card {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (W : Finset (Fin n)) (J : Finset (Fin k)) :
    Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} ≤
      W.card^J.card * n^(k-J.card) := by
  let encode : {φ : RootedInjection T ψ // overlapVertices W φ.val = J} →
      (J → W) × ({v : Fin k // v ∉ J} → Fin n) := fun φ =>
        (fun v => ⟨φ.val.val v, by
          have hv : v.val ∈ overlapVertices W φ.val.val := by rw [φ.property]; exact v.property
          exact (mem_overlapVertices W φ.val.val v).mp hv⟩,
         fun v => φ.val.val v)
  have hinj : Function.Injective encode := by
    intro φ χ he
    apply Subtype.ext
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    by_cases hv : v ∈ J
    · exact congrArg Subtype.val (congrFun (congrArg Prod.fst he) ⟨v,hv⟩)
    · exact congrFun (congrArg Prod.snd he) ⟨v,hv⟩
  have hc := Fintype.card_le_of_injective encode hinj
  have hfree : Fintype.card {v : Fin k // v ∉ J} = k-J.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      Fintype.card_subtype_compl (fun v : Fin k => v ∈ J)
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_coe,Fintype.card_fin,hfree] using hc

lemma imageEdges_inter_subset_induced {k n : ℕ} (T : RootedTemplate k)
    (φ : Fin k ↪ Fin n) (W : Finset (Fin n)) (F : Graph n)
    (hF : ∀ e ∈ F, e ⊆ W) :
    F ∩ imageEdges T φ ⊆
      (T.edges.filter (fun e => e ⊆ overlapVertices W φ)).image (fun e => e.map φ) := by
  intro e he
  obtain ⟨heF,heT⟩ := Finset.mem_inter.mp he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp heT
  apply Finset.mem_image.mpr
  refine ⟨f,Finset.mem_filter.mpr ⟨hf,?_⟩,rfl⟩
  intro v hv
  rw [mem_overlapVertices]
  exact hF (f.map φ) heF (Finset.mem_map.mpr ⟨v,hv,rfl⟩)

theorem rooted_new_edges_lower {k n : ℕ} (T : RootedTemplate k)
    (φ : Fin k ↪ Fin n) (W : Finset (Fin n)) (F : Graph n)
    (hF : ∀ e ∈ F, e ⊆ W) :
    T.edges.card-(T.edges.filter (fun e => e ⊆ overlapVertices W φ)).card ≤
      (imageEdges T φ \ F).card := by
  have hc := Finset.card_le_card (imageEdges_inter_subset_induced T φ W F hF)
  have hm : ((T.edges.filter (fun e => e ⊆ overlapVertices W φ)).image (fun e => e.map φ)).card =
      (T.edges.filter (fun e => e ⊆ overlapVertices W φ)).card := by
    apply Finset.card_image_of_injective
    exact fun _ _ h => Finset.map_injective φ h
  rw [hm] at hc
  rw [Finset.card_sdiff,imageEdges_card]
  omega

theorem rooted_weighted_extension_bound {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (W : Finset (Fin n)) (F : Graph n)
    (hW : ∀ v, ψ v ∈ W) (hF : ∀ e ∈ F, e ⊆ W)
    {p M : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 ≤ M)
    (hscale : ∀ J : Finset (Fin k), T.roots ⊆ J →
      (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤ M) :
    (∑ φ : RootedInjection T ψ, p^(imageEdges T φ.val \ F).card) ≤
      (2*((W.card : ℝ)+1))^k*M := by
  let b : Finset (Fin k) → ℕ := fun J => T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card
  have hfirst : (∑ φ : RootedInjection T ψ, p^(imageEdges T φ.val \ F).card) ≤
      ∑ φ : RootedInjection T ψ, p^(b (overlapVertices W φ.val)) := by
    apply Finset.sum_le_sum
    intro φ _
    exact pow_le_pow_of_le_one hp hp1 (rooted_new_edges_lower T φ.val W F hF)
  have hgroup : (∑ φ : RootedInjection T ψ, p^(b (overlapVertices W φ.val))) =
      ∑ J : Finset (Fin k),
        (Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} : ℝ)*p^(b J) := by
    rw [← Fintype.sum_fiberwise (fun φ : RootedInjection T ψ => overlapVertices W φ.val)]
    apply Finset.sum_congr rfl
    intro J _
    calc
      _ = ∑ _φ : {φ : RootedInjection T ψ // overlapVertices W φ.val = J}, p^(b J) := by
        apply Finset.sum_congr rfl
        intro φ _
        rw [φ.property]
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hfiber (J : Finset (Fin k)) :
      (Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} : ℝ)*p^(b J) ≤
        ((W.card : ℝ)+1)^k*M := by
    by_cases hJ : T.roots ⊆ J
    · have hjk : J.card ≤ k := by simpa only [Fintype.card_fin] using J.card_le_univ
      have hc : (Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} : ℝ) ≤
          (W.card : ℝ)^J.card*(n : ℝ)^(k-J.card) := by
        exact_mod_cast rooted_overlap_fiber_card T ψ W J
      have hw : (W.card : ℝ)^J.card ≤ ((W.card : ℝ)+1)^k := by
        calc
          _ ≤ ((W.card : ℝ)+1)^J.card := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
          _ ≤ _ := pow_le_pow_right₀ (show (1 : ℝ) ≤ (W.card : ℝ)+1 by have hz : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _; linarith) hjk
      calc
        _ ≤ ((W.card : ℝ)^J.card*(n : ℝ)^(k-J.card))*p^(b J) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hp _)
        _ = (W.card : ℝ)^J.card*((n : ℝ)^(k-J.card)*p^(b J)) := by ring
        _ ≤ ((W.card : ℝ)+1)^k*M :=
          mul_le_mul hw (hscale J hJ) (by positivity) (by positivity)
    · have he : IsEmpty {φ : RootedInjection T ψ // overlapVertices W φ.val = J} := by
        refine ⟨fun φ => hJ ?_⟩
        rw [← φ.property]
        exact overlapVertices_contains_roots T ψ W hW φ.val
      have := he
      simp only [Fintype.card_of_isEmpty,Nat.cast_zero,zero_mul]
      positivity
  calc
    _ ≤ _ := hfirst
    _ = _ := hgroup
    _ ≤ ∑ _J : Finset (Fin k), ((W.card : ℝ)+1)^k*M := Finset.sum_le_sum (fun J _ => hfiber J)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,
      Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,nsmul_eq_mul]; rw [mul_pow]; ring

lemma copyUnionSum_const_mul {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (q : ℕ) (f : Graph n → ℝ) (c : ℝ) (F : Graph n) :
    copyUnionSum required q (fun J => c*f J) F = c*copyUnionSum required q f F := by
  induction q generalizing F with
  | zero => rfl
  | succ q ih => simp only [copyUnionSum,ih,Finset.mul_sum]

lemma copyUnionSum_mono_bounded {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (b N q : ℕ) (hsize : ∀ a, (required a).card ≤ b)
    (f g : Graph n → ℝ) (hfg : ∀ F, F.card ≤ N → f F ≤ g F)
    (F : Graph n) (hF : F.card+q*b ≤ N) :
    copyUnionSum required q f F ≤ copyUnionSum required q g F := by
  induction q generalizing F with
  | zero => exact hfg F (by simpa using hF)
  | succ q ih =>
    apply Finset.sum_le_sum
    intro a _
    apply ih
    have hc := Finset.card_union_le F (required a)
    have hs := hsize a
    have hm : (q+1)*b = q*b+b := by ring
    omega

lemma copyUnionSum_intact {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (q : ℕ) (G F : Graph n) :
    copyUnionSum required q (fun J => intact J G) F = intact F G*(copyCount required G)^q := by
  induction q generalizing F with
  | zero => simp [copyUnionSum]
  | succ q ih =>
    simp only [copyUnionSum,ih,intact_union]
    rw [← Finset.sum_mul,← Finset.mul_sum]
    change (intact F G*copyCount required G)*(copyCount required G)^q = _
    rw [pow_succ']
    ring

lemma copyUnionSum_mean {n : ℕ} {α Ω : Type*} [Fintype α] [Fintype Ω]
    (required : α → Graph n) (q : ℕ) (μ : PMF Ω) (f : Graph n → Ω → ℝ) (F : Graph n) :
    copyUnionSum required q (fun J => pmfMean μ (f J)) F =
      pmfMean μ (fun ω => copyUnionSum required q (fun J => f J ω) F) := by
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    simp only [copyUnionSum,ih]
    exact (pmfMean_sum μ _).symm

lemma rooted_image_vertices {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n)
    {e : Finset (Fin n)} (he : e ∈ imageEdges T φ) : e ⊆ Finset.univ.map φ := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  exact Finset.map_subset_map.mpr (Finset.subset_univ f)

theorem rooted_union_moment_partition {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) {p M : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 ≤ M)
    (hscale : ∀ J : Finset (Fin k), T.roots ⊆ J →
      (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤ M)
    (N q : ℕ) (W : Finset (Fin n)) (F : Graph n)
    (hW : ∀ v, ψ v ∈ W) (hF : ∀ e ∈ F, e ⊆ W) (hcap : W.card+q*k ≤ N) :
    copyUnionSum (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      q (fun J => p^J.card) F ≤
      ((2*((N : ℝ)+1))^k*M)^q*p^F.card := by
  let B : ℝ := (2*((N : ℝ)+1))^k*M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change _ ≤ B^q*p^F.card
  induction q generalizing W F with
  | zero => simp [copyUnionSum]
  | succ q ih =>
    have hWcap : W.card ≤ N := by omega
    have hWreal : (W.card : ℝ) ≤ N := by exact_mod_cast hWcap
    have hb : (2*((W.card : ℝ)+1))^k*M ≤ B := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hext := (rooted_weighted_extension_bound T ψ W F hW hF hp hp1 hM hscale).trans hb
    calc
      _ ≤ ∑ φ : RootedInjection T ψ, B^q*p^(F ∪ imageEdges T φ.val).card := by
        apply Finset.sum_le_sum
        intro φ _
        apply ih (W := W ∪ Finset.univ.map φ.val)
        · intro v
          exact Finset.mem_union_left _ (hW v)
        · intro e he
          rcases Finset.mem_union.mp he with he | he
          · exact (hF e he).trans Finset.subset_union_left
          · exact (rooted_image_vertices T φ.val he).trans Finset.subset_union_right
        · have hc := Finset.card_union_le W (Finset.univ.map φ.val)
          have hm : (Finset.univ.map φ.val).card = k := by simp
          have hq : (q+1)*k = q*k+k := by ring
          omega
      _ = B^q*p^F.card*(∑ φ : RootedInjection T ψ, p^(imageEdges T φ.val \ F).card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro φ _
        have hc : (F ∪ imageEdges T φ.val).card = F.card+(imageEdges T φ.val \ F).card := by
          have hu := Finset.card_union_add_card_inter F (imageEdges T φ.val)
          have hs := Finset.card_sdiff (s := F) (t := imageEdges T φ.val)
          have hl := Finset.card_le_card (Finset.inter_subset_right : F ∩ imageEdges T φ.val ⊆ imageEdges T φ.val)
          omega
        rw [hc,pow_add]
        ring
      _ ≤ B^q*p^F.card*B := mul_le_mul_of_nonneg_left hext (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem rooted_count_moment_from_survival {k n : ℕ} {Ω : Type*} [Fintype Ω]
    (T : RootedTemplate k) (ψ : {v // v ∈ T.roots} ↪ Fin n)
    (μ : PMF Ω) (state : Ω → Graph n) (A : Ω → Prop)
    (q : ℕ) {p M U : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hscale : ∀ J : Finset (Fin k), T.roots ⊆ J →
      (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤ M)
    (hsurvive : ∀ F : Graph n, F.card ≤ q*T.edges.card →
      pmfMean μ (fun ω => if A ω then intact F (state ω) else 0) ≤ U*p^F.card) :
    pmfMean μ (fun ω => if A ω then (rootedCount T ψ (state ω))^q else 0) ≤
      U*((2*((((q+1)*k : ℕ) : ℝ)+1))^k*M)^q := by
  let req : RootedInjection T ψ → Graph n := fun φ => imageEdges T φ.val
  let f : Graph n → ℝ := fun F => pmfMean μ (fun ω => if A ω then intact F (state ω) else 0)
  have he : copyUnionSum req q f ∅ =
      pmfMean μ (fun ω => if A ω then (rootedCount T ψ (state ω))^q else 0) := by
    rw [copyUnionSum_mean req q μ]
    apply pmfMean_congr
    intro ω _
    by_cases hA : A ω
    · simp only [hA,ite_true]
      rw [copyUnionSum_intact]
      simp only [intact,Finset.empty_subset,ite_true,one_mul]
      rfl
    · simp only [hA,ite_false]
      have hz := copyUnionSum_const_mul req q (fun _ => (1 : ℝ)) 0 ∅
      simpa only [zero_mul] using hz
  let W : Finset (Fin n) := Finset.univ.map ψ
  have hw : ∀ v, ψ v ∈ W := fun v => Finset.mem_map.mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hWcard : W.card ≤ k := by
    have he : W.card = T.roots.card := by simp [W]
    rw [he]
    simpa only [Fintype.card_fin] using T.roots.card_le_univ
  have hb := rooted_union_moment_partition T ψ hp hp1 hM hscale ((q+1)*k) q W ∅ hw
    (by simp) (by nlinarith)
  simp only [Finset.card_empty,pow_zero,mul_one] at hb
  calc
    _ = copyUnionSum req q f ∅ := he.symm
    _ ≤ copyUnionSum req q (fun F => U*p^F.card) ∅ :=
      copyUnionSum_mono_bounded req T.edges.card (q*T.edges.card) q
        (fun φ => by simp only [req,imageEdges_card,le_refl]) f _ hsurvive ∅ (by simp)
    _ = U*copyUnionSum req q (fun F => p^F.card) ∅ := copyUnionSum_const_mul req q _ U ∅
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hU

theorem pmfMean_stopped_power_tail {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (A : Ω → Prop) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (q : ℕ) {t B : ℝ} (ht : 0 < t)
    (hmean : pmfMean μ (fun ω => if A ω then X ω^q else 0) ≤ B) :
    pmfMean μ (fun ω => if A ω ∧ t ≤ X ω then 1 else 0) ≤ B/t^q := by
  apply (le_div_iff₀ (pow_pos ht q)).mpr
  rw [← pmfMean_mul_const]
  apply le_trans _ hmean
  apply pmfMean_mono
  intro ω _
  by_cases hA : A ω
  · by_cases htX : t ≤ X ω
    · simp only [hA,htX,and_self,ite_true,one_mul]
      exact pow_le_pow_left₀ ht.le htX q
    · simp only [hA,htX,and_false,ite_false,ite_true,zero_mul]
      exact pow_nonneg (hX ω) q
  · simp [hA]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedTemplateEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma rootInjection_card_le {k n : ℕ} (T : RootedTemplate k) :
    Fintype.card ({v // v ∈ T.roots} ↪ Fin n) ≤ n^T.roots.card := by
  have hh := Fintype.card_le_of_injective
    (fun f : {v // v ∈ T.roots} ↪ Fin n => (f : {v // v ∈ T.roots} → Fin n))
    (fun _ _ h => DFunLike.coe_injective h)
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using hh

theorem rootedCountIndex_card_le (H n : ℕ) :
    Fintype.card (RootedCountIndex H n) ≤ rootedFamilySize H * (n+1)^H := by
  classical
  unfold RootedCountIndex
  simp only [Fintype.card_sigma]
  calc
    _ ≤ ∑ k : Fin (H+1), ∑ T : RootedTemplate k.val, (n+1)^H := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro T _
      apply (rootInjection_card_le T).trans
      have hr : T.roots.card ≤ k.val := by
        simpa using (Finset.card_le_univ T.roots)
      calc
        n^T.roots.card ≤ (n+1)^T.roots.card := Nat.pow_le_pow_left (Nat.le_succ n) _
        _ ≤ (n+1)^H := Nat.pow_le_pow_right (by omega) (by omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      rfl

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixTimeSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma prefixTime_le_square (n : ℕ) : prefixTime n ≤ n^2 := by
  have hf : prefixTargetTime n ≤ (n : ℝ)^2 := by
    unfold prefixTargetTime
    have h₁ : 0 ≤ 1/(n : ℝ) := by positivity
    have h₂ : 0 ≤ prefixTargetDensity n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h₃ := sq_nonneg (n : ℝ)
    nlinarith
  calc
    prefixTime n ≤ ⌊(n : ℝ)^2⌋₊ := Nat.floor_le_floor hf
    _ = n^2 := by simp only [← Nat.cast_pow,Nat.floor_natCast]

theorem rooted_noise_chances_le (H n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (RootedCountIndex H n)*2*(prefixTime n+1) ≤
      rootedFamilySize H * 2^(H+2)*n^(H+2) := by
  have hpow : (n+1)^H ≤ (2*n)^H := Nat.pow_le_pow_left (by omega) H
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  have ht : prefixTime n+1 ≤ 2*n^2 := by
    have hh := prefixTime_le_square n
    omega
  calc
    _ ≤ (rootedFamilySize H*(n+1)^H)*2*(2*n^2) := by
      gcongr
      exact rootedCountIndex_card_le H n
    _ ≤ (rootedFamilySize H*(2*n)^H)*2*(2*n^2) := by gcongr
    _ = _ := by rw [mul_pow,pow_add,pow_add]; ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedCompletionMax
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma rootedCompletionMax_ge_one {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) :
    1 ≤ rootedCompletionMax T n p := by
  unfold rootedCompletionMax
  apply Finset.le_sup'_of_le _ (Finset.mem_univ (Finset.univ : Finset (Fin k)))
  simp

lemma rootedCompletionMax_bound {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) :
    (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (· ⊆ J)).card) ≤
      rootedCompletionMax T n p := by
  unfold rootedCompletionMax
  apply Finset.le_sup'_of_le _ (Finset.mem_univ J)
  simp only [hJ,ite_true,le_refl]

theorem rooted_tail_from_survival {k n : ℕ} {Ω : Type*} [Fintype Ω]
    (T : RootedTemplate k) (ψ : {v // v ∈ T.roots} ↪ Fin n)
    (μ : PMF Ω) (state : Ω → Graph n) (A : Ω → Prop)
    (q : ℕ) {p B U : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 < B) (hU : 0 ≤ U)
    (hcoef : 2*(2*((((q+1)*k : ℕ) : ℝ)+1))^k ≤ B)
    (hsurvive : ∀ F : Graph n, F.card ≤ q*T.edges.card →
      pmfMean μ (fun ω => if A ω then intact F (state ω) else 0) ≤ U*p^F.card) :
    pmfMean μ (fun ω => if A ω ∧ B*rootedCompletionMax T n p ≤ rootedCount T ψ (state ω)
      then 1 else 0) ≤ U*(1/2 : ℝ)^q := by
  let M := rootedCompletionMax T n p
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (rootedCompletionMax_ge_one T n p)
  have hm := rooted_count_moment_from_survival T ψ μ state A q hp hp1 hM.le hU
    (rootedCompletionMax_bound T n p) hsurvive
  have ht := pmfMean_stopped_power_tail μ A (fun ω => rootedCount T ψ (state ω))
    (fun ω => copyCount_nonneg _ _) q (mul_pos hB hM) hm
  apply ht.trans
  have he : U*((2*((((q+1)*k : ℕ) : ℝ)+1))^k*M)^q/(B*M)^q =
      U*((2*((((q+1)*k : ℕ) : ℝ)+1))^k/B)^q := by
    rw [mul_div_assoc,← div_pow,mul_div_mul_right _ _ hM.ne']
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hU
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ hB).mpr
  linarith only [hcoef]

lemma rooted_moment_edge_cap (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ k ≤ H, ∀ T : RootedTemplate k, ((rootedMomentOrder n*T.edges.card : ℕ) : ℝ) ≤
      (n : ℝ)^(1/200000 : ℝ) := by
  have hc : (0 : ℝ) < 1/((H : ℝ)^2+1) := by positivity
  filter_upwards [prefixTemplateFactor_subpower 2 (by norm_num : (0 : ℝ) < 1/200000) hc,
    eventually_ge_atTop (1 : ℕ)] with n hb hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ 1+Real.log (n : ℝ) := by have := Real.log_nonneg hn1; linarith
  have hq : (rootedMomentOrder n : ℝ) ≤ (1+Real.log (n : ℝ))^2 := Nat.floor_le (sq_nonneg _)
  have hpow : (1+Real.log (n : ℝ))^(2 : ℝ) = (1+Real.log (n : ℝ))^2 := Real.rpow_two _
  change (1+Real.log (n : ℝ))^(2 : ℝ) ≤ _ at hb
  rw [hpow] at hb
  intro k hk T
  have he : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by
    exact_mod_cast (rootedTemplate_edges_card_le_sq T).trans (Nat.pow_le_pow_left hk 2)
  push_cast
  calc
    _ ≤ (1+Real.log (n : ℝ))^2*((H : ℝ)^2+1) :=
      mul_le_mul hq (by linarith only [he]) (Nat.cast_nonneg _) (sq_nonneg _)
    _ ≤ (1/((H : ℝ)^2+1)*(n : ℝ)^(1/200000 : ℝ))*((H : ℝ)^2+1) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by field_simp

lemma rooted_moment_coefficient (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    0 < (1+Real.log (n : ℝ))^(3*H+2) ∧
    ∀ k ≤ H, 2*(2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1))^k ≤
      (1+Real.log (n : ℝ))^(3*H+2) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually_ge_atTop (2*(2*(H : ℝ)+1))] with n hn
  change 2*(2*(H : ℝ)+1) ≤ Real.log (n : ℝ) at hn
  let L : ℝ := 1+Real.log (n : ℝ)
  have hL : 2 ≤ L := by dsimp [L]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hq : (rootedMomentOrder n : ℝ) ≤ L^2 := Nat.floor_le (sq_nonneg _)
  refine ⟨pow_pos hL0 _,?_⟩
  intro k hk
  have hkR : (k : ℝ) ≤ H := by exact_mod_cast hk
  have hcoeff : 2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1) ≤ L^3 := by
    push_cast
    have hq' : (rootedMomentOrder n : ℝ)+1 ≤ 2*L^2 := by nlinarith [sq_nonneg (L-1)]
    have hmul := mul_le_mul hq' hkR (Nat.cast_nonneg k) (by positivity : (0 : ℝ) ≤ 2*L^2)
    have hc : 2*(2*(H : ℝ)+1) ≤ L := by dsimp [L]; linarith
    have hhc := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
    nlinarith only [hmul,hhc,sq_nonneg (L-1),hL]
  have hcoeff0 : 0 ≤ 2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1) := by positivity
  have hpow : (2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1))^k ≤ L^(3*H) := by
    calc
      _ ≤ (L^3)^k := pow_le_pow_left₀ hcoeff0 hcoeff k
      _ = L^(3*k) := (pow_mul L 3 k).symm
      _ ≤ _ := pow_le_pow_right₀ hL1 (by omega)
  change 2*_ ≤ L^(3*H+2)
  rw [pow_add]
  have htail : 2 ≤ L^2 := by nlinarith
  exact mul_le_mul htail hpow (by positivity) (by positivity) |>.trans_eq (mul_comm _ _)

lemma historyAlive_past {α : Type*} (safe : ℕ → α → Prop) (T j : ℕ)
    (ω π : History α T) (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyAlive safe T j ω ↔ historyAlive safe T j π := by
  have he (i : ℕ) (hi : i < j) : ω (historyIndex T i) = π (historyIndex T i) := by
    apply h
    exact min_le_min_right T hi.le
  unfold historyAlive
  constructor
  · intro hA i hi; rw [← he i hi]; exact hA i hi
  · intro hA i hi; rw [he i hi]; exact hA i hi

lemma stopped_state_mean_past {α : Type*} [Fintype α] (initial : PMF α)
    (K : ℕ → α → PMF α) (safe : ℕ → α → Prop) (T j : ℕ) (hj : j ≤ T)
    (P : α → Prop) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if historyAlive safe T j ω ∧ P (ω (historyIndex T j)) then 1 else 0) =
    pmfMean (historyLaw initial K T j)
      (fun ω => if historyAlive safe T j ω ∧ P (ω (historyIndex T j)) then 1 else 0) := by
  apply historyLaw_past_mean initial K T j T hj
  intro ω π h
  have he := h (historyIndex T j) (le_refl _)
  rw [he,historyAlive_past safe T j ω π h]

theorem prefix_rooted_killed_tail (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ j ≤ prefixTime n, ∀ k ≤ H, ∀ T : RootedTemplate k,
      ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
        (prefixTime n) j ω ∧
        (1+Real.log (n : ℝ))^(3*H+2)*rootedCompletionMax T n (earlyDensity n j) ≤
          rootedCount T ψ (ω (historyIndex (prefixTime n) j)) then 1 else 0) ≤
      Real.exp 1*(1/2 : ℝ)^(rootedMomentOrder n) := by
  filter_upwards [prefix_killed_survival,rooted_moment_edge_cap H,
    rooted_moment_coefficient H,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hsurv hcap hcoef hp hn
  intro j hj k hk T ψ
  rw [stopped_state_mean_past _ _ _ _ _ hj
    (fun G => (1+Real.log (n : ℝ))^(3*H+2)*rootedCompletionMax T n (earlyDensity n j) ≤
      rootedCount T ψ G)]
  apply rooted_tail_from_survival T ψ _ _ _ (rootedMomentOrder n)
    (early_density_positive (by omega) hp hj).le (earlyDensity_le_one n j)
    hcoef.1 (Real.exp_pos 1).le (hcoef.2 k hk)
  intro F hF
  apply hsurv j hj F
  exact (show (F.card : ℝ) ≤ ((rootedMomentOrder n*T.edges.card : ℕ) : ℝ) by exact_mod_cast hF).trans
    (hcap k hk T)

lemma rooted_moment_tail_logsquare : ∀ᶠ n : ℕ in atTop,
    Real.exp 1*(1/2 : ℝ)^(rootedMomentOrder n) ≤ Real.exp (-(Real.log (n : ℝ))^2/4) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 3] with n hn
  have hq : (1+Real.log (n : ℝ))^2 < (rootedMomentOrder n : ℝ)+1 := Nat.lt_floor_add_one _
  have hlog2 : (1 : ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have he : (1/2 : ℝ)^(rootedMomentOrder n) =
      Real.exp (-(rootedMomentOrder n : ℝ)*Real.log 2) := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [inv_pow,one_div]
  rw [he,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (rootedMomentOrder n))
  nlinarith only [hh,hq,hn,sq_nonneg (Real.log (n : ℝ))]

theorem polynomial_logsquare_le_prefix_margin (A K : ℝ) : ∀ᶠ n : ℕ in atTop,
    A*(n : ℝ)^K*Real.exp (-(Real.log (n : ℝ))^2/4) ≤
      Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp hlog
  filter_upwards [hlog.eventually_ge_atTop (8*(K+1)),hlog.eventually_ge_atTop 1,
    hpow.eventually_ge_atTop 16,tendsto_natCast_atTop_atTop.eventually_ge_atTop A,
    eventually_ge_atTop (1 : ℕ)] with n hlinear hl hpow hA hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl0 : 0 < Real.log (n : ℝ) := by linarith
  have hlin := mul_le_mul_of_nonneg_right hlinear hl0.le
  have hpow' : 16*(Real.log (n : ℝ))^(4/3 : ℝ) ≤ (Real.log (n : ℝ))^2 := by
    have hm := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hl0.le (4/3 : ℝ))
    have he : (Real.log (n : ℝ))^(2/3 : ℝ)*(Real.log (n : ℝ))^(4/3 : ℝ) =
        (Real.log (n : ℝ))^2 := by
      rw [← Real.rpow_add hl0]; norm_num [Real.rpow_two]
    exact hm.trans_eq he
  calc
    _ ≤ (n : ℝ)*(n : ℝ)^K*Real.exp (-(Real.log (n : ℝ))^2/4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hn0.le _))
        (Real.exp_pos _).le
    _ = Real.exp ((K+1)*Real.log n-(Real.log (n : ℝ))^2/4) := by
      rw [show (n : ℝ)*(n : ℝ)^K = (n : ℝ)^(K+1) by
        rw [Real.rpow_add hn0,Real.rpow_one]; ring]
      rw [Real.rpow_def_of_pos hn0,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hlin,hpow'])

theorem prefix_rooted_upper_failure (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n))
      (fun ω => if PrefixRootedUpper H n ω then 0 else 1) ≤
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_rooted_killed_tail H,rooted_moment_tail_logsquare,
    polynomial_logsquare_le_prefix_margin
      ((rootedFamilySize H : ℝ)*2^(H+2)) (H+2),
    eventually_ge_atTop (1 : ℕ)] with n htail hnum hbudget hn
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  let P (i : Fin (prefixTime n+1) × RootedCountIndex H n)
      (ω : History (Graph n) (prefixTime n)) :=
    historyAlive (fun j => densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n))
      (prefixTime n) i.1.val ω ∧
    (1+Real.log (n : ℝ))^(3*H+2)*
      rootedCompletionMax i.2.2.1 n (earlyDensity n i.1.val) ≤
        rootedCount i.2.2.1 i.2.2.2 (ω (historyIndex (prefixTime n) i.1.val))
  have he (ω : History (Graph n) (prefixTime n)) :
      ¬ PrefixRootedUpper H n ω ↔ ∃ i ∈ Finset.univ, P i ω := by
    simp only [PrefixRootedUpper,not_forall,not_lt]
    constructor
    · rintro ⟨j,hj,ha,k,hk,T,ψ,hbad⟩
      exact ⟨(⟨j,by omega⟩,⟨⟨k,by omega⟩,T,ψ⟩),Finset.mem_univ _,ha,hbad⟩
    · rintro ⟨i,_,ha,hbad⟩
      exact ⟨i.1.val,by omega,ha,i.2.1.val,by omega,i.2.2.1,i.2.2.2,hbad⟩
  have hu := pmfMean_event_union μ Finset.univ P
  have hs : (∑ i, pmfMean μ (fun ω => if P i ω then 1 else 0)) ≤
      (Fintype.card (Fin (prefixTime n+1) × RootedCountIndex H n) : ℝ)*
        Real.exp (-(Real.log (n : ℝ))^2/4) := by
    calc
      _ ≤ ∑ _i : Fin (prefixTime n+1) × RootedCountIndex H n,
          Real.exp (-(Real.log (n : ℝ))^2/4) := by
        apply Finset.sum_le_sum
        intro i _
        exact (htail i.1.val (by omega) i.2.1.val (by omega) i.2.2.1 i.2.2.2).trans hnum
      _ = _ := by simp
  have hc : (Fintype.card (Fin (prefixTime n+1) × RootedCountIndex H n) : ℝ) ≤
      (rootedFamilySize H : ℝ)*2^(H+2)*(n : ℝ)^(H+2 : ℕ) := by
    have hh := rooted_noise_chances_le H n hn
    have hh' : Fintype.card (Fin (prefixTime n+1) × RootedCountIndex H n) ≤
        rootedFamilySize H*2^(H+2)*n^(H+2) := by
      simp only [Fintype.card_prod,Fintype.card_fin]
      nlinarith only [hh]
    exact_mod_cast hh'
  have hev : (n : ℝ)^((H : ℝ)+2) = (n : ℝ)^(H+2 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_cast
  rw [hev] at hbudget
  have hsumfinal := hs.trans ((mul_le_mul_of_nonneg_right hc
    (Real.exp_pos _).le).trans hbudget)
  have hfinal := hu.trans (by
    convert hsumfinal using 1; try rfl
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (pmfMean μ)
    funext ω
    by_cases h : P i ω <;> simp only [h,ite_true,ite_false])
  convert hfinal using 1; try rfl
  apply congrArg (pmfMean μ)
  funext ω
  simp only [← he]
  split_ifs <;> rfl

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleNoiseJumpBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma triangle_noise_jump_budget : ∀ᶠ n : ℕ in atTop,
    ∀ i < prefixTime n, 3*triangleNoiseLoad n i/earlyTriangleScale n (i+1) ≤ balancedJump n := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ)^(1999/2000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1999/2000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [earlyTriangleScale_regular,prefixDensity_eventually_inverse_lower,
    hg.eventually_ge_atTop 72,eventually_ge_atTop (1 : ℕ)] with n hr hp hg hn
  intro i hi
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp0 := early_density_positive (by omega) hp hi.le
  have hmin : 1/(n : ℝ) ≤ earlyDensity n i := hp.trans (earlyDensity_antitone n hi.le)
  have hratio := hr.2.2.1 i hi
  have hS := hr.1 i hi.le
  have hS' := hr.1 (i+1) (by omega)
  have hD : 0 ≤ earlyTemplateScale 1 2 n i := by unfold earlyTemplateScale; positivity
  have h₁ : 3*triangleNoiseLoad n i/earlyTriangleScale n (i+1) ≤
      12*earlyTemplateScale 1 2 n i/earlyTriangleScale n i := by
    apply (div_le_div_iff₀ hS' hS).mpr
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 6*earlyTemplateScale 1 2 n i by positivity)
    dsimp only [triangleNoiseLoad]
    nlinarith only [hh]
  have he : 12*earlyTemplateScale 1 2 n i/earlyTriangleScale n i =
      72/(n : ℝ)^2/earlyDensity n i := by
    unfold earlyTemplateScale earlyTriangleScale earlyTemplateScale
    field_simp
    ring
  rw [he] at h₁
  have h₂ : 72/(n : ℝ)^2/earlyDensity n i ≤ 72/(n : ℝ) := by
    apply (div_le_iff₀ hp0).mpr
    have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 72/(n : ℝ) by positivity)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have h₃ : 72/(n : ℝ) ≤ balancedJump n := by
    have hh := div_le_div_of_nonneg_right hg hn0.le
    apply hh.trans_eq
    unfold balancedJump
    calc
      (n : ℝ)^(1999/2000 : ℝ)/(n : ℝ) = (n : ℝ)^(1999/2000 : ℝ)/(n : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ)^(-1/2000 : ℝ) := by rw [← Real.rpow_sub hn0]; norm_num
  exact h₁.trans (h₂.trans h₃)

theorem prefix_triangle_noise_single : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixTriangleNoise n ω then 0 else 1) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
  filter_upwards [earlyTriangleScale_regular,triangle_noise_jump_budget,
    balanced_noise_exponent_budget 3,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (2 : ℕ)] with n hr hj hexp hp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hc : 0 < balancedJump n := Real.rpow_pos_of_pos hn0 _
  have hnoise : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hL : ∀ i < prefixTime n, 0 ≤ triangleNoiseLoad n i := by
    intro i hi
    unfold triangleNoiseLoad earlyTemplateScale
    positivity
  have ht := triangle_relative_template_self_bounded_tail (triangleRequired (n := n))
    (completeGraph n) (prefixTime n) (triangleNoiseLoad n) (earlyTriangleScale n)
    (balancedJump n) 2 hc (by norm_num) hr.1 hr.2.1 hL hj (codegreeNoiseRadius n) hnoise
  have ht' : pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixTriangleNoise n ω then 0 else 1) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp
      (-codegreeNoiseRadius n^2/(4*(balancedJump n*(copyCount (triangleRequired (n := n))
        (completeGraph n)/earlyTriangleScale n 0+2*relativeScaleBudget (earlyTriangleScale n) (prefixTime n)+
          codegreeNoiseRadius n+balancedJump n)+balancedJump n*codegreeNoiseRadius n))) := by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (pmfMean _)
    funext ω
    unfold PrefixTriangleNoise RelativeNoiseExit
    split_ifs <;> simp_all
  apply ht'.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div]
  apply neg_le_neg
  apply hexp.trans
  apply div_le_div_of_nonneg_left (sq_nonneg _)
  · have hscale : 0 ≤ copyCount (triangleRequired (n := n)) (completeGraph n)/earlyTriangleScale n 0 :=
      div_nonneg (copyCount_nonneg _ _) (hr.1 0 (Nat.zero_le _)).le
    have hbudget := relativeScaleBudget_nonneg (earlyTriangleScale n) (prefixTime n) hr.1 hr.2.1
    positivity
  · have hi := initial_triangle_ratio_le_two hn
    have hbgt := hr.2.2.2
    have hh := mul_le_mul_of_nonneg_left (show copyCount (triangleRequired (n := n)) (completeGraph n)/earlyTriangleScale n 0+
        2*relativeScaleBudget (earlyTriangleScale n) (prefixTime n)+codegreeNoiseRadius n+balancedJump n ≤
        2+4*(3 : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n by
          nlinarith only [hi,hbgt,Real.log_nonneg hn1]) hc.le
    norm_num only [Nat.cast_ofNat] at hexp ⊢
    linarith only [hh]

theorem prefix_triangle_noise_failure : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixTriangleNoise n ω then 0 else 1) ≤
      Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_triangle_noise_single,polynomial_logsquare_le_prefix_margin 4 2,
    eventually_ge_atTop (1 : ℕ)] with n ht hb hn
  apply ht.trans
  have htime : 2*(prefixTime n+1 : ℝ) ≤ 4*(n : ℝ)^2 := by
    have ht : (prefixTime n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast prefixTime_le_square n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [ht,hn1]
  apply (mul_le_mul_of_nonneg_right htime (Real.exp_pos _).le).trans
  simpa only [Real.rpow_two] using hb

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixCodegreeNoiseGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

theorem prefix_codegree_noise_failure : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixCodegreeNoiseGood n ω then 0 else 1) ≤
      Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_codegree_relative_noise_bound,codegree_noise_exponent_lower,
    prefixTemplateFactor_subpower 2 (by norm_num : (0 : ℝ) < 1/2500) (by norm_num : (0 : ℝ) < 1),
    polynomial_logsquare_le_prefix_margin 4 4,eventually_ge_atTop (1 : ℕ)] with n ht hexp hlog hb hn
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hr : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hexp' : (Real.log (n : ℝ))^2/4 ≤ codegreeNoiseRadius n^2/codegreeNoiseDenominator n := by
    have hh : (1+Real.log (n : ℝ))^2 ≤ (n : ℝ)^(1/2500 : ℝ) := by
      simpa only [prefixTemplateFactor,Real.rpow_two,one_mul] using hlog
    have hln := Real.log_nonneg hn1
    nlinarith only [hh,hln,hexp,sq_nonneg (Real.log (n : ℝ))]
  have hsingle (uv : Fin n × Fin n) :
      pmfMean μ (fun ω => if PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
    have ht' : pmfMean μ (fun ω => if PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0) ≤
        2*(prefixTime n+1 : ℝ)*Real.exp (-(codegreeNoiseRadius n)^2/codegreeNoiseDenominator n) := by
      unfold codegreeNoiseDenominator
      refine le_trans ?_ (ht uv.1 uv.2 (codegreeNoiseRadius n) hr)
      apply le_of_eq
      congr 1
      funext ω
      by_cases hω : PrefixCodegreeNoiseExit uv.1 uv.2 ω <;>
        simp_all only [PrefixCodegreeNoiseExit, ite_true, ite_false]
    apply ht'.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    rw [neg_div,neg_div]
    exact neg_le_neg hexp'
  have hu := pmfMean_event_union μ Finset.univ (fun uv : Fin n × Fin n => PrefixCodegreeNoiseExit uv.1 uv.2)
  have hs : (∑ uv : Fin n × Fin n,
      pmfMean μ (fun ω => if PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0)) ≤
      4*(n : ℝ)^4*Real.exp (-(Real.log (n : ℝ))^2/4) := by
    calc
      _ ≤ ∑ _uv : Fin n × Fin n, 2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) :=
        Finset.sum_le_sum (fun uv _ => hsingle uv)
      _ = (n : ℝ)^2*(2*(prefixTime n+1))*Real.exp (-(Real.log (n : ℝ))^2/4) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have htime : (prefixTime n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast prefixTime_le_square n
        have hnt : 1 ≤ (n : ℝ)^2 := by nlinarith
        nlinarith only [mul_le_mul_of_nonneg_left htime (sq_nonneg (n : ℝ)),
          mul_le_mul_of_nonneg_left hnt (sq_nonneg (n : ℝ))]
  rw [show (n : ℝ)^(4 : ℝ) = (n : ℝ)^4 from Real.rpow_natCast _ 4] at hb
  have hf := hu.trans (hs.trans hb)
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (pmfMean μ)
  funext ω
  have he : (∃ uv ∈ (Finset.univ : Finset (Fin n × Fin n)), PrefixCodegreeNoiseExit uv.1 uv.2 ω) ↔
      ¬ PrefixCodegreeNoiseGood n ω := by simp [PrefixCodegreeNoiseGood,Prod.exists]
  simp only [he, ite_not]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixBalancedNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

theorem prefix_balanced_noise_failure (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n))
      (fun ω => if PrefixBalancedNoise H n ω then 0 else 1) ≤
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_balanced_noise_single H,
    polynomial_logsquare_le_prefix_margin ((rootedFamilySize H : ℝ)*2^(H+2)) (H+2),
    eventually_ge_atTop (1 : ℕ)] with n htail hb hn
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  let P (i : RootedCountIndex H n) (ω : History (Graph n) (prefixTime n)) :=
    RelativeNoiseExit (fun φ : RootedInjection i.2.1 i.2.2 => imageEdges i.2.1 φ.val)
      (balancedLoad H i.2.1 n) (earlyTemplateScale (i.1.val-i.2.1.roots.card) i.2.1.edges.card n)
      2 (codegreeNoiseRadius n) (prefixTime n) ω
  have he (ω : History (Graph n) (prefixTime n)) :
      ¬ PrefixBalancedNoise H n ω ↔ ∃ i ∈ Finset.univ, P i ω := by
    simp only [PrefixBalancedNoise,not_forall,not_not]
    constructor
    · rintro ⟨k,hk,T,ψ,h⟩
      exact ⟨⟨⟨k,by omega⟩,T,ψ⟩,Finset.mem_univ _,h⟩
    · rintro ⟨i,_,h⟩
      exact ⟨i.1.val,by omega,i.2.1,i.2.2,h⟩
  have hu := pmfMean_event_union μ Finset.univ P
  have hs : (∑ i, pmfMean μ (fun ω => if P i ω then 1 else 0)) ≤
      (Fintype.card (RootedCountIndex H n) : ℝ)*2*(prefixTime n+1)*
        Real.exp (-(Real.log (n : ℝ))^2/4) := by
    calc
      _ ≤ ∑ _i : RootedCountIndex H n,
          2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
        apply Finset.sum_le_sum
        intro i _
        exact htail i.1.val (by omega) i.2.1 i.2.2
      _ = _ := by simp; ring
  have hc : (Fintype.card (RootedCountIndex H n) : ℝ)*2*(prefixTime n+1) ≤
      (rootedFamilySize H : ℝ)*2^(H+2)*(n : ℝ)^(H+2 : ℕ) := by
    exact_mod_cast rooted_noise_chances_le H n hn
  have hev : (n : ℝ)^((H : ℝ)+2) = (n : ℝ)^(H+2 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_cast
  rw [hev] at hb
  have hs' := hs.trans ((mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans hb)
  have hf := hu.trans hs'
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  try rfl
  apply congrArg (pmfMean μ)
  funext ω
  simp only [← he]
  split_ifs <;> rfl

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_NormalizedTrackingAbsolute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Filter Classical

namespace SharpTerminalLeave

lemma four_prefix_margins : ∀ᶠ n : ℕ in atTop,
    4*Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) ≤
      Real.exp (-(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (Real.log (n : ℝ))^(4/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually (eventually_ge_atTop (Real.log 4))] with n hn
  have hh : (4 : ℝ) ≤ Real.exp ((Real.log (n : ℝ))^(4/3 : ℝ)) := by
    calc
      (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hn
  calc
    _ ≤ Real.exp ((Real.log (n : ℝ))^(4/3 : ℝ))*Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem uniform_prefix_obligation : UniformPrefixObligation := by
  refine ⟨1/80000,by norm_num,(3*(8001 : ℕ)+2 : ℕ),?_⟩
  filter_upwards [prefix_good_history,prefix_rooted_upper_failure 8001,
    prefix_balanced_noise_failure 8001,prefix_triangle_noise_failure,
    prefix_codegree_noise_failure,four_prefix_margins] with n hgood hr hb ht hc hmargin
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  have hm : μ.map (fun ω => ω (historyIndex (prefixTime n) (prefixTime n))) = prefixLaw n := by
    rw [historyLaw_marginal _ _ _ _ le_rfl,markovLaw_triangle_step]
    rfl
  unfold prefixFailure
  rw [← hm,pmfMean_map]
  have hpoint : ∀ ω ∈ μ.support,
      (if GoodPrefixGraph n (1/80000) (3*(8001 : ℕ)+2 : ℕ) (ω (historyIndex (prefixTime n) (prefixTime n))) then (0 : ℝ) else 1) ≤
      (if PrefixRootedUpper 8001 n ω then 0 else 1)+
      (if PrefixBalancedNoise 8001 n ω then 0 else 1)+
      (if PrefixTriangleNoise n ω then 0 else 1)+
      (if PrefixCodegreeNoiseGood n ω then 0 else 1) := by
    intro ω hω
    by_cases h₁ : PrefixRootedUpper 8001 n ω <;>
      by_cases h₂ : PrefixBalancedNoise 8001 n ω <;>
      by_cases h₃ : PrefixTriangleNoise n ω <;>
      by_cases h₄ : PrefixCodegreeNoiseGood n ω
    all_goals simp only [h₁,h₂,h₃,h₄,ite_true,ite_false]
    · rw [ite_eq_left (hgood ω hω h₁ h₂ h₃ h₄)]; norm_num
    all_goals split_ifs <;> norm_num
  have hs := pmfMean_mono μ hpoint
  simp only [pmfMean_add] at hs
  apply hs.trans
  have hs' := add_le_add (add_le_add (add_le_add hr hb) ht) hc
  calc
    _ ≤ ((Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ))+
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)))+
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)))+
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := hs'
    _ = 4*Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by ring
    _ ≤ _ := hmargin

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixFailureEnvelopeSuperpolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefix_failure_envelope_superpolynomial (K : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^K *
      Real.exp (- (Real.log n)^(4/3 : ℝ))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log (n : ℝ))^(1/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp hlog
  have hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ)^K *
      Real.exp (- (Real.log n)^(4/3 : ℝ)) ≤ (n : ℝ)^(-1 : ℝ) := by
    filter_upwards [hpow.eventually (eventually_ge_atTop (K+1)),
      eventually_ge_atTop (2 : ℕ)] with n hn hsize
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn1
    have hl0 : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    have he : (Real.log (n : ℝ))^(4/3 : ℝ) =
        Real.log n * (Real.log n)^(1/3 : ℝ) := by
      rw [show (4/3 : ℝ) = 1+1/3 by norm_num,Real.rpow_add hl0,Real.rpow_one]
    have hle : (K+1)*Real.log n ≤ (Real.log (n : ℝ))^(4/3 : ℝ) := by
      rw [he,mul_comm (K+1)]
      exact mul_le_mul_of_nonneg_left hn hl0.le
    calc
      (n : ℝ)^K * Real.exp (- (Real.log n)^(4/3 : ℝ)) ≤
          (n : ℝ)^K * (n : ℝ)^(-(K+1)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
        rw [Real.rpow_def_of_pos hn0]
        apply Real.exp_le_exp.mpr
        nlinarith only [hle]
      _ = (n : ℝ)^(-1 : ℝ) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
  exact squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) hbound
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
      tendsto_natCast_atTop_atTop)

theorem prefix_failure_l2_envelope_tendsto :
    Tendsto (fun n : ℕ => (2*(n : ℝ)+1)*
      Real.exp (- (Real.log n)^(4/3 : ℝ))) atTop (𝓝 0) := by
  have h1 := prefix_failure_envelope_superpolynomial 1
  have h0 := prefix_failure_envelope_superpolynomial 0
  simpa only [Real.rpow_one,Real.rpow_zero,one_mul,mul_add,add_mul,mul_zero,
    add_zero,Function.comp_def,mul_assoc] using (h1.const_mul 2).add h0

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Filter Classical

namespace SharpTerminalLeave

theorem sharp_terminal_leave_l2 :
    Tendsto (fun n => expectation n (fun G =>
      (normalizedLeave n G-sharpConstant)^2)) atTop (𝓝 0) := by
  obtain ⟨c,hc,C,hprefix⟩ := uniform_prefix_obligation
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le
      (pmfMean_nonneg (terminalLaw n) (fun G _ => sq_nonneg (normalizedLeave n G-sharpConstant))))
  · intro b hb
    have hb2 : 0 < b/2 := by linarith
    filter_upwards [hprefix,main_l2_prefix_failure_bound c C hc (b/2) hb2,
      (tendsto_order.mp prefix_failure_l2_envelope_tendsto).2 (b/2) hb2] with n hpre hmain htail
    have hh := mul_le_mul_of_nonneg_left hpre (by positivity : 0 ≤ 2*(n : ℝ)+1)
    linarith only [hmain,hh,htail]

theorem sharp_terminal_leave_probability (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => probability n (fun G =>
      ε < |normalizedLeave n G-sharpConstant|)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    apply pmfMean_nonneg (terminalLaw n)
    intro G _
    split_ifs <;> norm_num
  · intro n
    exact pmfMean_markov_sq (terminalLaw n) (fun G => normalizedLeave n G-sharpConstant) ε hε
  · simpa only [zero_div,expectation,pmfMean] using sharp_terminal_leave_l2.div_const (ε^2)

theorem sharp_terminal_leave_expectation :
    Tendsto (fun n => expectation n (fun G => (G.card : ℝ))/normalization n)
      atTop (𝓝 sharpConstant) := by
  have hmean : Tendsto (fun n => expectation n (normalizedLeave n)) atTop (𝓝 sharpConstant) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp sharp_terminal_leave_l2).2 (ε^2) (sq_pos_of_pos hε)] with n hn
    have hh := pmfMean_sq_le (terminalLaw n) (fun G => normalizedLeave n G-sharpConstant)
    rw [pmfMean_sub,pmfMean_const] at hh
    rw [Real.dist_eq]
    apply (sq_lt_sq₀ (abs_nonneg _) hε.le).mp
    rw [sq_abs]
    exact hh.trans_lt hn
  simpa only [expectation_normalizedLeave] using hmean

theorem sharp_terminal_leave_oai :
    Tendsto (fun n => expectation n (fun G =>
      (normalizedLeave n G - sharpConstant) ^ 2)) atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => probability n (fun G =>
        ε < |normalizedLeave n G - sharpConstant|)) atTop (𝓝 0)) ∧
    Tendsto (fun n => expectation n (fun G => (G.card : ℝ)) / normalization n)
      atTop (𝓝 sharpConstant) :=
  ⟨sharp_terminal_leave_l2,sharp_terminal_leave_probability,sharp_terminal_leave_expectation⟩

end SharpTerminalLeave
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.sharp_terminal_leave_oai := @OAI.SharpTerminalLeave.sharp_terminal_leave_oai
