-- Prove2me | solution 1 for OAI.BalancedTransport.balanced_three_stack_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T15:56:33.631015+00:00
-- url     : https://prove2.me/submissions/30c66526-827f-444b-9266-943fdb06f494

import Mathlib
import Definitions.Def_BalancedThreeStack

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

def rhoPolynomial : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => X ^ 2 * (rhoPolynomial n - (rhoPolynomial n).derivative)

def rhoWeight (p : Polynomial ℤ) (k : ℕ) : ℕ :=
  ∑ j ∈ p.support, (p.coeff j).natAbs * (j + k).factorial

def rhoJet (n : ℕ) (x : ℝ) : ℝ :=
  (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) x⁻¹ * expNegInvGlue x

lemma rhoJet_zero (x : ℝ) : rhoJet 0 x = expNegInvGlue x := by
  simp [rhoJet, rhoPolynomial]

lemma rhoJet_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (rhoJet n) (rhoJet (n + 1) x) x := by
  unfold rhoJet
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    ((rhoPolynomial n).map (Int.castRingHom ℝ)) x
  simpa [rhoJet, rhoPolynomial, ← Polynomial.eval₂_eq_eval_map,
    Polynomial.derivative_map] using h

lemma rhoJet_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rhoJet n) := by
  unfold rhoJet
  simpa only [← Polynomial.eval₂_eq_eval_map] using
    (expNegInvGlue.contDiff_polynomial_eval_inv_mul
      ((rhoPolynomial n).map (Int.castRingHom ℝ)) (n := (⊤ : ℕ∞)))

lemma rhoJet_eq_iteratedDeriv (n : ℕ) : rhoJet n = iteratedDeriv n expNegInvGlue := by
  induction n with
  | zero => exact funext rhoJet_zero
  | succ n ih =>
    rw [iteratedDeriv_succ, ← ih]
    exact funext (fun x => (rhoJet_hasDerivAt n x).deriv.symm)

lemma rhoJet_zero_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) : rhoJet n x = 0 := by
  simp [rhoJet, expNegInvGlue.zero_of_nonpos hx]

lemma inv_pow_mul_rho_le {x : ℝ} (hx : 0 < x) (j k : ℕ) :
    x⁻¹ ^ j * expNegInvGlue x ≤ ((j + k).factorial : ℝ) * x ^ k := by
  have hf : (0 : ℝ) < (j + k).factorial := by positivity
  have he := Real.pow_div_factorial_le_exp x⁻¹ (inv_nonneg.mpr hx.le) (j + k)
  have hdiv : x⁻¹ ^ (j + k) / Real.exp x⁻¹ ≤ ((j + k).factorial : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    simpa [mul_comm] using (div_le_iff₀ hf).mp he
  have hid : x⁻¹ ^ j * expNegInvGlue x =
      (x⁻¹ ^ (j + k) / Real.exp x⁻¹) * x ^ k := by
    rw [expNegInvGlue, ite_eq_right hx.not_ge, Real.exp_neg, pow_add]
    field_simp
    simp [inv_mul_cancel₀ (pow_ne_zero k hx.ne')]
  rw [hid]
  exact mul_le_mul_of_nonneg_right hdiv (pow_nonneg hx.le _)

lemma polynomial_rho_seam_bound (p : Polynomial ℤ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |p.eval₂ (Int.castRingHom ℝ) x⁻¹ * expNegInvGlue x| ≤
      (rhoWeight p k : ℝ) * x ^ k := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  calc
    |∑ j ∈ p.support, (Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| ≤
        ∑ j ∈ p.support, |(Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) * (x⁻¹ ^ j * expNegInvGlue x) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [abs_mul, abs_of_pos hx,
        abs_of_nonneg (expNegInvGlue.nonneg x), mul_assoc]
    _ ≤ ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) *
        (((j + k).factorial : ℝ) * x ^ k) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (inv_pow_mul_rho_le hx j k) (Nat.cast_nonneg _)
    _ = (rhoWeight p k : ℝ) * x ^ k := by
      simp [rhoWeight, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc]

lemma rhoJet_bound (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoWeight (rhoPolynomial n) 0 : ℝ) := by
  by_cases hx : 0 < x
  · simpa [rhoJet] using polynomial_rho_seam_bound (rhoPolynomial n) 0 hx
  · rw [rhoJet_zero_of_nonpos n (le_of_not_gt hx), abs_zero]
    exact Nat.cast_nonneg _

lemma rhoJet_seam_bound (n k : ℕ) {x ε : ℝ} (hε : 0 ≤ ε) (hx : x ≤ ε) :
    |rhoJet n x| ≤ (rhoWeight (rhoPolynomial n) k : ℝ) * ε ^ k := by
  by_cases hxpos : 0 < x
  · exact (polynomial_rho_seam_bound (rhoPolynomial n) k hxpos).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxpos.le hx _) (Nat.cast_nonneg _))
  · rw [rhoJet_zero_of_nonpos n (le_of_not_gt hxpos), abs_zero]
    positivity

lemma transition_denom_lower (x : ℝ) :
    1 / 9 ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have hb : (1 / 9 : ℝ) ≤ expNegInvGlue (1 / 2) := by
    have he : Real.exp (2 : ℝ) < 9 := by
      have hh := Real.exp_one_lt_three
      have hp := Real.exp_pos 1
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    norm_num [expNegInvGlue, Real.exp_neg]
    rw [← one_div]
    apply (le_div_iff₀ (Real.exp_pos (2 : ℝ))).mpr
    linarith
  by_cases hx : 1 / 2 ≤ x
  · exact hb.trans ((expNegInvGlue.monotone hx).trans
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · have hh : 1 / 2 ≤ 1 - x := by linarith
    exact hb.trans ((expNegInvGlue.monotone hh).trans
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

def transitionWeight : ℕ → ℕ
  | 0 => 1
  | n + 1 => 9 * (rhoWeight (rhoPolynomial (n + 1)) 0 +
      ∑ i : Fin (n + 1),
        (n + 1).choose i * transitionWeight i *
          (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0))
termination_by n => n
decreasing_by exact i.isLt

def transitionDenom (x : ℝ) : ℝ := expNegInvGlue x + expNegInvGlue (1 - x)

lemma transitionDenom_contDiff : ContDiff ℝ (⊤ : ℕ∞) transitionDenom := by
  unfold transitionDenom
  fun_prop

lemma transitionDenom_jet_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n transitionDenom x| ≤ (2 * rhoWeight (rhoPolynomial n) 0 : ℕ) := by
  have ha : ContDiffAt ℝ n expNegInvGlue x := expNegInvGlue.contDiff.contDiffAt
  have hb : ContDiffAt ℝ n (fun x : ℝ => expNegInvGlue (1 - x)) x := by fun_prop
  unfold transitionDenom
  rw [iteratedDeriv_fun_add ha hb, iteratedDeriv_comp_const_sub]
  calc
    |iteratedDeriv n expNegInvGlue x + (-1 : ℝ) ^ n • iteratedDeriv n expNegInvGlue (1 - x)| ≤
        |iteratedDeriv n expNegInvGlue x| +
          |(-1 : ℝ) ^ n • iteratedDeriv n expNegInvGlue (1 - x)| := abs_add_le _ _
    _ = |rhoJet n x| + |rhoJet n (1 - x)| := by
      simp [← rhoJet_eq_iteratedDeriv, smul_eq_mul, abs_mul, abs_pow]
    _ ≤ (2 * rhoWeight (rhoPolynomial n) 0 : ℕ) := by
      have h₁ := rhoJet_bound n x
      have h₂ := rhoJet_bound n (1 - x)
      push_cast
      linarith

lemma transition_mul_denom : Real.smoothTransition * transitionDenom = expNegInvGlue := by
  funext x
  exact div_mul_cancel₀ _ (Real.smoothTransition.pos_denom x).ne'

lemma transition_jet_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n Real.smoothTransition x| ≤ (transitionWeight n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [iteratedDeriv_zero, transitionWeight]
      rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
      simpa using Real.smoothTransition.le_one x
    | succ n =>
      have hs : ContDiffAt ℝ (n + 1) Real.smoothTransition x :=
        Real.smoothTransition.contDiffAt
      have hd : ContDiffAt ℝ (n + 1) transitionDenom x :=
        transitionDenom_contDiff.contDiffAt.of_le
          (WithTop.coe_le_coe.mpr (show (↑(n + 1) : ℕ∞) ≤ ⊤ from le_top))
      have hL := iteratedDeriv_mul hs hd
      rw [transition_mul_denom, Finset.sum_range_succ] at hL
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        iteratedDeriv_zero] at hL
      let S : ℝ := ∑ i ∈ Finset.range (n + 1),
        (n + 1).choose i * iteratedDeriv i Real.smoothTransition x *
          iteratedDeriv (n + 1 - i) transitionDenom x
      let Q : ℕ := ∑ i ∈ Finset.range (n + 1),
        (n + 1).choose i * transitionWeight i *
          (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0)
      have hS : |S| ≤ (Q : ℝ) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        dsimp only [Q]
        push_cast
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (ih i (Finset.mem_range.mp hi)) (Nat.cast_nonneg _)
        · simpa using transitionDenom_jet_bound (n + 1 - i) x
        · exact abs_nonneg _
        · positivity
      have he : iteratedDeriv (n + 1) Real.smoothTransition x * transitionDenom x =
          rhoJet (n + 1) x - S := by
        rw [rhoJet_eq_iteratedDeriv]
        linarith [hL]
      have hden := transition_denom_lower x
      change 1 / 9 ≤ transitionDenom x at hden
      have hp : 0 < transitionDenom x := by linarith
      have hbound : |iteratedDeriv (n + 1) Real.smoothTransition x| * transitionDenom x ≤
          (rhoWeight (rhoPolynomial (n + 1)) 0 : ℝ) + (Q : ℝ) := by
        rw [← abs_of_pos hp, ← abs_mul, he]
        exact (abs_sub _ _).trans (add_le_add (rhoJet_bound _ _) hS)
      have habs := abs_nonneg (iteratedDeriv (n + 1) Real.smoothTransition x)
      have hprod := mul_le_mul_of_nonneg_left hden habs
      rw [transitionWeight, show (∑ i : Fin (n + 1),
        (n + 1).choose i * transitionWeight i *
          (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0)) = Q from
          Fin.sum_univ_eq_sum_range (fun i : ℕ => (n + 1).choose i * transitionWeight i *
            (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0)) (n + 1)]
      push_cast
      change _ ≤ 9 * ((rhoWeight (rhoPolynomial (n + 1)) 0 : ℝ) + (Q : ℝ))
      nlinarith

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder

instance : Fintype Direction :=
  ⟨{.stay, .left, .right}, by intro d; cases d <;> simp⟩

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport

end BalancedTransport
end

noncomputable section
namespace BalancedTransport
open MeasureTheory
open scoped ENNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end BalancedTransport
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Encodable

lemma primrec_int_ofNat : Primrec (Int.ofNat : ℕ → ℤ) := by
  apply Primrec.encode_iff.mp
  exact Primrec.nat_double

lemma primrec_int_negSucc : Primrec (Int.negSucc : ℕ → ℤ) := by
  apply Primrec.encode_iff.mp
  exact Primrec.nat_double_succ

lemma primrec_int_cases {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a) := by
  refine (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp hf))
    (hh.comp Primrec.id (Primrec.nat_div2.comp (Primrec.encode.comp hf)))
    (hg.comp Primrec.id (Primrec.nat_div2.comp (Primrec.encode.comp hf)))).of_eq ?_
  intro a
  generalize he : f a = z
  cases z with
  | ofNat n =>
    change (bif (2*n).bodd then h a (2*n).div2 else g a (2*n).div2) = g a n
    simp [Nat.div2_val]
  | negSucc n =>
    change (bif (2*n+1).bodd then h a (2*n+1).div2 else g a (2*n+1).div2) = h a n
    simp [Nat.div2_val]

lemma primrec_int_natAbs : Primrec Int.natAbs := by
  exact (primrec_int_cases Primrec.id Primrec.snd.to₂
    (Primrec.succ.comp Primrec.snd).to₂).of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_toNat : Primrec Int.toNat := by
  exact (primrec_int_cases Primrec.id Primrec.snd.to₂
    (Primrec.const 0).to₂).of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_neg : Primrec (fun z : ℤ => -z) := by
  have h₀ : Primrec (fun n : ℕ => -(n : ℤ)) := by
    refine (Primrec.nat_casesOn Primrec.id (Primrec.const (0 : ℤ))
      (primrec_int_negSucc.comp Primrec.snd).to₂).of_eq ?_
    intro n; cases n <;> rfl
  exact (primrec_int_cases Primrec.id (h₀.comp Primrec.snd).to₂
    (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
      (fun z => by cases z <;> rfl)

lemma primrec_int_natSub : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  refine (Primrec.ite Primrec.nat_le
    (primrec_int_neg.comp (primrec_int_ofNat.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)))
    (primrec_int_ofNat.comp Primrec.nat_sub)).of_eq ?_
  intro ⟨a,b⟩
  dsimp
  split_ifs with h
  · rw [Int.ofNat_sub h]; ring
  · rw [Int.ofNat_sub (by omega)]

lemma primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have h₀ : Primrec₂ (fun a : ℕ => fun z : ℤ => (a : ℤ) + z) := by
    refine (primrec_int_cases Primrec.snd
      (primrec_int_ofNat.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (primrec_int_natSub.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).to₂).of_eq ?_
    intro ⟨a,z⟩; cases z <;> simp [Int.negSucc_eq, sub_eq_add_neg]
  have h₁ : Primrec₂ (fun a : ℕ => fun z : ℤ => Int.negSucc a + z) := by
    refine (primrec_int_neg.comp
      (h₀.comp (Primrec.succ.comp Primrec.fst) (primrec_int_neg.comp Primrec.snd))).of_eq ?_
    intro ⟨a,z⟩; simp; omega
  exact (primrec_int_cases Primrec.fst
    (h₀.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
    (h₁.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).of_eq
      (fun ⟨z,w⟩ => by cases z <;> rfl)

lemma primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have h₀ : Primrec₂ (fun a : ℕ => fun z : ℤ => (a : ℤ) * z) := by
    refine (primrec_int_cases Primrec.snd
      (primrec_int_ofNat.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (primrec_int_neg.comp (primrec_int_ofNat.comp
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)))).to₂).of_eq ?_
    intro ⟨a,z⟩; cases z <;> simp [Int.negSucc_eq, mul_add]
  have h₁ : Primrec₂ (fun a : ℕ => fun z : ℤ => Int.negSucc a * z) := by
    refine (primrec_int_neg.comp
      (h₀.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)).of_eq ?_
    intro ⟨a,z⟩; simp only [Int.negSucc_eq]; push_cast; ring
  exact (primrec_int_cases Primrec.fst
    (h₀.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
    (h₁.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).of_eq
      (fun ⟨z,w⟩ => by cases z <;> rfl)

lemma computable_find {α : Type*} [Primcodable α] {p : α → ℕ → Prop}
    [DecidableRel p] (hp : Computable₂ (fun a n => decide (p a n)))
    (hex : ∀ a, ∃ n, p a n) : Computable (fun a => Nat.find (hex a)) := by
  have hp' : Partrec₂ (fun a n => Part.some (decide (p a n))) := hp.partrec
  refine (Partrec.rfind hp').of_eq_tot ?_
  intro a
  apply Nat.mem_rfind.mpr
  constructor
  · simpa using Nat.find_spec (hex a)
  · intro m hm
    simpa using Nat.find_min (hex a) hm

lemma primrec_nat_dvd : PrimrecRel ((· ∣ ·) : ℕ → ℕ → Prop) := by
  exact (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst)
    (Primrec.const 0)).of_eq (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

lemma primrec_nat_gcd : Primrec₂ Nat.gcd := by
  have hp : PrimrecRel (fun ab : ℕ × ℕ => fun k => k ∣ ab.1 ∧ k ∣ ab.2) :=
    (primrec_nat_dvd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (primrec_nat_dvd.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  refine (Primrec.nat_findGreatest Primrec.nat_add hp).of_eq ?_
  intro ⟨a,b⟩
  dsimp only
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨?_, (fun _ => ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩), ?_⟩
  · rcases eq_or_lt_of_le (Nat.zero_le (a+b)) with h | h
    · have : a = 0 ∧ b = 0 := by omega
      simp [this.1, this.2]
    · exact Nat.le_of_dvd h (dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  · intro k hk hkb ⟨hka, hkb'⟩
    have hd := Nat.dvd_gcd hka hkb'
    have hg : 0 < a.gcd b := by
      by_contra hn
      have : a = 0 ∧ b = 0 := Nat.gcd_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hn)
      omega
    exact (not_le_of_gt hk) (Nat.le_of_dvd hg hd)

lemma primrec_nat_coprime : PrimrecRel Nat.Coprime := by
  exact (Primrec.eq.comp primrec_nat_gcd (Primrec.const 1)).of_eq
    (fun _ => Iff.rfl)

def rawRatCode (q : ℚ) : ℕ := Nat.pair (Encodable.encode q.num) q.den

def validRatCode (n : ℕ) : Prop :=
  0 < n.unpair.2 ∧ (Denumerable.ofNat ℤ n.unpair.1).natAbs.Coprime n.unpair.2

instance : DecidablePred validRatCode := fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma primrec_validRatCode : PrimrecPred validRatCode := by
  exact (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.snd.comp Primrec.unpair)).and
    (primrec_nat_coprime.comp
      (primrec_int_natAbs.comp ((Primrec.ofNat ℤ).comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))

lemma rawRatCode_eq (q : ℚ) : rawRatCode q = @Encodable.encode ℚ Rat.instEncodable q := rfl

lemma validRatCode_iff (n : ℕ) :
    validRatCode n ↔ n ∈ Set.range (@Encodable.encode ℚ Rat.instEncodable) := by
  constructor
  · rintro ⟨hp, hc⟩
    let q : ℚ := ⟨Denumerable.ofNat ℤ n.unpair.1, n.unpair.2, hp.ne', hc⟩
    refine ⟨q, ?_⟩
    change Nat.pair (Encodable.encode (Denumerable.ofNat ℤ n.unpair.1)) n.unpair.2 = n
    exact (congrArg (fun k => Nat.pair k n.unpair.2) (Denumerable.encode_ofNat _)).trans (Nat.pair_unpair _)
  · rintro ⟨q, rfl⟩
    change validRatCode (rawRatCode q)
    simpa only [validRatCode, rawRatCode, Nat.unpair_pair, Denumerable.ofNat_encode] using And.intro q.pos q.reduced

def ratRank (n : ℕ) : ℕ := ((List.range n).filter (fun n => decide (validRatCode n))).length

lemma primrec_ratRank : Primrec ratRank :=
  Primrec.list_length.comp ((Primrec.listFilter primrec_validRatCode).comp Primrec.list_range)

lemma ratRank_code (q : ℚ) : ratRank (rawRatCode q) =
    @Encodable.encode ℚ (inferInstance : Primcodable ℚ).toEncodable q := by
  let := @Encodable.decidableRangeEncode ℚ Rat.instEncodable
  change ((List.range (rawRatCode q)).filter _).length =
    (List.range (rawRatCode q)).countP (fun n => decide
      (n ∈ Set.range (@Encodable.encode ℚ Rat.instEncodable)))
  rw [List.countP_eq_length_filter]
  simp only [validRatCode_iff]

lemma rawRatCode_injective : Function.Injective rawRatCode :=
  @Encodable.encode_injective ℚ Rat.instEncodable

lemma ratRank_injective_valid {m n : ℕ} (hm : validRatCode m) (hn : validRatCode n)
    (h : ratRank m = ratRank n) : m = n := by
  obtain ⟨a, rfl⟩ := (validRatCode_iff m).mp hm
  obtain ⟨b, rfl⟩ := (validRatCode_iff n).mp hn
  rw [← rawRatCode_eq, ← rawRatCode_eq, ratRank_code, ratRank_code] at h
  exact congrArg (@Encodable.encode ℚ Rat.instEncodable)
    (@Encodable.encode_injective ℚ (inferInstance : Primcodable ℚ).toEncodable _ _ h)

lemma computable_rawRatCode : Computable rawRatCode := by
  have hx : ∀ n : ℕ, ∃ k, validRatCode k ∧ ratRank k = n := by
    intro n
    refine ⟨rawRatCode (Denumerable.ofNat ℚ n), ?_, ?_⟩
    · exact (validRatCode_iff _).mpr ⟨_, rfl⟩
    · rw [ratRank_code, Denumerable.encode_ofNat]
  have hp : PrimrecRel (fun n k => validRatCode k ∧ ratRank k = n) :=
    (primrec_validRatCode.comp Primrec.snd).and
      (Primrec.eq.comp (primrec_ratRank.comp Primrec.snd) Primrec.fst)
  refine ((computable_find hp.decide.to_comp hx).comp Primrec.encode.to_comp).of_eq ?_
  intro q
  apply ratRank_injective_valid (Nat.find_spec (hx _)).1 ((validRatCode_iff _).mpr ⟨q,rfl⟩)
  exact (Nat.find_spec (hx _)).2.trans (ratRank_code q).symm

lemma computable_rat_num : Computable Rat.num := by
  refine (((Primrec.ofNat ℤ).to_comp.comp
    (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp computable_rawRatCode)))).of_eq ?_
  intro q
  simp only [rawRatCode, Nat.unpair_pair, Denumerable.ofNat_encode]

lemma computable_rat_den : Computable Rat.den := by
  exact ((Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp computable_rawRatCode))).of_eq
    (fun q => by simp [rawRatCode])

lemma rat_fraction_eq_iff (q : ℚ) (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    q = (n : ℚ) / d ↔ q.num * (d : ℤ) = n * (q.den : ℤ) := by
  have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have h := @Rat.divInt_eq_divInt_iff q.den d q.num n hden hd'
  simpa only [Rat.num_divInt_den, Rat.divInt_eq_div, Rat.intCast_natCast, Rat.num_div_den] using h

lemma computable_rat_of_parts {α : Type*} [Primcodable α]
    {n : α → ℤ} {d : α → ℕ} (hn : Computable n) (hd : Computable d)
    (hpos : ∀ a, d a ≠ 0) : Computable (fun a => (n a : ℚ) / d a) := by
  let p : α → ℕ → Prop := fun a k =>
    (Denumerable.ofNat ℚ k).num * (d a : ℤ) =
      n a * ((Denumerable.ofNat ℚ k).den : ℤ)
  have hn' : Computable (fun k => (Denumerable.ofNat ℚ k).num) :=
    computable_rat_num.comp (Computable.ofNat ℚ)
  have hd' : Computable (fun k => ((Denumerable.ofNat ℚ k).den : ℤ)) :=
    primrec_int_ofNat.to_comp.comp (computable_rat_den.comp (Computable.ofNat ℚ))
  have hl : Computable (fun ak : α × ℕ => (Denumerable.ofNat ℚ ak.2).num * (d ak.1 : ℤ)) :=
    primrec_int_mul.to_comp.comp (hn'.comp Computable.snd)
      ((primrec_int_ofNat.to_comp.comp hd).comp Computable.fst)
  have hr : Computable (fun ak : α × ℕ => n ak.1 * ((Denumerable.ofNat ℚ ak.2).den : ℤ)) :=
    primrec_int_mul.to_comp.comp (hn.comp Computable.fst) (hd'.comp Computable.snd)
  have hp : Computable₂ (fun a k => decide (p a k)) :=
    Primrec.eq.decide.to_comp.comp hl hr
  have hx : ∀ a, ∃ k, p a k := by
    intro a
    refine ⟨@Encodable.encode ℚ (inferInstance : Primcodable ℚ).toEncodable ((n a : ℚ) / d a), ?_⟩
    dsimp [p]
    rw [Denumerable.ofNat_encode]
    exact (rat_fraction_eq_iff _ _ _ (hpos a)).mp rfl
  refine ((Computable.ofNat ℚ).comp (computable_find hp hx)).of_eq ?_
  intro a
  exact (rat_fraction_eq_iff _ _ _ (hpos a)).mpr (Nat.find_spec (hx a))

lemma computable_rat_add : Computable₂ ((· + ·) : ℚ → ℚ → ℚ) := by
  have ha : Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.fst)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.snd)
  have hb : Computable (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.snd)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.fst)
  have hn : Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ)) :=
    primrec_int_add.to_comp.comp ha hb
  have hd : Computable (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
    Primrec.nat_mul.to_comp.comp (computable_rat_den.comp Computable.fst) (computable_rat_den.comp Computable.snd)
  refine (computable_rat_of_parts hn hd (fun p => mul_ne_zero p.1.den_ne_zero p.2.den_ne_zero)).of_eq ?_
  intro ⟨a,b⟩
  dsimp
  push_cast
  rw [add_div, mul_div_mul_right _ _ (by exact_mod_cast b.den_ne_zero : (b.den : ℚ) ≠ 0)]
  rw [mul_comm (a.den : ℚ), mul_div_mul_right _ _ (by exact_mod_cast a.den_ne_zero : (a.den : ℚ) ≠ 0)]
  rw [Rat.num_div_den, Rat.num_div_den]

lemma computable_rat_mul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ) := by
  have hn : Computable (fun p : ℚ × ℚ => p.1.num * p.2.num) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.fst) (computable_rat_num.comp Computable.snd)
  have hd : Computable (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
    Primrec.nat_mul.to_comp.comp (computable_rat_den.comp Computable.fst) (computable_rat_den.comp Computable.snd)
  refine (computable_rat_of_parts hn hd (fun p => mul_ne_zero p.1.den_ne_zero p.2.den_ne_zero)).of_eq ?_
  intro ⟨a,b⟩
  dsimp
  push_cast
  rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]

lemma computable_rat_neg : Computable (fun q : ℚ => -q) := by
  exact (computable_rat_of_parts (primrec_int_neg.to_comp.comp computable_rat_num)
    computable_rat_den Rat.den_ne_zero).of_eq (fun q => by
      push_cast
      rw [neg_div, Rat.num_div_den])

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_ite {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  exact (Computable.cond hp hf hg).of_eq (fun a => by
    by_cases h : p a <;> simp [h])

lemma primrec_int_nonneg : PrimrecPred (fun z : ℤ => 0 ≤ z) := by
  refine ⟨inferInstance, (primrec_int_cases Primrec.id (Primrec.const true).to₂
    (Primrec.const false).to₂).of_eq ?_⟩
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

lemma primrec_int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) := by
  exact (primrec_int_nonneg.comp
    (primrec_int_add.comp Primrec.snd (primrec_int_neg.comp Primrec.fst))).of_eq
    (fun p => by simp only [← sub_eq_add_neg, sub_nonneg])

lemma computable_rat_le : Computable₂ (fun a b : ℚ => decide (a ≤ b)) := by
  have ha : Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.fst)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.snd)
  have hb : Computable (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.snd)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.fst)
  refine ((primrec_int_le.decide.to_comp).comp ha hb).of_eq ?_
  intro ⟨a,b⟩
  have he : a.num * (b.den : ℤ) ≤ b.num * (a.den : ℤ) ↔ a ≤ b := by
    simpa only [Rat.num_divInt_den] using
      (Rat.divInt_le_divInt (a := a.num) (c := b.num) (by exact_mod_cast a.pos : (0 : ℤ) < a.den)
        (by exact_mod_cast b.pos : (0 : ℤ) < b.den)).symm
  simp only [he]

lemma computable_rat_abs : Computable (fun q : ℚ => |q|) := by
  exact (computable_ite (computable_rat_le.comp (Computable.const 0) Computable.id)
    Computable.id computable_rat_neg).of_eq (fun q => by
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · exact (abs_of_neg (lt_of_not_ge h)).symm)

lemma computable_rat_sub : Computable₂ ((· - ·) : ℚ → ℚ → ℚ) := by
  exact (computable_rat_add.comp Computable.fst (computable_rat_neg.comp Computable.snd)).of_eq
    (fun _ => (sub_eq_add_neg _ _).symm)

lemma computable_rat_natCast : Computable (fun n : ℕ => (n : ℚ)) := by
  exact (computable_rat_of_parts primrec_int_ofNat.to_comp (Computable.const 1)
    (fun _ => by decide)).of_eq (fun n => by norm_cast; simp)

lemma computable_rat_intCast : Computable (fun n : ℤ => (n : ℚ)) := by
  exact (computable_rat_of_parts Computable.id (Computable.const 1)
    (fun _ => by decide)).of_eq (fun n => by norm_num)

lemma primrec_int_sign : Primrec Int.sign := by
  have h : Primrec (fun n : ℕ => if n = 0 then (0 : ℤ) else 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1)
  refine (primrec_int_cases Primrec.id (h.comp Primrec.snd).to₂
    (Primrec.const (-1 : ℤ)).to₂).of_eq ?_
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

lemma computable_rat_inv : Computable (fun q : ℚ => q⁻¹) := by
  have hn : Computable (fun q : ℚ => q.num.sign * (q.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (primrec_int_sign.to_comp.comp computable_rat_num)
      (primrec_int_ofNat.to_comp.comp computable_rat_den)
  have hnum : Computable (fun q : ℚ => q⁻¹.num) := hn.of_eq (fun q => (Rat.num_inv q).symm)
  have hd : Computable (fun q : ℚ => q⁻¹.den) := by
    refine (computable_ite (Primrec.eq.decide.to_comp.comp computable_rat_num (Computable.const 0))
      (Computable.const 1) (primrec_int_natAbs.to_comp.comp computable_rat_num)).of_eq ?_
    intro q
    exact (Rat.den_inv q).symm
  exact (computable_rat_of_parts hnum hd (fun q => q⁻¹.den_ne_zero)).of_eq
    (fun q => Rat.num_div_den q⁻¹)

lemma computable_rat_div : Computable₂ ((· / ·) : ℚ → ℚ → ℚ) := by
  exact (computable_rat_mul.comp Computable.fst (computable_rat_inv.comp Computable.snd)).of_eq
    (fun _ => (div_eq_mul_inv _ _).symm)

lemma primrec_nat_factorial : Primrec Nat.factorial := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => ℕ) 1 (fun n r => (n + 1) * r) n) :=
    Primrec.nat_rec (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine (h.comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [Nat.factorial_succ] using congrArg (fun k => (n + 1) * k) ih

lemma computable_rat_pow : Computable₂ ((· ^ ·) : ℚ → ℕ → ℚ) := by
  have h : Computable (fun p : ℚ × ℕ =>
      Nat.rec (motive := fun _ => ℚ) (1 : ℚ) (fun _ r => r * p.1) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const 1)
      (computable_rat_mul.comp (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.fst)).to₂
  refine h.of_eq ?_
  intro ⟨q,n⟩
  dsimp
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using congrArg (fun r => r * q) ih

lemma computable_sum_range {α : Type*} [Primcodable α]
    {f : α → ℕ → ℚ} (hf : Computable₂ f) :
    Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hh : Computable (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => ℚ) (0 : ℚ) (fun n r => r + f p.1 n) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const 0)
      (computable_rat_add.comp (Computable.snd.comp Computable.snd)
        (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  refine hh.of_eq ?_
  intro ⟨a,n⟩
  dsimp
  induction n with
  | zero => simp
  | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun r => r + f a n) ih

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

def expAccurate (q : ℚ) (n k : ℕ) : Prop :=
  |q| / ((k + 1 : ℕ) : ℚ) ≤ 1 / 2 ∧
    |q| ^ k / ((k.factorial : ℕ) : ℚ) * 2 ≤ (1 / 2 : ℚ) ^ n

instance (q : ℚ) (n : ℕ) : DecidablePred (expAccurate q n) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma computable_decide_and {α : Type*} [Primcodable α]
    {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Computable fun a => decide (p a)) (hq : Computable fun a => decide (q a)) :
    Computable (fun a => decide (p a ∧ q a)) := by
  exact (Computable.cond hp hq (Computable.const false)).of_eq (fun a => by
    by_cases h : p a <;> simp [h])

lemma computable_expAccurate :
    Computable₂ (fun p : ℚ × ℕ => fun k => decide (expAccurate p.1 p.2 k)) := by
  have hq : Computable (fun p : (ℚ × ℕ) × ℕ => |p.1.1|) :=
    computable_rat_abs.comp (Computable.fst.comp Computable.fst)
  have hr : Computable (fun p : (ℚ × ℕ) × ℕ => |p.1.1| / ((p.2 + 1 : ℕ) : ℚ)) :=
    computable_rat_div.comp hq (computable_rat_natCast.comp (Computable.succ.comp Computable.snd))
  have ha : Computable (fun p : (ℚ × ℕ) × ℕ =>
      |p.1.1| ^ p.2 / (p.2.factorial : ℚ) * 2) :=
    computable_rat_mul.comp (computable_rat_div.comp (computable_rat_pow.comp hq Computable.snd)
      (computable_rat_natCast.comp (primrec_nat_factorial.to_comp.comp Computable.snd)))
      (Computable.const 2)
  exact computable_decide_and
    (computable_rat_le.comp hr (Computable.const (1 / 2)))
    (computable_rat_le.comp ha (computable_rat_pow.comp (Computable.const (1 / 2))
      (Computable.snd.comp Computable.fst)))

lemma exists_expAccurate (q : ℚ) (n : ℕ) : ∃ k, expAccurate q n k := by
  have h₀ : Tendsto (fun k : ℕ => (|q| : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_iff.mpr (tendsto_add_atTop_nat 1))
  have h₁ : Tendsto (fun k : ℕ => (|q| : ℝ) ^ k / (k.factorial : ℝ) * 2)
      atTop (𝓝 0) := by
    simpa using (Real.summable_pow_div_factorial (|q| : ℝ)).tendsto_atTop_zero.mul_const 2
  have he : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hh₀ := h₀.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hh₁ := h₁.eventually_lt_const he
  obtain ⟨k, hk₀, hk₁⟩ := (hh₀.and hh₁).exists
  refine ⟨k, ?_, ?_⟩
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one] using hk₀.le
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hk₁.le

noncomputable def expCutoff (q : ℚ) (n : ℕ) : ℕ :=
  Nat.find (exists_expAccurate q n)

lemma computable_expCutoff : Computable₂ expCutoff :=
  computable_find computable_expAccurate (fun p => exists_expAccurate p.1 p.2)

noncomputable def expApprox (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (expCutoff q n), q ^ k / (k.factorial : ℚ)

lemma computable_expApprox : Computable₂ expApprox := by
  have hs : Computable₂ (fun q : ℚ => fun n : ℕ =>
      ∑ k ∈ Finset.range n, q ^ k / (k.factorial : ℚ)) :=
    computable_sum_range (computable_rat_div.comp computable_rat_pow
      (computable_rat_natCast.comp (primrec_nat_factorial.to_comp.comp Computable.snd)))
  exact hs.comp Computable.fst computable_expCutoff

lemma real_exp_tail_bound (x : ℝ) (k : ℕ) (h : |x| / (k + 1 : ℕ) ≤ 1 / 2) :
    |Real.exp x - ∑ j ∈ Finset.range k, x ^ j / (j.factorial : ℝ)| ≤
      |x| ^ k / (k.factorial : ℝ) * 2 := by
  have hc : ‖(x : ℂ)‖ / (k + 1 : ℕ) ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  have hh := @Complex.exp_bound' (x : ℂ) k hc
  rw [← Complex.ofReal_exp] at hh
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

lemma expApprox_spec (q : ℚ) (n : ℕ) :
    |(expApprox q n : ℝ) - Real.exp (q : ℝ)| ≤ error n := by
  have hk := Nat.find_spec (exists_expAccurate q n)
  change expAccurate q n (expCutoff q n) at hk
  have hrat : |(q : ℝ)| / ((expCutoff q n + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hk.1
    push_cast at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hb := real_exp_tail_bound (q : ℝ) (expCutoff q n) hrat
  have ht : |(q : ℝ)| ^ expCutoff q n / ((expCutoff q n).factorial : ℝ) * 2 ≤ error n := by
    dsimp [error]
    have hh := (Rat.cast_le (K := ℝ)).mpr hk.2
    push_cast at hh
    simpa only [one_div] using hh
  rw [abs_sub_comm]
  simpa only [expApprox, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    using hb.trans ht

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder

structure Machine (Q Γ : Type*) where
  halt : Q
  blank : Γ
  transition : Q → Γ → Transition Q Γ

inductive Record (Q Γ : Type*) where
  | stay (q : Q) (a : Γ)
  | left (q : Q) (a c : Γ)
  | right (q : Q) (a c : Γ)
  | extend (q : Q) (a : Γ)
  deriving DecidableEq, Fintype

inductive Letter (Q Γ : Type*) where
  | work (a : Γ)
  | marked (a : Γ)
  | boundary
  | record (r : Record Q Γ)
  deriving DecidableEq, Fintype

inductive Control (Q : Type*) where
  | ready (q : Q)
  | outward (q : Q)
  | returning (q : Q)
  | execute (q : Q)
  deriving DecidableEq, Fintype

structure Configuration (Q Γ : Type*) where
  control : Control Q
  left : Stream' (Letter Q Γ)
  right : Stream' (Letter Q Γ)
  history : Stream' (Letter Q Γ)

structure Tails (Q Γ : Type*) where
  left : Stream' (Letter Q Γ)
  right : Stream' (Letter Q Γ)
  history : Stream' (Letter Q Γ)

structure Instruction (Q Γ : Type*) where
  sourceControl : Control Q
  targetControl : Control Q
  sourceLeft : List (Letter Q Γ)
  sourceRight : List (Letter Q Γ)
  sourceHistory : List (Letter Q Γ)
  targetLeft : List (Letter Q Γ)
  targetRight : List (Letter Q Γ)
  targetHistory : List (Letter Q Γ)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
open Stream'
variable {Q Γ : Type*}

def source (r : Instruction Q Γ) (t : Tails Q Γ) : Configuration Q Γ :=
  ⟨r.sourceControl, r.sourceLeft ++ₛ t.left,
    r.sourceRight ++ₛ t.right, r.sourceHistory ++ₛ t.history⟩

def target (r : Instruction Q Γ) (t : Tails Q Γ) : Configuration Q Γ :=
  ⟨r.targetControl, r.targetLeft ++ₛ t.left,
    r.targetRight ++ₛ t.right, r.targetHistory ++ₛ t.history⟩

def sourceTails (r : Instruction Q Γ) (c : Configuration Q Γ) : Tails Q Γ :=
  ⟨Stream'.drop r.sourceLeft.length c.left,
    Stream'.drop r.sourceRight.length c.right,
    Stream'.drop r.sourceHistory.length c.history⟩

def targetTails (r : Instruction Q Γ) (c : Configuration Q Γ) : Tails Q Γ :=
  ⟨Stream'.drop r.targetLeft.length c.left,
    Stream'.drop r.targetRight.length c.right,
    Stream'.drop r.targetHistory.length c.history⟩

@[simp] theorem sourceTails_source (r : Instruction Q Γ) (t : Tails Q Γ) :
    r.sourceTails (r.source t) = t := by
  cases t
  simp [sourceTails, source, Stream'.drop_append_stream]

@[simp] theorem targetTails_target (r : Instruction Q Γ) (t : Tails Q Γ) :
    r.targetTails (r.target t) = t := by
  cases t
  simp [targetTails, target, Stream'.drop_append_stream]

def Balanced (r : Instruction Q Γ) : Prop :=
  r.sourceLeft.length + r.sourceRight.length + r.sourceHistory.length =
    r.targetLeft.length + r.targetRight.length + r.targetHistory.length

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

inductive Row (Q Γ : Type*) where
  | enter (q : Q) (a : Γ)
  | outward (q : Q) (c : Γ)
  | supply (q : Q)
  | backward (q : Q) (c : Γ)
  | restore (q : Q) (a : Γ)
  | stay (q : Q) (a : Γ)
  | left (q : Q) (a c : Γ)
  | right (q : Q) (a c : Γ)
  | extend (q : Q) (a : Γ)
  deriving DecidableEq, Fintype

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Row
open Stream'
variable {Q Γ : Type*}
open Control Letter

def valid (M : Machine Q Γ) : Row Q Γ → Prop
  | enter q _ | outward q _ | supply q | backward q _ | restore q _ => q ≠ M.halt
  | stay q a => q ≠ M.halt ∧ (M.transition q a).move = .stay
  | left q a _ => q ≠ M.halt ∧ (M.transition q a).move = .left
  | right q a _ | extend q a => q ≠ M.halt ∧ (M.transition q a).move = .right

def instruction (M : Machine Q Γ) : Row Q Γ → Instruction Q Γ
  | enter q a =>
      ⟨ready q, Control.outward q, [], [work a], [], [marked a], [], []⟩
  | outward q c =>
      ⟨Control.outward q, Control.outward q, [], [work c], [], [work c], [], []⟩
  | supply q =>
      ⟨Control.outward q, returning q, [], [boundary, work M.blank], [],
        [], [boundary], [work M.blank]⟩
  | backward q c =>
      ⟨returning q, returning q, [work c], [], [], [], [work c], []⟩
  | restore q a =>
      ⟨returning q, execute q, [marked a], [], [], [], [work a], []⟩
  | stay q a =>
      ⟨execute q, ready (M.transition q a).state, [], [work a], [work M.blank],
        [], [work (M.transition q a).write], [record (.stay q a)]⟩
  | left q a c =>
      ⟨execute q, ready (M.transition q a).state, [work c], [work a], [work M.blank],
        [], [work c, work (M.transition q a).write], [record (.left q a c)]⟩
  | right q a c =>
      ⟨execute q, ready (M.transition q a).state, [], [work a, work c], [work M.blank],
        [work (M.transition q a).write], [work c], [record (.right q a c)]⟩
  | extend q a =>
      ⟨execute q, ready (M.transition q a).state,
        [], [work a, boundary, work M.blank], [work M.blank],
        [work (M.transition q a).write], [work M.blank, boundary], [record (.extend q a)]⟩

theorem balanced (M : Machine Q Γ) (r : Row Q Γ) :
    (r.instruction M).Balanced := by
  cases r <;> simp [instruction, Instruction.Balanced]

end BalancedTransport.Recorder.Row
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]
open Letter Control

def sourceRow (M : Machine Q Γ) (c : Configuration Q Γ) : Option (Row Q Γ) :=
  match c.control with
  | ready q =>
      if q = M.halt then none else
      match c.right.head with
      | work a => some (.enter q a)
      | _ => none
  | outward q =>
      if q = M.halt then none else
      match c.right.head with
      | work a => some (.outward q a)
      | boundary => if c.right.tail.head = work M.blank then some (.supply q) else none
      | _ => none
  | returning q =>
      if q = M.halt then none else
      match c.left.head with
      | work a => some (.backward q a)
      | marked a => some (.restore q a)
      | _ => none
  | execute q =>
      if q = M.halt then none else
      if c.history.head = work M.blank then
        match c.right.head with
        | work a =>
            match (M.transition q a).move with
            | .stay => some (.stay q a)
            | .left =>
                match c.left.head with
                | work v => some (.left q a v)
                | _ => none
            | .right =>
                match c.right.tail.head with
                | work v => some (.right q a v)
                | boundary =>
                    if c.right.tail.tail.head = work M.blank then some (.extend q a) else none
                | _ => none
        | _ => none
      else none

def targetRow (c : Configuration Q Γ) : Option (Row Q Γ) :=
  match c.control with
  | ready _ =>
      match c.history.head with
      | record (.stay q a) => some (.stay q a)
      | record (.left q a v) => some (.left q a v)
      | record (.right q a v) => some (.right q a v)
      | record (.extend q a) => some (.extend q a)
      | _ => none
  | outward q =>
      match c.left.head with
      | marked a => some (.enter q a)
      | work a => some (.outward q a)
      | _ => none
  | returning q =>
      match c.right.head with
      | boundary => some (.supply q)
      | work a => some (.backward q a)
      | _ => none
  | execute q =>
      match c.right.head with
      | work a => some (.restore q a)
      | _ => none

@[simp] theorem sourceRow_source (M : Machine Q Γ) (r : Row Q Γ)
    (hr : r.valid M) (t : Tails Q Γ) :
    sourceRow M ((r.instruction M).source t) = some r := by
  cases r <;>
    simp_all [Row.valid, Row.instruction, Instruction.source, sourceRow,
      Stream'.appendStream', Stream'.head]

omit [DecidableEq Q] [DecidableEq Γ] in

@[simp] theorem targetRow_target (M : Machine Q Γ) (r : Row Q Γ) (t : Tails Q Γ) :
    targetRow ((r.instruction M).target t) = some r := by
  cases r <;>
    simp [Row.instruction, Instruction.target, targetRow,
      Stream'.appendStream', Stream'.head]

theorem source_separation (M : Machine Q Γ) {r s : Row Q Γ}
    (hr : r.valid M) (hs : s.valid M) {t u : Tails Q Γ}
    (he : (r.instruction M).source t = (s.instruction M).source u) : r = s ∧ t = u := by
  have hrs : r = s := by
    have hh := congrArg (sourceRow M) he
    simpa [sourceRow_source M r hr, sourceRow_source M s hs] using hh
  subst s
  exact ⟨rfl, by simpa using congrArg (Instruction.sourceTails (r.instruction M)) he⟩

omit [DecidableEq Q] [DecidableEq Γ] in

theorem target_separation (M : Machine Q Γ) {r s : Row Q Γ} {t u : Tails Q Γ}
    (he : (r.instruction M).target t = (s.instruction M).target u) : r = s ∧ t = u := by
  have hrs : r = s := by
    have hh := congrArg targetRow he
    simpa using hh
  subst s
  exact ⟨rfl, by simpa using congrArg (Instruction.targetTails (r.instruction M)) he⟩

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

def Step {Q Γ : Type*} (M : Machine Q Γ) (c d : Configuration Q Γ) : Prop :=
  ∃ r : Row Q Γ, r.valid M ∧ ∃ t : Tails Q Γ,
    c = (r.instruction M).source t ∧ d = (r.instruction M).target t

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]

theorem step_deterministic (M : Machine Q Γ) {c d e : Configuration Q Γ}
    (hd : Step M c d) (he : Step M c e) : d = e := by
  obtain ⟨r, hr, t, hrt, hrd⟩ := hd
  obtain ⟨s, hs, u, hsu, hse⟩ := he
  obtain ⟨rfl, rfl⟩ := source_separation M hr hs (hrt.symm.trans hsu)
  exact hrd.trans hse.symm

omit [DecidableEq Q] [DecidableEq Γ] in

theorem step_injective (M : Machine Q Γ) {c d e : Configuration Q Γ}
    (hc : Step M c e) (hd : Step M d e) : c = d := by
  obtain ⟨r, hr, t, hrt, hre⟩ := hc
  obtain ⟨s, hs, u, hsu, hse⟩ := hd
  obtain ⟨rfl, rfl⟩ := target_separation M (hre.symm.trans hse)
  exact hrt.trans hsu.symm

instance (M : Machine Q Γ) : DecidablePred (Row.valid M) := by
  intro r
  cases r <;> simp only [Row.valid] <;> infer_instance

def table [Fintype Q] [Fintype Γ] (M : Machine Q Γ) : Finset (Row Q Γ) :=
  Finset.univ.filter (Row.valid M)

omit [DecidableEq Γ] in

@[simp] theorem mem_table [Fintype Q] [Fintype Γ] (M : Machine Q Γ) (r : Row Q Γ) :
    r ∈ table M ↔ r.valid M := by
  simp [table]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

inductive Exec {Q Γ : Type*} (M : Machine Q Γ) :
    ℕ → Configuration Q Γ → Configuration Q Γ → Prop
  | refl (c) : Exec M 0 c c
  | cons {n c d e} : Step M c d → Exec M n d e → Exec M (n + 1) c e

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} (M : Machine Q Γ)
open Letter Control

theorem row_step (r : Row Q Γ) (hr : r.valid M) (t : Tails Q Γ) :
    Step M ((r.instruction M).source t) ((r.instruction M).target t) :=
  ⟨r, hr, t, rfl, rfl⟩

theorem outward_scan (q : Q) (hq : q ≠ M.halt) (w : List Γ)
    (L R J : Stream' (Letter Q Γ)) :
    Exec M w.length
      ⟨outward q, L, w.map work ++ₛ R, J⟩
      ⟨outward q, w.reverse.map work ++ₛ L, R, J⟩ := by
  induction w generalizing L with
  | nil => simpa using Exec.refl (M := M) (⟨outward q, L, R, J⟩ : Configuration Q Γ)
  | cons a as ih =>
      have h := row_step M (.outward q a) hq ⟨L, as.map work ++ₛ R, J⟩
      have hh := Exec.cons h (ih (work a :: L))
      simpa [Row.instruction, Instruction.source, Instruction.target,
        Stream'.appendStream', List.reverse_cons, List.map_append] using hh

theorem returning_scan (q : Q) (hq : q ≠ M.halt) (w : List Γ)
    (L R J : Stream' (Letter Q Γ)) :
    Exec M w.length
      ⟨returning q, w.map work ++ₛ L, R, J⟩
      ⟨returning q, L, w.reverse.map work ++ₛ R, J⟩ := by
  induction w generalizing R with
  | nil => simpa using Exec.refl (M := M) (⟨returning q, L, R, J⟩ : Configuration Q Γ)
  | cons a as ih =>
      have h := row_step M (.backward q a) hq ⟨as.map work ++ₛ L, R, J⟩
      have hh := Exec.cons h (ih (work a :: R))
      simpa [Row.instruction, Instruction.source, Instruction.target,
        Stream'.appendStream', List.reverse_cons, List.map_append] using hh

end BalancedTransport.Recorder
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

theorem single {source target : Configuration Q Γ} (step : Step M source target) :
    Exec M 1 source target :=
  .cons step (.refl target)

theorem trans {firstLength secondLength : ℕ} {source middle target : Configuration Q Γ}
    (first : Exec M firstLength source middle) (second : Exec M secondLength middle target) :
    Exec M (firstLength + secondLength) source target := by
  induction first with
  | refl => simpa using second
  | cons step _ inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Exec.cons step (inductionHypothesis second))

end Exec

variable (M : Machine Q Γ)
open Letter Control

theorem preparation (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L B J : Stream' (Letter Q Γ)) :
    Exec M (2 * w.length + 3)
      ⟨ready q, L, work a :: (w.map work ++ₛ (boundary :: work M.blank :: B)), J⟩
      ⟨execute q, L, work a :: (w.map work ++ₛ (boundary :: B)), work M.blank :: J⟩ := by
  have h₁ := row_step M (.enter q a) hq
    ⟨L, w.map work ++ₛ (boundary :: work M.blank :: B), J⟩
  have h₂ := outward_scan M q hq w (marked a :: L) (boundary :: work M.blank :: B) J
  have h₃ := row_step M (.supply q) hq
    ⟨w.reverse.map work ++ₛ (marked a :: L), B, J⟩
  have h₄ := returning_scan M q hq w.reverse (marked a :: L)
    (boundary :: B) (work M.blank :: J)
  have h₅ := row_step M (.restore q a) hq
    ⟨L, w.map work ++ₛ (boundary :: B), work M.blank :: J⟩
  simp only [List.reverse_reverse, List.length_reverse] at h₄
  have h₁' := Exec.single h₁
  have h₃' := Exec.single h₃
  have h₅' := Exec.single h₅
  simp only [Row.instruction, Instruction.source, Instruction.target,
    Stream'.appendStream'] at h₁' h₃' h₅'
  have hh := (((h₁'.trans h₂).trans h₃').trans h₄).trans h₅'
  convert hh using 1
  omega

theorem preparation_blank_tail (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * w.length + 3)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨execute q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        work M.blank :: J⟩ := by
  have hh := preparation M q hq a w L (Stream'.const (work M.blank)) J
  have hb : (work M.blank :: Stream'.const (work M.blank) : Stream' (Letter Q Γ)) =
      Stream'.const (work M.blank) := by
    ext n
    cases n <;> rfl
  simpa only [hb] using hh

theorem checkpoint_length (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) (d : Configuration Q Γ)
    (hd : Step M
      ⟨execute q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        work M.blank :: J⟩ d) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩ d := by
  have hh := (preparation_blank_tail M q hq a w L J).trans (Exec.single hd)
  have e : 2 * (w.length + 1) + 2 = 2 * w.length + 3 + 1 := by omega
  rw [e]
  exact hh

theorem checkpoint_stay (q : Q) (hq : q ≠ M.halt) (a : Γ)
    (hm : (M.transition q a).move = .stay) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, L,
        work (M.transition q a).write ::
          (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.stay q a) :: J⟩ := by
  apply checkpoint_length M q hq a w L J
  exact row_step M (.stay q a) ⟨hq, hm⟩
    ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩

theorem checkpoint_left (q : Q) (hq : q ≠ M.halt) (a c : Γ)
    (hm : (M.transition q a).move = .left) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, work c :: L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, L,
        work c :: work (M.transition q a).write ::
          (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.left q a c) :: J⟩ := by
  apply checkpoint_length M q hq a w (work c :: L) J
  exact row_step M (.left q a c) ⟨hq, hm⟩
    ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩

theorem checkpoint_right (q : Q) (hq : q ≠ M.halt) (a c : Γ)
    (hm : (M.transition q a).move = .right) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 2) + 2)
      ⟨ready q, L,
        work a :: work c :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, work (M.transition q a).write :: L,
        work c :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.right q a c) :: J⟩ := by
  have hh := checkpoint_length M q hq a (c :: w) L J _
    (row_step M (.right q a c) ⟨hq, hm⟩
      ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩)
  simpa [Nat.add_assoc, Row.instruction, Instruction.target, Stream'.appendStream'] using hh

theorem checkpoint_extend (q : Q) (hq : q ≠ M.halt) (a : Γ)
    (hm : (M.transition q a).move = .right) (L J : Stream' (Letter Q Γ)) :
    Exec M 4
      ⟨ready q, L, work a :: boundary :: Stream'.const (work M.blank), J⟩
      ⟨ready (M.transition q a).state, work (M.transition q a).write :: L,
        work M.blank :: boundary :: Stream'.const (work M.blank),
        record (.extend q a) :: J⟩ := by
  apply checkpoint_length M q hq a [] L J
  have hh := row_step M (.extend q a) ⟨hq, hm⟩
    ⟨L, Stream'.const (work M.blank), J⟩
  have hb : (work M.blank :: Stream'.const (work M.blank) : Stream' (Letter Q Γ)) =
      Stream'.const (work M.blank) := by
    ext n
    cases n <;> rfl
  simpa [Row.instruction, Instruction.source, Instruction.target,
    Stream'.appendStream', hb] using hh

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def word (r : ℝ) (digit : S → ℝ) : List S → ℝ
  | [] => 0
  | a :: w => r * (digit a + word r digit w)

def prefixPoint (r : ℝ) (digit : S → ℝ) (w : List S) (z : ℝ) : ℝ :=
  word r digit w + r ^ w.length * z

def interval (r : ℝ) (digit : S → ℝ) (w : List S) : Set ℝ :=
  Set.Icc (word r digit w) (word r digit w + r ^ w.length)

@[simp] theorem word_nil (r : ℝ) (digit : S → ℝ) : word r digit [] = 0 := rfl

@[simp] theorem prefix_nil (r : ℝ) (digit : S → ℝ) (z : ℝ) :
    prefixPoint r digit [] z = z := by simp [prefixPoint]

@[simp] theorem prefix_cons (r : ℝ) (digit : S → ℝ) (a : S)
    (w : List S) (z : ℝ) :
    prefixPoint r digit (a :: w) z = r * (digit a + prefixPoint r digit w z) := by
  simp only [prefixPoint, word, List.length_cons, pow_succ]
  ring

theorem word_append (r : ℝ) (digit : S → ℝ) (u v : List S) :
    word r digit (u ++ v) = word r digit u + r ^ u.length * word r digit v := by
  induction u with
  | nil => simp
  | cons a u ih =>
      simp only [List.cons_append, word, List.length_cons, pow_succ, ih]
      ring

theorem prefix_append (r : ℝ) (digit : S → ℝ) (u v : List S) (z : ℝ) :
    prefixPoint r digit (u ++ v) z = prefixPoint r digit u (prefixPoint r digit v z) := by
  simp only [prefixPoint, word_append, List.length_append, pow_add]
  ring

theorem prefix_mem_interval {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ interval r digit w := by
  have hpow := pow_nonneg hr w.length
  dsimp [prefixPoint, interval]
  constructor
  · linarith [mul_nonneg hpow hz.1]
  · nlinarith [hz.2]

theorem interval_eq_image {r : ℝ} (hr : 0 < r) (digit : S → ℝ) (w : List S) :
    interval r digit w = prefixPoint r digit w '' Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · intro hy
    have hp : 0 < r ^ w.length := pow_pos hr _
    refine ⟨(y - word r digit w) / r ^ w.length, ?_, ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr hy.1) hp.le
      · apply (div_le_one hp).mpr
        exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hy.2)
    · dsimp [prefixPoint]
      field_simp
      ring
  · rintro ⟨z, hz, rfl⟩
    exact prefix_mem_interval hr.le digit w hz

def replacement (r : ℝ) (digit : S → ℝ) (u v : List S) (x : ℝ) : ℝ :=
  word r digit v + (r ^ v.length / r ^ u.length) * (x - word r digit u)

theorem replacement_prefix {r : ℝ} (hr : r ≠ 0) (digit : S → ℝ)
    (u v : List S) (z : ℝ) :
    replacement r digit u v (prefixPoint r digit u z) = prefixPoint r digit v z := by
  dsimp [replacement, prefixPoint]
  field_simp
  ring

theorem replacement_interval {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (u v : List S) :
    replacement r digit u v '' interval r digit u = interval r digit v := by
  rw [interval_eq_image hr digit u, interval_eq_image hr digit v, Set.image_image]
  congr 1
  funext z
  exact replacement_prefix hr.ne' digit u v z

def scales (r : ℝ) (u v : Fin 3 → List S) : Fin 3 → ℝ :=
  fun i => r ^ (v i).length / r ^ (u i).length

theorem determinant_one {r : ℝ} (hr : r ≠ 0) (u v : Fin 3 → List S)
    (h : ∑ i, (u i).length = ∑ i, (v i).length) :
    Matrix.det (Matrix.diagonal (scales r u v)) = 1 := by
  rw [Matrix.det_diagonal]
  simp only [scales, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [h]
  exact div_self (pow_ne_zero _ hr)

theorem scales_positive {r : ℝ} (hr : 0 < r) (u v : Fin 3 → List S) (i : Fin 3) :
    0 < scales r u v i := div_pos (pow_pos hr _) (pow_pos hr _)

def stream {B : ℕ} (digit : S → Fin B) (s : Stream' S) : ℝ :=
  Real.ofDigits (fun n => digit (s n))

theorem stream_mem_unit {B : ℕ} (digit : S → Fin B) (s : Stream' S) :
    stream digit s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem stream_cons {B : ℕ} (digit : S → Fin B) (a : S) (s : Stream' S) :
    stream digit (a :: s) = (B : ℝ)⁻¹ * ((digit a : ℝ) + stream digit s) := by
  have hh := Real.ofDigits_eq_sum_add_ofDigits (fun n => digit ((a :: s) n)) 1
  simpa [stream, Real.ofDigitsTerm, Stream'.cons, mul_add, mul_comm] using hh

theorem stream_append {B : ℕ} (digit : S → Fin B) (w : List S) (s : Stream' S) :
    stream digit (w ++ₛ s) =
      prefixPoint (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w (stream digit s) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [Stream'.appendStream', stream_cons, ih, prefix_cons]

theorem stream_append_mem_interval {B : ℕ} (digit : S → Fin B)
    (w : List S) (s : Stream' S) :
    stream digit (w ++ₛ s) ∈ interval (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w := by
  rw [stream_append]
  exact prefix_mem_interval (inv_nonneg.mpr (Nat.cast_nonneg _)) _ _ (stream_mem_unit _ _)

theorem replacement_stream {B : ℕ} (hB : B ≠ 0) (digit : S → Fin B)
    (u v : List S) (s : Stream' S) :
    replacement (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) u v (stream digit (u ++ₛ s)) =
      stream digit (v ++ₛ s) := by
  rw [stream_append, stream_append]
  exact replacement_prefix (inv_ne_zero (Nat.cast_ne_zero.mpr hB)) _ _ _ _

theorem stream_mem_interior {B : ℕ} (hB : 0 < B) (digit : S → Fin B)
    (hlo : ∀ a, 0 < (digit a : ℝ)) (hhi : ∀ a, (digit a : ℝ) + 1 < B)
    (s : Stream' S) : stream digit s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hb : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hs : s = s.head :: s.tail := by
    funext n
    cases n <;> rfl
  rw [hs, stream_cons]
  have htail := stream_mem_unit digit s.tail
  constructor
  · exact mul_pos (inv_pos.mpr hb) (by linarith [hlo s.head, htail.1])
  · rw [mul_comm, ← div_eq_mul_inv]
    apply (div_lt_one hb).mpr
    linarith [hhi s.head, htail.2]

theorem prefix_mem_unit {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => simpa using hz
  | cons a w ih =>
      rw [prefix_cons]
      exact ⟨mul_nonneg hr (add_nonneg (hd₀ a) ih.1),
        (mul_le_mul_of_nonneg_left (show digit a + prefixPoint r digit w z ≤
          digit a + 1 by linarith [ih.2]) hr).trans (hd₁ a)⟩

theorem interval_subset_unit {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (w : List S) : interval r digit w ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [interval_eq_image hr]
  rintro _ ⟨z, hz, rfl⟩
  exact prefix_mem_unit hr.le digit hd₀ hd₁ w hz

theorem prefix_gap {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (p u v : List S) (a b : S) {x y : ℝ}
    (hx : x ∈ interval r digit (p ++ a :: u))
    (hy : y ∈ interval r digit (p ++ b :: v)) :
    r ^ (p.length + 1) * (digit b - digit a - 1) ≤ y - x := by
  rw [interval_eq_image hr] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hs' := prefix_mem_unit hr.le digit hd₀ hd₁ u hs
  have ht' := prefix_mem_unit hr.le digit hd₀ hd₁ v ht
  rw [prefix_append, prefix_append, prefix_cons, prefix_cons]
  dsimp [prefixPoint]
  have hn : 0 ≤ r ^ p.length * r := mul_nonneg (pow_nonneg hr.le _) hr.le
  have hh : 0 ≤ r ^ p.length * r *
      (prefixPoint r digit v t - prefixPoint r digit u s + 1) :=
    mul_nonneg hn (by linarith [hs'.2, ht'.1])
  dsimp [prefixPoint] at hh
  rw [pow_succ]
  nlinarith only [hh]

end BalancedTransport.Coding
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem disjoint_of_first_difference {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (p u v : List S) (a b : S) (hab : digit a + 1 < digit b) :
    Disjoint (interval r digit (p ++ a :: u)) (interval r digit (p ++ b :: v)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := prefix_gap hr digit hd₀ hd₁ p u v a b hx hy
  have hp : 0 < r ^ (p.length + 1) * (digit b - digit a - 1) :=
    mul_pos (pow_pos hr _) (by linarith)
  linarith

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
variable {Q Γ : Type*}

def sourcePrefixes (r : Instruction Q Γ) : Fin 3 → List (Letter Q Γ) :=
  ![r.sourceLeft, r.sourceRight, r.sourceHistory]

def targetPrefixes (r : Instruction Q Γ) : Fin 3 → List (Letter Q Γ) :=
  ![r.targetLeft, r.targetRight, r.targetHistory]

theorem balanced_determinant (inst : Instruction Q Γ) (h : inst.Balanced)
    {r : ℝ} (hr : r ≠ 0) :
    Matrix.det (Matrix.diagonal (Coding.scales r inst.sourcePrefixes inst.targetPrefixes)) = 1 := by
  apply Coding.determinant_one hr
  simpa [sourcePrefixes, targetPrefixes, Fin.sum_univ_succ, Instruction.Balanced,
    add_assoc] using h

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport

theorem Recorder.Row.determinant_one {Q Γ : Type*} (M : Recorder.Machine Q Γ)
    (row : Recorder.Row Q Γ) {r : ℝ} (hr : r ≠ 0) :
    Matrix.det (Matrix.diagonal (Coding.scales r
      (row.instruction M).sourcePrefixes (row.instruction M).targetPrefixes)) = 1 :=
  (row.instruction M).balanced_determinant (row.balanced M) hr

theorem residual_zero_pressure_solution (ν : ℝ) (U : Velocity)
    (hU : Smooth U) (hzero : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    ZeroDataSolution ν (affineForce (inertialCoefficient U) (viscousCoefficient U) ν)
      U (fun _ _ => 0) := by
  refine ⟨hU, contDiffOn_const, hzero, hdiv, ?_⟩
  intro t ht x
  have hp : gradient (fun _ _ => 0) t x = 0 := by
    ext i
    simp [gradient, spaceD]
  rw [hp]
  simp only [affineForce, inertialCoefficient, viscousCoefficient, smul_neg, neg_zero, zero_add]
  abel

end BalancedTransport
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

theorem first_difference {u v : List S} (hu : ¬ u.IsPrefix v) (hv : ¬ v.IsPrefix u) :
    ∃ p a b u' v', u = p ++ a :: u' ∧ v = p ++ b :: v' ∧ a ≠ b := by
  classical
  induction u generalizing v with
  | nil => exact False.elim (hu ⟨v, by simp⟩)
  | cons a u ih =>
      cases v with
      | nil => exact False.elim (hv ⟨a :: u, by simp⟩)
      | cons b v =>
          by_cases hab : a = b
          · subst b
            have hu' : ¬u.IsPrefix v := by
              rintro ⟨w, hw⟩
              exact hu ⟨w, by simpa using congrArg (List.cons a) hw⟩
            have hv' : ¬v.IsPrefix u := by
              rintro ⟨w, hw⟩
              exact hv ⟨w, by simpa using congrArg (List.cons a) hw⟩
            obtain ⟨p, b, c, u', v', hu'', hv'', hbc⟩ := ih hu' hv'
            exact ⟨a :: p, b, c, u', v', by simp [hu''], by simp [hv''], hbc⟩
          · exact ⟨[], a, b, u, v, rfl, rfl, hab⟩

theorem incompatible_intervals_disjoint {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    {u v : List S} (hu : ¬u.IsPrefix v) (hv : ¬v.IsPrefix u) :
    Disjoint (interval r digit u) (interval r digit v) := by
  obtain ⟨p, a, b, u', v', rfl, rfl, hab⟩ := first_difference hu hv
  rcases hgap a b hab with hab' | hba'
  · exact disjoint_of_first_difference hr digit hd₀ hd₁ p u' v' a b hab'
  · exact (disjoint_of_first_difference hr digit hd₀ hd₁ p v' u' b a hba').symm

theorem comparable_of_intersection {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    {u v : List S} {x : ℝ} (hu : x ∈ interval r digit u) (hv : x ∈ interval r digit v) :
    u.IsPrefix v ∨ v.IsPrefix u := by
  by_contra h
  push Not at h
  exact Set.disjoint_left.mp (incompatible_intervals_disjoint hr digit hd₀ hd₁ hgap h.1 h.2)
    hu hv

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem common_extensions (filler : S) {u v : List S}
    (h : u.IsPrefix v ∨ v.IsPrefix u) :
    ∃ s t : Stream' S, u ++ₛ s = v ++ₛ t := by
  rcases h with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact ⟨w ++ₛ Stream'.const filler, Stream'.const filler,
      (Stream'.append_append_stream _ _ _).symm⟩
  · exact ⟨Stream'.const filler, w ++ₛ Stream'.const filler,
      Stream'.append_append_stream _ _ _⟩

def oddDigit {n : ℕ} (a : Fin n) : Fin (2 * n + 1) :=
  ⟨2 * a.val + 1, by omega⟩

theorem oddDigit_pos {n : ℕ} (a : Fin n) : 0 < (oddDigit a : ℝ) := by
  dsimp [oddDigit]
  positivity

theorem oddDigit_upper {n : ℕ} (a : Fin n) :
    (oddDigit a : ℝ) + 1 < (2 * n + 1 : ℕ) := by
  have hh : (2 * a.val + 1) + 1 < 2 * n + 1 := by omega
  exact_mod_cast hh

theorem oddDigit_gap {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (oddDigit a : ℝ) + 1 < (oddDigit b : ℝ) ∨
      (oddDigit b : ℝ) + 1 < (oddDigit a : ℝ) := by
  have hv : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
  rcases lt_or_gt_of_ne hv with h | h
  · left
    have hh : (2 * a.val + 1) + 1 < 2 * b.val + 1 := by omega
    exact_mod_cast hh
  · right
    have hh : (2 * b.val + 1) + 1 < 2 * a.val + 1 := by omega
    exact_mod_cast hh

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def box (r : ℝ) (digit : S → ℝ) (o : Space) (u : Fin 3 → List S) : Set Space :=
  {x | ∀ i, x i - o i ∈ interval r digit (u i)}

def boxMap (r : ℝ) (digit : S → ℝ) (o o' : Space)
    (u v : Fin 3 → List S) (x : Space) : Space :=
  fun i => o' i + replacement r digit (u i) (v i) (x i - o i)

theorem boxMap_image {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (o o' : Space) (u v : Fin 3 → List S) :
    boxMap r digit o o' u v '' box r digit o u = box r digit o' v := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hi : replacement r digit (u i) (v i) (x i - o i) ∈ interval r digit (v i) := by
      rw [← replacement_interval hr digit (u i) (v i)]
      exact ⟨x i - o i, hx i, rfl⟩
    simpa only [boxMap, add_sub_cancel_left] using hi
  · intro hy
    have hex : ∀ i, ∃ z : ℝ, z ∈ interval r digit (u i) ∧
        replacement r digit (u i) (v i) z = y i - o' i := by
      intro i
      have hi := hy i
      rw [← replacement_interval hr digit (u i) (v i)] at hi
      exact hi
    choose z hz he using hex
    refine ⟨fun i => o i + z i, ?_, ?_⟩
    · intro i
      simpa only [add_sub_cancel_left] using hz i
    · funext i
      simp only [boxMap, add_sub_cancel_left, he]
      ring

theorem boxMap_sub (r : ℝ) (digit : S → ℝ) (o o' : Space)
    (u v : Fin 3 → List S) (x y : Space) (i : Fin 3) :
    boxMap r digit o o' u v x i - boxMap r digit o o' u v y i =
      scales r u v i * (x i - y i) := by
  dsimp [boxMap, replacement, scales]
  ring

def codedPoint {B : ℕ} (digit : S → Fin B) (o : Space) (s : Fin 3 → Stream' S) : Space :=
  fun i => o i + stream digit (s i)

theorem codedPoint_mem_box {B : ℕ} (digit : S → Fin B) (o : Space)
    (u : Fin 3 → List S) (s : Fin 3 → Stream' S) :
    codedPoint digit o (fun i => u i ++ₛ s i) ∈
      box (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) o u := by
  intro i
  simpa only [codedPoint, add_sub_cancel_left] using
    stream_append_mem_interval digit (u i) (s i)

theorem boxMap_codedPoint {B : ℕ} (hB : B ≠ 0) (digit : S → Fin B) (o o' : Space)
    (u v : Fin 3 → List S) (s : Fin 3 → Stream' S) :
    boxMap (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) o o' u v
      (codedPoint digit o (fun i => u i ++ₛ s i)) =
      codedPoint digit o' (fun i => v i ++ₛ s i) := by
  funext i
  simp only [boxMap, codedPoint, add_sub_cancel_left]
  rw [replacement_stream hB]

def origin (k : ℕ) : Space := ![4 * (k : ℝ), 0, 0]

theorem control_eq_of_box_intersection {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    {k l : ℕ} {u v : Fin 3 → List S} {x : Space}
    (hu : x ∈ box r digit (origin k) u) (hv : x ∈ box r digit (origin l) v) : k = l := by
  have hu' := interval_subset_unit hr digit hd₀ hd₁ (u 0) (hu 0)
  have hv' := interval_subset_unit hr digit hd₀ hd₁ (v 0) (hv 0)
  simp only [origin, Matrix.cons_val_zero, Set.mem_Icc] at hu' hv'
  rcases lt_trichotomy k l with h | h | h
  · have h' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast h
    linarith [hu'.2, hv'.1]
  · exact h
  · have h' : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
    linarith [hv'.2, hu'.1]

theorem box_compact (r : ℝ) (digit : S → ℝ) (o : Space) (u : Fin 3 → List S) :
    IsCompact (box r digit o u) := by
  have he : box r digit o u = Set.pi Set.univ
      (fun i => Set.Icc (o i + word r digit (u i))
        (o i + word r digit (u i) + r ^ (u i).length)) := by
    ext x
    simp only [box, Set.mem_ofPred_eq, Set.mem_univ_pi, interval, Set.mem_Icc]
    congr! 1 with i
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [he]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}

def placement [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) (s : Control Q) : ℕ :=
  if s = .ready M.halt then 0 else (Fintype.equivFin (Control Q) s).val + 1

@[simp] theorem placement_halt [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) :
    placement M (.ready M.halt) = 0 := by simp [placement]

theorem placement_positive [Fintype Q] [DecidableEq Q] (M : Machine Q Γ)
    (s : Control Q) (hs : s ≠ .ready M.halt) : 0 < placement M s := by simp [placement, hs]

theorem placement_injective [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) :
    Function.Injective (placement M) := by
  intro s t h
  by_cases hs : s = .ready M.halt <;> by_cases ht : t = .ready M.halt
  · exact hs.trans ht.symm
  · simp [placement, hs, ht] at h
  · simp [placement, hs, ht] at h
  · simp only [placement, hs, ht, ↓reduceIte, Nat.add_right_cancel_iff] at h
    exact (Fintype.equivFin (Control Q)).injective (Fin.ext h)

def Instruction.sourceBox (inst : Instruction Q Γ) (r : ℝ) (digit : Letter Q Γ → ℝ)
    (id : Control Q → ℕ) : Set Space :=
  Coding.box r digit (Coding.origin (id inst.sourceControl)) inst.sourcePrefixes

def Instruction.targetBox (inst : Instruction Q Γ) (r : ℝ) (digit : Letter Q Γ → ℝ)
    (id : Control Q → ℕ) : Set Space :=
  Coding.box r digit (Coding.origin (id inst.targetControl)) inst.targetPrefixes

theorem source_boxes_disjoint [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ)
    {r : ℝ} (hr : 0 < r) (digit : Letter Q Γ → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    (id : Control Q → ℕ) (hid : Function.Injective id)
    {a b : Row Q Γ} (ha : a.valid M) (hb : b.valid M) (hab : a ≠ b) :
    Disjoint ((a.instruction M).sourceBox r digit id)
      ((b.instruction M).sourceBox r digit id) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hcontrol : (a.instruction M).sourceControl = (b.instruction M).sourceControl :=
    hid (Coding.control_eq_of_box_intersection hr digit hd₀ hd₁ hx hy)
  have hi : ∀ i : Fin 3,
      ((a.instruction M).sourcePrefixes i).IsPrefix ((b.instruction M).sourcePrefixes i) ∨
      ((b.instruction M).sourcePrefixes i).IsPrefix ((a.instruction M).sourcePrefixes i) := by
    intro i
    apply Coding.comparable_of_intersection hr digit hd₀ hd₁ hgap (hx i)
    simpa only [Instruction.sourceBox, hcontrol] using hy i
  choose s t he using fun i => Coding.common_extensions (Letter.boundary : Letter Q Γ) (hi i)
  have heq : (a.instruction M).source ⟨s 0, s 1, s 2⟩ =
      (b.instruction M).source ⟨t 0, t 1, t 2⟩ := by
    dsimp [Instruction.source]
    congr 1
    · exact he 0
    · exact he 1
    · exact he 2
  exact hab (source_separation M ha hb heq).1

theorem target_boxes_disjoint (M : Machine Q Γ)
    {r : ℝ} (hr : 0 < r) (digit : Letter Q Γ → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    (id : Control Q → ℕ) (hid : Function.Injective id)
    {a b : Row Q Γ} (hab : a ≠ b) :
    Disjoint ((a.instruction M).targetBox r digit id)
      ((b.instruction M).targetBox r digit id) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hcontrol : (a.instruction M).targetControl = (b.instruction M).targetControl :=
    hid (Coding.control_eq_of_box_intersection hr digit hd₀ hd₁ hx hy)
  have hi : ∀ i : Fin 3,
      ((a.instruction M).targetPrefixes i).IsPrefix ((b.instruction M).targetPrefixes i) ∨
      ((b.instruction M).targetPrefixes i).IsPrefix ((a.instruction M).targetPrefixes i) := by
    intro i
    apply Coding.comparable_of_intersection hr digit hd₀ hd₁ hgap (hx i)
    simpa only [Instruction.targetBox, hcontrol] using hy i
  choose s t he using fun i => Coding.common_extensions (Letter.boundary : Letter Q Γ) (hi i)
  have heq : (a.instruction M).target ⟨s 0, s 1, s 2⟩ =
      (b.instruction M).target ⟨t 0, t 1, t 2⟩ := by
    dsimp [Instruction.target]
    congr 1
    · exact he 0
    · exact he 1
    · exact he 2
  exact hab (target_separation M heq).1

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

def base (Q Γ : Type*) [Fintype Q] [Fintype Γ] : ℕ :=
  2 * Fintype.card (Letter Q Γ) + 1

def digit (a : Letter Q Γ) : Fin (base Q Γ) :=
  Coding.oddDigit (Fintype.equivFin (Letter Q Γ) a)

theorem base_pos : 0 < base Q Γ := by simp [base]

theorem digit_pos (a : Letter Q Γ) : 0 < (digit a : ℝ) :=
  Coding.oddDigit_pos _

theorem digit_upper (a : Letter Q Γ) : (digit a : ℝ) + 1 < base Q Γ :=
  Coding.oddDigit_upper _

theorem digit_gap (a b : Letter Q Γ) (hab : a ≠ b) :
    (digit a : ℝ) + 1 < (digit b : ℝ) ∨ (digit b : ℝ) + 1 < (digit a : ℝ) :=
  Coding.oddDigit_gap _ _ (fun he => hab ((Fintype.equivFin _).injective he))

end BalancedTransport.Recorder
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def pd (i : Fin 3) (f : Space → F) (x : Space) : F :=
  fderiv ℝ f x (Pi.single i 1)

@[simp] theorem pd_const (i : Fin 3) (a : F) (x : Space) :
    pd i (fun _ => a) x = 0 := by simp [pd]

@[simp] theorem pd_coord (i j : Fin 3) (x : Space) :
    pd i (fun y : Space => y j) x = (Pi.single i (1 : ℝ) : Space) j := by
  rw [pd, (hasFDerivAt_apply j x).fderiv]
  rfl

@[simp] theorem pd_sub_const (i : Fin 3) (f : Space → F) (a : F) (x : Space) :
    pd i (fun y => f y - a) x = pd i f x := by
  simp only [pd, fderiv_sub_const]

theorem pd_add (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp only [pd, fderiv_fun_add hf hg, add_apply]

theorem pd_sub (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp only [pd, fderiv_fun_sub hf hg, sub_apply]

theorem pd_mul (i : Fin 3) {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = f x * pd i g x + g x * pd i f x := by
  simp only [pd, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]

theorem pd_apply (i j : Fin 3) {f : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => f y j) x = pd i f x j := by
  simp only [pd, fderiv_apply hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

theorem pd_contDiff (i : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem pd_comm (i j : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x
  have he (v : Space) : fderiv ℝ (fun y => fderiv ℝ f y v) x =
      (ContinuousLinearMap.apply ℝ F v) ∘L fderiv ℝ (fderiv ℝ f) x :=
    ((ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
  simp only [he, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact hf.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) _ _

def curl (A : Space → Space) (x : Space) : Space :=
  ![pd 1 (fun y => A y 2) x - pd 2 (fun y => A y 1) x,
    pd 2 (fun y => A y 0) x - pd 0 (fun y => A y 2) x,
    pd 0 (fun y => A y 1) x - pd 1 (fun y => A y 0) x]

def divergence (A : Space → Space) (x : Space) : ℝ :=
  ∑ i, pd i (fun y => A y i) x

theorem curl_contDiff {A : Space → Space} (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ (⊤ : ℕ∞) (curl A) := by
  have he := contDiff_pi.mp hA
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (pd_contDiff 1 (he 2)).sub (pd_contDiff 2 (he 1))
  · exact (pd_contDiff 2 (he 0)).sub (pd_contDiff 0 (he 2))
  · exact (pd_contDiff 0 (he 1)).sub (pd_contDiff 1 (he 0))

theorem divergence_curl {A : Space → Space} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (x : Space) :
    divergence (curl A) x = 0 := by
  have he := contDiff_pi.mp hA
  have hd (i j : Fin 3) : DifferentiableAt ℝ (pd i (fun y => A y j)) x :=
    (pd_contDiff i (he j)).differentiable (by simp) x
  simp only [divergence, Fin.sum_univ_succ, curl, Matrix.cons_val_zero,
    Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  change (pd 0 (fun y => pd 1 (fun z => A z 2) y - pd 2 (fun z => A z 1) y) x) +
    ((pd 1 (fun y => pd 2 (fun z => A z 0) y - pd 0 (fun z => A z 2) y) x) +
    (pd 2 (fun y => pd 0 (fun z => A z 1) y - pd 1 (fun z => A z 0) y) x)) = 0
  rw [pd_sub _ (hd 1 2) (hd 2 1), pd_sub _ (hd 2 0) (hd 0 2),
    pd_sub _ (hd 0 1) (hd 1 0)]
  rw [pd_comm 0 1 (he 2), pd_comm 0 2 (he 1), pd_comm 1 2 (he 0)]
  ring

theorem curl_congr {A B : Space → Space} {x : Space}
    (h : A =ᶠ[𝓝 x] B) : curl A x = curl B x := by
  have he (j : Fin 3) : (fun y => A y j) =ᶠ[𝓝 x] (fun y => B y j) :=
    h.mono (fun _ hh => congrFun hh j)
  simp only [curl, pd, (he 0).fderiv_eq, (he 1).fderiv_eq, (he 2).fderiv_eq]

@[simp] theorem curl_zero : curl (0 : Space → Space) = 0 := by
  funext x
  simp [curl]

theorem tsupport_curl_subset (A : Space → Space) :
    tsupport (curl A) ⊆ tsupport A := by
  apply closure_minimal _ (isClosed_tsupport A)
  intro x hx
  by_contra hxA
  have hh : A =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxA
  have hz := curl_congr hh
  exact hx (by simpa using hz)

theorem curl_hasCompactSupport {A : Space → Space} (hA : HasCompactSupport A) :
    HasCompactSupport (curl A) :=
  hA.of_isClosed_subset (isClosed_tsupport _) (tsupport_curl_subset A)

def affinePotential (c v l : Space) (x : Space) : Space :=
  ![(1 / 2 : ℝ) * (v 1 * (x 2 - c 2) - v 2 * (x 1 - c 1)) +
      (1 / 3 : ℝ) * (l 1 - l 2) * (x 1 - c 1) * (x 2 - c 2),
    (1 / 2 : ℝ) * (v 2 * (x 0 - c 0) - v 0 * (x 2 - c 2)) +
      (1 / 3 : ℝ) * (l 2 - l 0) * (x 2 - c 2) * (x 0 - c 0),
    (1 / 2 : ℝ) * (v 0 * (x 1 - c 1) - v 1 * (x 0 - c 0)) +
      (1 / 3 : ℝ) * (l 0 - l 1) * (x 0 - c 0) * (x 1 - c 1)]

theorem affinePotential_contDiff (c v l : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (affinePotential c v l) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [affinePotential] <;> fun_prop

theorem curl_affinePotential (c v l : Space) (hl : ∑ i, l i = 0) (x : Space) :
    curl (affinePotential c v l) x = fun i => v i + l i * (x i - c i) := by
  have hl' : l 0 + l 1 + l 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hl
  funext i
  fin_cases i <;>
    simp (disch := fun_prop) [curl, affinePotential, pd_add, pd_sub, pd_mul, Pi.single_apply] <;>
    nlinarith [mul_eq_zero_of_left hl' (x 0 - c 0),
      mul_eq_zero_of_left hl' (x 1 - c 1), mul_eq_zero_of_left hl' (x 2 - c 2)]

def boxCutoff (a b : Space) (η : ℝ) (x : Space) : ℝ :=
  ∏ i : Fin 3, Real.smoothTransition ((x i - a i + 2 * η) / η) *
    Real.smoothTransition ((b i + 2 * η - x i) / η)

def openEnlargement (a b : Space) (η : ℝ) : Set Space :=
  Set.pi Set.univ (fun i => Set.Ioo (a i - η) (b i + η))

def closedEnlargement (a b : Space) (η : ℝ) : Set Space :=
  Set.Icc (fun i => a i - η) (fun i => b i + η)

@[simp] theorem mem_openEnlargement (a b : Space) (η : ℝ) (x : Space) :
    x ∈ openEnlargement a b η ↔ ∀ i, a i - η < x i ∧ x i < b i + η := by
  simp [openEnlargement]

@[simp] theorem mem_closedEnlargement (a b : Space) (η : ℝ) (x : Space) :
    x ∈ closedEnlargement a b η ↔ ∀ i, a i - η ≤ x i ∧ x i ≤ b i + η := by
  simp only [closedEnlargement, mem_Icc, Pi.le_def, forall_and]

theorem openEnlargement_isOpen (a b : Space) (η : ℝ) :
    IsOpen (openEnlargement a b η) := by
  exact isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem closedEnlargement_isCompact (a b : Space) (η : ℝ) :
    IsCompact (closedEnlargement a b η) := isCompact_Icc

theorem boxCutoff_contDiff (a b : Space) (η : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (boxCutoff a b η) := by
  unfold boxCutoff
  fun_prop

theorem boxCutoff_eq_one {a b : Space} {η : ℝ} (hη : 0 < η) {x : Space}
    (hx : x ∈ closedEnlargement a b η) : boxCutoff a b η x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  obtain ⟨hl, hr⟩ := (mem_closedEnlargement _ _ _ _).mp hx i
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)), one_mul]

theorem boxCutoff_eventually_one {a b : Space} {η : ℝ} (hη : 0 < η)
    {x : Space} (hx : x ∈ openEnlargement a b η) :
    boxCutoff a b η =ᶠ[𝓝 x] 1 := by
  filter_upwards [(openEnlargement_isOpen a b η).mem_nhds hx] with y hy
  apply boxCutoff_eq_one hη
  exact (mem_closedEnlargement _ _ _ _).mpr fun i =>
    ⟨((mem_openEnlargement _ _ _ _).mp hy i).1.le,
      ((mem_openEnlargement _ _ _ _).mp hy i).2.le⟩

theorem boxCutoff_eq_zero {a b : Space} {η : ℝ} (hη : 0 < η) {x : Space}
    (hx : x ∉ closedEnlargement a b (2 * η)) : boxCutoff a b η x = 0 := by
  rw [mem_closedEnlargement] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hl : a i - 2 * η ≤ x i
  · have he : Real.smoothTransition ((b i + 2 * η - x i) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith [hi hl]) hη.le)
    rw [he, mul_zero]
  · have he : Real.smoothTransition ((x i - a i + 2 * η) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith) hη.le)
    rw [he, zero_mul]

theorem tsupport_boxCutoff_subset (a b : Space) {η : ℝ} (hη : 0 < η) :
    tsupport (boxCutoff a b η) ⊆ closedEnlargement a b (2 * η) := by
  apply closure_minimal _ (closedEnlargement_isCompact _ _ _).isClosed
  intro x hx
  by_contra hn
  exact hx (boxCutoff_eq_zero hη hn)

theorem boxCutoff_hasCompactSupport (a b : Space) {η : ℝ} (hη : 0 < η) :
    HasCompactSupport (boxCutoff a b η) :=
  (closedEnlargement_isCompact _ _ _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_boxCutoff_subset a b hη)

def localizedAffine (a b c v l : Space) (η : ℝ) : Space → Space :=
  curl (fun x => boxCutoff a b η x • affinePotential c v l x)

theorem localizedAffine_contDiff (a b c v l : Space) (η : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (localizedAffine a b c v l η) :=
  curl_contDiff ((boxCutoff_contDiff a b η).smul (affinePotential_contDiff c v l))

theorem localizedAffine_divergence (a b c v l : Space) (η : ℝ) (x : Space) :
    divergence (localizedAffine a b c v l η) x = 0 :=
  divergence_curl ((boxCutoff_contDiff a b η).smul (affinePotential_contDiff c v l)) x

theorem localizedAffine_eq {a b c v l : Space} {η : ℝ} (hη : 0 < η)
    (hl : ∑ i, l i = 0) {x : Space} (hx : x ∈ openEnlargement a b η) :
    localizedAffine a b c v l η x = fun i => v i + l i * (x i - c i) := by
  unfold localizedAffine
  rw [curl_congr (show (fun y => boxCutoff a b η y • affinePotential c v l y) =ᶠ[𝓝 x]
      affinePotential c v l from (boxCutoff_eventually_one hη hx).mono
        (fun y hy => by simp only [hy, Pi.one_apply, one_smul])), curl_affinePotential c v l hl]

theorem tsupport_localizedAffine_subset (a b c v l : Space) {η : ℝ} (hη : 0 < η) :
    tsupport (localizedAffine a b c v l η) ⊆ closedEnlargement a b (2 * η) := by
  refine (tsupport_curl_subset _).trans ?_
  apply closure_minimal _ (closedEnlargement_isCompact _ _ _).isClosed
  intro x hx
  by_contra hn
  exact hx (by simp [boxCutoff_eq_zero hη hn])

theorem localizedAffine_hasCompactSupport (a b c v l : Space) {η : ℝ} (hη : 0 < η) :
    HasCompactSupport (localizedAffine a b c v l η) :=
  (closedEnlargement_isCompact _ _ _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_localizedAffine_subset a b c v l hη)

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def JointSmooth (f : Field F) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)

theorem JointSmooth.slice {f : Field F} (hf : JointSmooth f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (f t) := hf.comp (contDiff_const.prodMk contDiff_id)

theorem JointSmooth.spaceD {f : Field F} (hf : JointSmooth f) (i : Fin 3) :
    JointSmooth (spaceD i f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × Space => f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem JointSmooth.curl {A : Velocity} (hA : JointSmooth A) :
    JointSmooth (fun t => curl (A t)) := by
  have he (i : Fin 3) : JointSmooth (fun t x => A t x i) := contDiff_pi.mp hA i
  have hd (i j : Fin 3) := (he j).spaceD i
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (hd 1 2).sub (hd 2 1)
  · exact (hd 2 0).sub (hd 0 2)
  · exact (hd 0 1).sub (hd 1 0)

theorem divergence_eq_div {A : Velocity} (hA : JointSmooth A) (t : ℝ) (x : Space) :
    divergence (A t) x = div A t x := by
  apply Finset.sum_congr rfl
  intro i _
  exact pd_apply i i ((hA.slice t).differentiable (by simp) x)

theorem JointSmooth.solenoidal_curl {A : Velocity} (hA : JointSmooth A)
    (t : ℝ) (x : Space) : div (fun s => Geometry.curl (A s)) t x = 0 := by
  rw [← divergence_eq_div hA.curl]
  exact divergence_curl (hA.slice t) x

def fullTimeD (f : Field F) : Field F := fun t x => deriv (fun s => f s x) t

theorem JointSmooth.fullTimeD {f : Field F} (hf : JointSmooth f) :
    JointSmooth (fullTimeD f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × ℝ => f z.2 z.1.2) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact ContDiff.fderiv_apply (f := fun z : ℝ × Space => fun s => f s z.2)
    hh contDiff_fst contDiff_const (by simp)

def lowerEndpoint (a : Space) (c d : ℝ → Space) (t : ℝ) : Space :=
  fun i => c t i + d t i * a i

def logarithmicRate (d : ℝ → Space) (t : ℝ) : Space :=
  fun i => deriv (fun s => d s i) t / d t i

def movingBoxVelocity (a b : Space) (c d : ℝ → Space) (η : ℝ) : Velocity :=
  fun t => localizedAffine (lowerEndpoint a c d t) (lowerEndpoint b c d t)
    (c t) (deriv c t) (logarithmicRate d t) η

lemma logarithmicRate_trace_zero {d : ℝ → Space} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (hdet : ∀ t, ∏ i, d t i = 1) (t : ℝ) :
    ∑ i, logarithmicRate d t i = 0 := by
  have dh (i : Fin 3) := ((contDiff_pi.mp hd i).differentiable (by simp) t).hasDerivAt
  have hconst : (fun s => d s 0 * d s 1 * d s 2) = fun _ => (1 : ℝ) := by
    funext s
    simpa [Fin.prod_univ_succ, mul_assoc] using hdet s
  have hh := ((dh 0).fun_mul (dh 1)).fun_mul (dh 2)
  rw [hconst] at hh
  have hz := hh.unique (hasDerivAt_const t (1 : ℝ))
  simp only [logarithmicRate, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change deriv (fun s => d s 0) t / d t 0 +
    (deriv (fun s => d s 1) t / d t 1 + deriv (fun s => d s 2) t / d t 2) = 0
  field_simp [hn t 0, hn t 1, hn t 2]
  nlinarith

lemma logarithmicRate_contDiff {d : ℝ → Space} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (logarithmicRate d) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_infty_iff_deriv.mp (contDiff_pi.mp hd i)).2.div
    (contDiff_pi.mp hd i) (fun t => hn t i)

theorem movingBoxVelocity_jointSmooth {c d : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (a b : Space) (η : ℝ) :
    JointSmooth (movingBoxVelocity a b c d η) := by
  apply JointSmooth.curl
  have hcd := (contDiff_infty_iff_deriv.mp hc).2
  have hl := logarithmicRate_contDiff hd hn
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space =>
    boxCutoff (lowerEndpoint a c d z.1) (lowerEndpoint b c d z.1) η z.2 •
      affinePotential (c z.1) (deriv c z.1) (logarithmicRate d z.1) z.2)
  refine ContDiff.smul (f := fun z : ℝ × Space =>
    boxCutoff (lowerEndpoint a c d z.1) (lowerEndpoint b c d z.1) η z.2)
    (g := fun z : ℝ × Space =>
      affinePotential (c z.1) (deriv c z.1) (logarithmicRate d z.1) z.2) ?_ ?_
  · unfold boxCutoff lowerEndpoint
    fun_prop
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [affinePotential] <;> fun_prop

theorem movingBoxVelocity_divergence {c d : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (a b : Space) (η t : ℝ) (x : Space) :
    div (movingBoxVelocity a b c d η) t x = 0 := by
  rw [← divergence_eq_div (movingBoxVelocity_jointSmooth hc hd hn a b η)]
  exact localizedAffine_divergence _ _ _ _ _ _ _

def affinePath (c d : ℝ → Space) (z : Space) (t : ℝ) : Space :=
  fun i => c t i + d t i * z i

lemma affinePath_mem_plateau {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) {z : Space} (hz : z ∈ Set.Icc a b) {t : ℝ}
    (hd : ∀ i, 0 < d t i) :
    affinePath c d z t ∈ openEnlargement (lowerEndpoint a c d t)
      (lowerEndpoint b c d t) η := by
  rw [mem_openEnlargement]
  intro i
  have hz₁ := hz.1 i
  have hz₂ := hz.2 i
  dsimp [lowerEndpoint, affinePath]
  constructor <;> nlinarith [hd i]

theorem affinePath_hasDerivAt_of_mem_plateau {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (t : ℝ)
    (hx : affinePath c d z t ∈ openEnlargement
      (lowerEndpoint a c d t) (lowerEndpoint b c d t) η) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t := by
  have hn (s : ℝ) (i : Fin 3) := (hp s i).ne'
  rw [movingBoxVelocity, localizedAffine_eq hη (logarithmicRate_trace_zero hd hn hdet t)
    hx]
  apply hasDerivAt_pi.mpr
  intro i
  have hci := (hasDerivAt_pi.mp ((hc.differentiable (by simp) t).hasDerivAt) i)
  have hdi := ((contDiff_pi.mp hd i).differentiable (by simp) t).hasDerivAt
  have he : deriv c t i + logarithmicRate d t i * (affinePath c d z t i - c t i) =
      deriv c t i + deriv (fun s => d s i) t * z i := by
    dsimp [logarithmicRate, affinePath]
    field_simp [hn t i]
    ring
  rw [he]
  exact hci.fun_add (hdi.mul_const (z i))

theorem affinePath_hasDerivAt {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (hz : z ∈ Set.Icc a b) (t : ℝ) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t :=
  affinePath_hasDerivAt_of_mem_plateau hη hc hd hp hdet t
    (affinePath_mem_plateau hη hz (hp t))

lemma affinePath_mem_plateau_of_scaled_bound {a b : Space} {c d : ℝ → Space}
    {η δ : ℝ} {z : Space} (hz : z ∈ openEnlargement a b δ) {t : ℝ}
    (hp : ∀ i, 0 < d t i) (hscale : ∀ i, d t i * δ ≤ η) :
    affinePath c d z t ∈ openEnlargement (lowerEndpoint a c d t)
      (lowerEndpoint b c d t) η := by
  rw [mem_openEnlargement] at hz ⊢
  intro i
  have hlo := mul_lt_mul_of_pos_left (hz i).1 (hp i)
  have hhi := mul_lt_mul_of_pos_left (hz i).2 (hp i)
  dsimp [affinePath, lowerEndpoint]
  constructor <;> nlinarith [hscale i]

theorem affinePath_neighborhood {a b : Space} {c d : ℝ → Space} {η δ : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (hz : z ∈ openEnlargement a b δ) (t : ℝ)
    (hscale : ∀ i, d t i * δ ≤ η) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t :=
  affinePath_hasDerivAt_of_mem_plateau hη hc hd hp hdet t
    (affinePath_mem_plateau_of_scaled_bound hz (hp t) hscale)

@[simp] lemma affinePotential_zero (c : Space) : affinePotential c 0 0 = 0 := by
  ext x i
  fin_cases i <;> simp [affinePotential]

@[simp] lemma localizedAffine_zero (a b c : Space) (η : ℝ) :
    localizedAffine a b c 0 0 η = 0 := by
  unfold localizedAffine
  have he : (fun x => boxCutoff a b η x • affinePotential c 0 0 x) = 0 := by
    ext x i
    fin_cases i <;> simp [affinePotential]
  rw [he]
  exact curl_zero

theorem movingBoxVelocity_zero {a b : Space} {c d : ℝ → Space} {η t : ℝ}
    (hc : deriv c t = 0) (hd : ∀ i, deriv (fun s => d s i) t = 0) :
    movingBoxVelocity a b c d η t = 0 := by
  have hl : logarithmicRate d t = 0 := by ext i; simp [logarithmicRate, hd]
  simp [movingBoxVelocity, hc, hl]

lemma tsupport_movingBoxVelocity_subset (a b : Space) (c d : ℝ → Space) {η : ℝ}
    (hη : 0 < η) (t : ℝ) :
    tsupport (movingBoxVelocity a b c d η t) ⊆
      closedEnlargement (lowerEndpoint a c d t) (lowerEndpoint b c d t) (2 * η) :=
  tsupport_localizedAffine_subset _ _ _ _ _ hη

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def fullMixedD : MultiIndex → Field F → Field F
  | [], v => v
  | none :: a, v => fullTimeD (fullMixedD a v)
  | some i :: a, v => spaceD i (fullMixedD a v)

lemma JointSmooth.fullMixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex) :
    JointSmooth (fullMixedD a v) := by
  induction a with
  | nil => exact hv
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD i

lemma JointSmooth.timeSlice {v : Field F} (hv : JointSmooth v) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => v t x) := hv.comp (contDiff_id.prodMk contDiff_const)

lemma fullMixedD_eq_mixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) : fullMixedD a v t x = mixedD a v t x := by
  induction a generalizing t x with
  | nil => rfl
  | cons i a ha =>
    cases i with
    | none =>
      change deriv (fun s => fullMixedD a v s x) t =
        derivWithin (fun s => mixedD a v s x) (Ici 0) t
      rw [← derivWithin_congr (s := Ici (0 : ℝ)) (fun s hs => ha s hs x) (ha t ht x)]
      exact (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t).derivWithin
        (uniqueDiffOn_Ici 0 t ht) |>.symm
    | some i =>
      change fderiv ℝ (fullMixedD a v t) x _ = fderiv ℝ (mixedD a v t) x _
      rw [show fullMixedD a v t = mixedD a v t from funext (ha t ht)]

def SpatiallySupported (K : Set Space) (v : Field F) : Prop :=
  ∀ t x, x ∉ K → v t x = 0

lemma SpatiallySupported.fullTimeD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) : SpatiallySupported K (fullTimeD v) := by
  intro t x hx
  have he : (fun s => v s x) = fun _ => (0 : F) := funext (fun s => h s x hx)
  change deriv (fun s => v s x) t = 0
  rw [he]
  exact deriv_const t (0 : F)

lemma SpatiallySupported.spaceD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (i : Fin 3) :
    SpatiallySupported K (spaceD i v) := by
  intro t x hx
  have he : v t =ᶠ[𝓝 x] 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact h t y hy
  change fderiv ℝ (v t) x (Pi.single i 1) = 0
  rw [he.fderiv_eq]
  simp

lemma SpatiallySupported.fullMixedD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (a : MultiIndex) :
    SpatiallySupported K (fullMixedD a v) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD hK i

def RepeatsAfter (T : ℝ) (v : Field F) : Prop :=
  ∀ t, T ≤ t → v (t + 1) = v t

lemma RepeatsAfter.spaceD {T : ℝ} {v : Field F} (h : RepeatsAfter T v) (i : Fin 3) :
    RepeatsAfter T (spaceD i v) := by
  intro t ht
  funext x
  change fderiv ℝ (v (t + 1)) x (Pi.single i 1) = fderiv ℝ (v t) x (Pi.single i 1)
  rw [h t ht]

lemma RepeatsAfter.fullTimeD {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    (hv : JointSmooth v) : RepeatsAfter T (fullTimeD v) := by
  intro t ht
  funext x
  have hh := (hv.timeSlice x).differentiable (by simp)
  have hs : DifferentiableAt ℝ (fun s => v (s + 1) x) t :=
    (hh (t + 1)).comp t (differentiableAt_id.add_const 1)
  have he : EqOn (fun s => v (s + 1) x) (fun s => v s x) (Ici T) :=
    fun s hs => congrFun (h s hs) x
  change deriv (fun s => v s x) (t + 1) = deriv (fun s => v s x) t
  rw [← deriv_comp_add_const (fun s => v s x) 1 t,
    ← hs.derivWithin (uniqueDiffOn_Ici T t ht),
    derivWithin_congr he (he ht),
    (hh t).derivWithin (uniqueDiffOn_Ici T t ht)]

lemma RepeatsAfter.fullMixedD {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    (hv : JointSmooth v) (a : MultiIndex) : RepeatsAfter T (fullMixedD a v) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD (hv.fullMixedD a)
      | some i => exact ha.spaceD i

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma RepeatsAfter.add_nat {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    {t : ℝ} (ht : T ≤ t) (n : ℕ) : v (t + n) = v t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, h _ (by linarith [Nat.cast_nonneg (α := ℝ) n]), ih]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma RepeatsAfter.reduce {v : Field F} (h : RepeatsAfter 1 v) {t : ℝ} (ht : 0 ≤ t) :
    ∃ s ∈ Icc (0 : ℝ) 2, v t = v s := by
  by_cases ht' : t ≤ 2
  · exact ⟨t, ⟨ht, ht'⟩, rfl⟩
  · have htn : 0 ≤ t - 1 := by linarith
    let n := ⌊t - 1⌋₊
    have hle : (n : ℝ) ≤ t - 1 := Nat.floor_le htn
    have hlt : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - 1)
    refine ⟨t - n, ⟨by linarith, by linarith⟩, ?_⟩
    have he := h.add_nat (t := t - n) (by linarith) n
    simpa using he

theorem boundedMixed_of_compact_repeating {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v)
    (hp : RepeatsAfter 1 v) : BoundedMixed v := by
  intro a
  have ha := hv.fullMixedD a
  have hsa := hs.fullMixedD hK.isClosed a
  have hpa := hp.fullMixedD hv a
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    ha.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  rw [← fullMixedD_eq_mixedD hv a t ht x]
  obtain ⟨s, hs, he⟩ := hpa.reduce ht
  rw [congrFun he x]
  by_cases hx : x ∈ K
  · exact (hC (s, x) ⟨hs,hx⟩).trans (le_max_left _ _)
  · rw [hsa s x hx, norm_zero]
    exact le_max_right _ _

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

lemma JointSmooth.sum {v : ι → Field F} (hv : ∀ i, JointSmooth (v i)) :
    JointSmooth (fun t x => ∑ i, v i t x) := by
  exact ContDiff.sum (fun i _ => hv i)

lemma div_sum {v : ι → Velocity} (hv : ∀ i, JointSmooth (v i)) (t : ℝ) (x : Space) :
    div (fun t x => ∑ i, v i t x) t x = ∑ i, div (v i) t x := by
  have hd (i : ι) := ((hv i).slice t).differentiable (by simp) x
  simp only [div, spaceD, fderiv_fun_sum (fun i _ => hd i), sum_apply,
    Finset.sum_apply]
  exact Finset.sum_comm

def familyVelocity (a b : ι → Space) (c d : ι → ℝ → Space) (η : ℝ) : Velocity :=
  fun t x => ∑ i, movingBoxVelocity (a i) (b i) (c i) (d i) η t x

lemma familyVelocity_jointSmooth {c d : ι → ℝ → Space}
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hn : ∀ i t j, d i t j ≠ 0) (a b : ι → Space) (η : ℝ) :
    JointSmooth (familyVelocity a b c d η) :=
  JointSmooth.sum (fun i => movingBoxVelocity_jointSmooth (hc i) (hd i) (hn i) (a i) (b i) η)

lemma familyVelocity_divergence {c d : ι → ℝ → Space}
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hn : ∀ i t j, d i t j ≠ 0) (a b : ι → Space) (η t : ℝ) (x : Space) :
    div (familyVelocity a b c d η) t x = 0 := by
  change div (fun t x => ∑ i, movingBoxVelocity (a i) (b i) (c i) (d i) η t x) t x = 0
  rw [div_sum
    (fun i => movingBoxVelocity_jointSmooth (hc i) (hd i) (hn i) (a i) (b i) η)]
  exact Finset.sum_eq_zero (fun i _ =>
    movingBoxVelocity_divergence (hc i) (hd i) (hn i) (a i) (b i) η t x)

lemma tsupport_familyVelocity_subset (a b : ι → Space) (c d : ι → ℝ → Space)
    {η : ℝ} (hη : 0 < η) (t : ℝ) :
    tsupport (familyVelocity a b c d η t) ⊆
      ⋃ i, closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun _ => isCompact_Icc.isClosed))
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  apply image_eq_zero_of_notMem_tsupport
  intro hi
  exact hn (mem_iUnion.mpr ⟨i,
    tsupport_movingBoxVelocity_subset (a i) (b i) (c i) (d i) hη t hi⟩)

lemma openEnlargement_subset_closedEnlargement {a b : Space} {η δ : ℝ}
    (h : η ≤ δ) : openEnlargement a b η ⊆ closedEnlargement a b δ := by
  intro x hx
  rw [mem_openEnlargement] at hx
  rw [mem_closedEnlargement]
  intro i
  constructor <;> linarith [(hx i).1, (hx i).2]

lemma familyVelocity_eq_on_plateau {a b : ι → Space} {c d : ι → ℝ → Space}
    {η t : ℝ} (hη : 0 < η) (i : ι) {x : Space}
    (hx : x ∈ openEnlargement (lowerEndpoint (a i) (c i) (d i) t)
      (lowerEndpoint (b i) (c i) (d i) t) η)
    (hsep : Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (a j) (c j) (d j) t)
        (lowerEndpoint (b j) (c j) (d j) t) (2 * η))) :
    familyVelocity a b c d η t x = movingBoxVelocity (a i) (b i) (c i) (d i) η t x := by
  apply Finset.sum_eq_single i
  · intro j _ hji
    apply image_eq_zero_of_notMem_tsupport
    intro hxj
    exact Set.disjoint_left.mp (hsep (Ne.symm hji))
      (openEnlargement_subset_closedEnlargement (by linarith) hx)
      (tsupport_movingBoxVelocity_subset (a j) (b j) (c j) (d j) hη t hxj)
  · simp

theorem familyVelocity_affinePath {a b : ι → Space} {c d : ι → ℝ → Space}
    {η δ : ℝ} (hη : 0 < η)
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hp : ∀ i t j, 0 < d i t j) (hdet : ∀ i t, ∏ j, d i t j = 1)
    (i : ι) {z : Space} (hz : z ∈ openEnlargement (a i) (b i) δ) (t : ℝ)
    (hscale : ∀ j, d i t j * δ ≤ η)
    (hsep : Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (a j) (c j) (d j) t)
        (lowerEndpoint (b j) (c j) (d j) t) (2 * η))) :
    HasDerivAt (affinePath (c i) (d i) z)
      (familyVelocity a b c d η t (affinePath (c i) (d i) z t)) t := by
  rw [familyVelocity_eq_on_plateau hη i
    (affinePath_mem_plateau_of_scaled_bound hz (hp i t) hscale) hsep]
  exact affinePath_neighborhood hη (hc i) (hd i) (hp i) (hdet i) hz t hscale

lemma familyVelocity_zero {a b : ι → Space} {c d : ι → ℝ → Space} {η t : ℝ}
    (hc : ∀ i, deriv (c i) t = 0) (hd : ∀ i j, deriv (fun s => d i s j) t = 0) :
    familyVelocity a b c d η t = 0 := by
  ext x j
  simp [familyVelocity, movingBoxVelocity_zero (hc _) (hd _)]

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def ForwardEq (v w : Field F) : Prop := ∀ t, 0 ≤ t → v t = w t

lemma ForwardEq.mixedD {v w : Field F} (h : ForwardEq v w) (a : MultiIndex) :
    ForwardEq (BalancedTransport.mixedD a v) (BalancedTransport.mixedD a w) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
    intro t ht
    funext x
    cases i with
    | none =>
      change derivWithin (fun s => BalancedTransport.mixedD a v s x) (Ici 0) t =
        derivWithin (fun s => BalancedTransport.mixedD a w s x) (Ici 0) t
      exact derivWithin_congr (s := Ici (0 : ℝ))
        (fun s hs => congrFun (ha s hs) x) (congrFun (ha t ht) x)
    | some i =>
      change fderiv ℝ (BalancedTransport.mixedD a v t) x _ = fderiv ℝ (BalancedTransport.mixedD a w t) x _
      rw [ha t ht]

lemma ForwardEq.smooth {v w : Field F} (h : ForwardEq v w) (hv : Smooth v) : Smooth w := by
  apply hv.congr
  intro z hz
  exact congrFun (h z.1 hz.1).symm z.2

lemma JointSmooth.smooth {v : Field F} (hv : JointSmooth v) : Smooth v := hv.contDiffOn

lemma ForwardEq.boundedMixed {v w : Field F} (h : ForwardEq v w)
    (hv : BoundedMixed v) : BoundedMixed w := by
  intro a
  obtain ⟨C, hC, hbound⟩ := hv a
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [← (h.mixedD a) t ht]
  exact hbound t ht x

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma ForwardEq.repeatsAfter {v w : Field F} (h : ForwardEq v w)
    (hp : RepeatsAfter 1 v) : RepeatsAfter 1 w := by
  intro t ht
  rw [← h t (by linarith), ← h (t+1) (by linarith)]
  exact hp t ht

lemma JointSmooth.laplacian {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (BalancedTransport.laplacian v) := JointSmooth.sum (fun i => (hv.spaceD i).spaceD i)

lemma JointSmooth.convection {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (BalancedTransport.convection v) := by
  apply JointSmooth.sum
  intro i
  exact (contDiff_pi.mp hv i).smul (hv.spaceD i)

def fullInertial (v : Velocity) : Velocity := fun t x => BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x

lemma JointSmooth.fullInertial {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (fullInertial v) := hv.fullTimeD.add hv.convection

lemma JointSmooth.viscousCoefficient {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (viscousCoefficient v) := hv.laplacian.neg

lemma fullInertial_forwardEq {v : Velocity} (hv : JointSmooth v) :
    ForwardEq (fullInertial v) (inertialCoefficient v) := by
  intro t ht
  funext x
  change BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x = timeD v t x + BalancedTransport.convection v t x
  rw [show BalancedTransport.Geometry.fullTimeD v t x = timeD v t x from fullMixedD_eq_mixedD hv [none] t ht x]

lemma SpatiallySupported.laplacian {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) (hK : IsClosed K) : SpatiallySupported K (BalancedTransport.laplacian v) := by
  intro t x hx
  exact Finset.sum_eq_zero (fun i _ => ((h.spaceD hK i).spaceD hK i) t x hx)

lemma SpatiallySupported.convection {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) : SpatiallySupported K (BalancedTransport.convection v) := by
  intro t x hx
  change ∑ i, (v t x i) • BalancedTransport.spaceD i v t x = 0
  simp [h t x hx]

lemma SpatiallySupported.fullInertial {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) : SpatiallySupported K (fullInertial v) := by
  intro t x hx
  change BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x = 0
  rw [h.fullTimeD t x hx, h.convection t x hx, add_zero]

lemma SpatiallySupported.viscousCoefficient {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) (hK : IsClosed K) :
    SpatiallySupported K (viscousCoefficient v) := by
  intro t x hx
  change -BalancedTransport.laplacian v t x = 0
  rw [h.laplacian hK t x hx, neg_zero]

lemma RepeatsAfter.laplacian {T : ℝ} {v : Velocity} (h : RepeatsAfter T v) :
    RepeatsAfter T (BalancedTransport.laplacian v) := by
  intro t ht
  funext x
  change (∑ i, BalancedTransport.spaceD i (BalancedTransport.spaceD i v) (t + 1) x) = ∑ i, BalancedTransport.spaceD i (BalancedTransport.spaceD i v) t x
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (((h.spaceD i).spaceD i) t ht) x

lemma RepeatsAfter.convection {T : ℝ} {v : Velocity} (h : RepeatsAfter T v) :
    RepeatsAfter T (BalancedTransport.convection v) := by
  intro t ht
  funext x
  change (∑ i, v (t + 1) x i • BalancedTransport.spaceD i v (t + 1) x) = ∑ i, v t x i • BalancedTransport.spaceD i v t x
  simp only [h t ht, (h.spaceD _) t ht]

lemma RepeatsAfter.fullInertial {T : ℝ} {v : Velocity} (h : RepeatsAfter T v)
    (hv : JointSmooth v) : RepeatsAfter T (fullInertial v) := by
  intro t ht
  funext x
  change BalancedTransport.Geometry.fullTimeD v (t+1) x + BalancedTransport.convection v (t+1) x = BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x
  rw [h.fullTimeD hv t ht, h.convection t ht]

lemma RepeatsAfter.viscousCoefficient {T : ℝ} {v : Velocity} (h : RepeatsAfter T v) :
    RepeatsAfter T (viscousCoefficient v) := by
  intro t ht
  funext x
  change -BalancedTransport.laplacian v (t+1) x = -BalancedTransport.laplacian v t x
  rw [h.laplacian t ht]

theorem prescribed_residual_regularity {K : Set Space} (hK : IsCompact K) {U : Velocity}
    (hU : JointSmooth U) (hs : SpatiallySupported K U) (hp : RepeatsAfter 1 U)
    (hzero : ∀ x, U 0 x = 0) (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    Smooth (inertialCoefficient U) ∧ Smooth (viscousCoefficient U) ∧
    CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ BoundedMixed (inertialCoefficient U) ∧ BoundedMixed (viscousCoefficient U) ∧
    PeriodicAfterOne U ∧
    ∀ ν : ℝ, let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f := by
  have hf₀ := hU.fullInertial
  have hf₁ := hU.viscousCoefficient
  have he := fullInertial_forwardEq hU
  have hs₀ := hs.fullInertial
  have hs₁ := hs.viscousCoefficient hK.isClosed
  have hp₀ := hp.fullInertial hU
  have hp₁ := hp.viscousCoefficient
  refine ⟨he.smooth hf₀.smooth, hf₁.smooth, ⟨K, hK, ?_⟩,
    boundedMixed_of_compact_repeating hK hU hs hp,
    he.boundedMixed (boundedMixed_of_compact_repeating hK hf₀ hs₀ hp₀),
    boundedMixed_of_compact_repeating hK hf₁ hs₁ hp₁, ?_, ?_⟩
  · intro t ht x hx
    exact ⟨hs t x hx, (congrFun (he t ht) x).symm.trans (hs₀ t x hx), hs₁ t x hx⟩
  · intro t ht x
    exact congrFun (hp t ht) x
  · intro ν
    dsimp only
    let g : Velocity := fun t x => fullInertial U t x + ν • viscousCoefficient U t x
    have hg : JointSmooth g := hf₀.add (ContDiff.smul (f := fun _ : ℝ × Space => ν) contDiff_const hf₁)
    have hgs : SpatiallySupported K g := by
      intro t x hx
      dsimp [g]
      rw [hs₀ t x hx, hs₁ t x hx, smul_zero, add_zero]
    have hgp : RepeatsAfter 1 g := by
      intro t ht
      ext x i
      dsimp [g]
      rw [hp₀ t ht, hp₁ t ht]
    have hge : ForwardEq g (affineForce (inertialCoefficient U) (viscousCoefficient U) ν) := by
      intro t ht
      ext x i
      dsimp [g, affineForce]
      rw [he t ht]
    refine ⟨residual_zero_pressure_solution ν U hU.smooth hzero hdiv,
      hge.smooth hg.smooth,
      hge.boundedMixed (boundedMixed_of_compact_repeating hK hg hgs hgp), ?_⟩
    intro t ht x
    exact congrFun (hge.repeatsAfter hgp t ht) x

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Encodable
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
variable {O : Set (ℕ →. ℕ)}

lemma computableIn_of_eq {f g : α → β} (hf : ComputableIn O f)
    (h : ∀ a, f a = g a) : ComputableIn O g := (funext h) ▸ hf

lemma computableIn_pair {f : α → β} {g : α → γ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O (fun a => (f a, g a)) := by
  apply Nat.RecursiveIn.of_eq (Nat.RecursiveIn.pair hf hg)
  intro n
  cases decode (α := α) n <;> simp [Seq.seq]

lemma computableIn_comp {f : β → γ} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O (fun a => f (g a)) := by
  apply Nat.RecursiveIn.of_eq (Nat.RecursiveIn.comp hf hg)
  intro n
  cases decode (α := α) n <;> simp

lemma computableIn_comp₂ {δ : Type*} [Primcodable δ] {f : β → γ → δ}
    {g : α → β} {h : α → γ} (hf : ComputableIn₂ O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O (fun a => f (g a) (h a)) :=
  computableIn_comp hf (computableIn_pair hg hh)

lemma computableIn_fin_triple (f g h : α → β) (hf : ComputableIn O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O (fun a => ![f a, g a, h a]) := by
  have hv : Primrec₂ (fun i : Fin 3 => fun p : β × β × β => (![p.1, p.2.1, p.2.2] : Fin 3 → β) i) := by
    apply Primrec.fin_curry₁.mpr
    intro i
    fin_cases i
    · exact Primrec.fst
    · exact Primrec.fst.comp Primrec.snd
    · exact Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : β × β × β => ![p.1, p.2.1, p.2.2]) :=
    Primrec.fin_curry.mpr (hv.comp Primrec.snd Primrec.fst)
  exact computableIn_comp hc.computableIn (computableIn_pair hf (computableIn_pair hg hh))

lemma computableIn_fin_eval {n : ℕ} {f : α → (Fin n → β)} (hf : ComputableIn O f)
    (i : Fin n) : ComputableIn O (fun a => f a i) :=
  computableIn_comp (Primrec.fin_app.comp Primrec.id (Primrec.const i)).computableIn hf

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

lemma fullMixedD_add {v w : Velocity} (hv : JointSmooth v) (hw : JointSmooth w)
    (a : MultiIndex) : fullMixedD a (fun t x => v t x + w t x) =
      fun t x => fullMixedD a v t x + fullMixedD a w t x := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    cases i with
    | none =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [fullTimeD, deriv_fun_add (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t)
        (((hw.fullMixedD a).timeSlice x).differentiable (by simp) t)]
      rfl
    | some i =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [spaceD, fderiv_fun_add (((hv.fullMixedD a).slice t).differentiable (by simp) x)
        (((hw.fullMixedD a).slice t).differentiable (by simp) x)]
      rfl

lemma fullMixedD_smul (v : Velocity) (c : ℝ) (a : MultiIndex) :
    fullMixedD a (fun t x => c • v t x) = fun t x => c • fullMixedD a v t x := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    cases i with
    | none =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [fullTimeD, deriv_fun_const_smul_field]
      rfl
    | some i =>
      simp only [fullMixedD, ih]
      ext t x k
      change fderiv ℝ (c • fullMixedD a v t) x _ k = _
      rw [fderiv_const_smul_field]
      rfl

lemma mixedD_affineForce_of_extensions {v w V W : Velocity}
    (hv : JointSmooth V) (hw : JointSmooth W) (hev : ForwardEq V v) (hew : ForwardEq W w)
    (c : ℝ) (a : MultiIndex) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    mixedD a (affineForce v w c) t x = mixedD a v t x + c • mixedD a w t x := by
  have hcw : JointSmooth (fun t x => c • W t x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => c • W z.1 z.2)
    exact (contDiff_const (c := c)).smul hw
  have hadd : JointSmooth (fun t x => V t x + c • W t x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => V z.1 z.2 + c • W z.1 z.2)
    exact hv.add hcw
  have he : ForwardEq (fun t x => V t x + c • W t x) (affineForce v w c) := by
    intro t ht
    funext x
    change V t x + c • W t x = v t x + c • w t x
    rw [hev t ht, hew t ht]
  rw [← congrFun ((he.mixedD a) t ht) x,
    ← fullMixedD_eq_mixedD hadd a t ht x, fullMixedD_add hv hcw,
    fullMixedD_smul]
  dsimp only
  rw [fullMixedD_eq_mixedD hv a t ht x,
    fullMixedD_eq_mixedD hw a t ht x,
    congrFun ((hev.mixedD a) t ht) x, congrFun ((hew.mixedD a) t ht) x]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity

lemma error_nonneg (n : ℕ) : 0 ≤ error n := by unfold error; positivity

lemma error_le_one (n : ℕ) : error n ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)

lemma error_add (n k : ℕ) : error (n + k) = error n * error k := pow_add _ _ _

lemma nat_mul_error_shift (n k : ℕ) : (k : ℝ) * error (n + k) ≤ error n := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.cast_succ, pow_succ]
      have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
  have he : (k : ℝ) * error k ≤ 1 := by
    unfold error
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr hk
  rw [error_add]
  nlinarith [mul_le_mul_of_nonneg_left he (error_nonneg n)]

lemma family_effective_field {v : Family Velocity} (hv : EffectiveFamily v)
    (M : FiniteMachine) (w : Input M) (O : Set (ℕ →. ℕ)) : EffectiveFieldIn O (v M w) := by
  obtain ⟨E, b, R, hE, hb, _, heval, hbound, _⟩ := hv
  refine ⟨(fun s => E (inputCode M w, s)), (fun a => b (inputCode M w, a)),
    (hE.comp ((Computable.const _).pair Computable.id)).computableIn,
    (hb.comp ((Computable.const _).pair Computable.id)).computableIn, ?_, ?_⟩
  · intro a z n hz i
    exact heval M w a z n hz i
  · intro a t ht x
    exact hbound M w a t ht x

lemma realName_oracle_computable (name : ℕ → ℚ) :
    ComputableIn {nameOracle name} name := by
  have h := Nat.RecursiveIn.oracle (O := {nameOracle name}) (nameOracle name) (Set.mem_singleton _)
  change Nat.RecursiveIn {nameOracle name} (fun n => Part.some (Encodable.encode (name n))) at h
  have hr := Nat.RecursiveIn.comp (Primrec.nat_iff.mp primrec_ratRank).recursiveIn h
  apply Nat.RecursiveIn.of_eq hr
  intro n
  simp only [Part.bind_some, Encodable.decode_nat,
    Part.coe_some, Part.map_some]
  change (Part.some (rawRatCode (name n))).bind (fun k => Part.some (ratRank k)) = _
  rw [Part.bind_some]
  exact congrArg Part.some (ratRank_code (name n))

lemma computableIn_rat_add {α : Type*} [Primcodable α] {O : Set (ℕ →. ℕ)}
    {f g : α → ℚ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f a + g a) :=
  computableIn_comp (O := O) (f := fun p : ℚ × ℚ => p.1 + p.2) (g := fun a => (f a, g a))
    (Computable.computableIn computable_rat_add) (computableIn_pair hf hg)

lemma computableIn_rat_mul {α : Type*} [Primcodable α] {O : Set (ℕ →. ℕ)}
    {f g : α → ℚ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f a * g a) :=
  computableIn_comp (O := O) (f := fun p : ℚ × ℚ => p.1 * p.2) (g := fun a => (f a, g a))
    (Computable.computableIn computable_rat_mul) (computableIn_pair hf hg)

theorem effective_affine_force {O : Set (ℕ →. ℕ)} {v w : Velocity} {ν : ℝ}
    (hv : EffectiveFieldIn O v) (hw : EffectiveFieldIn O w)
    {name : ℕ → ℚ} (hc : ComputableIn O name) (hn : RealName name ν)
    (hlin : ∀ a t, 0 ≤ t → ∀ x,
      mixedD a (affineForce v w ν) t x = mixedD a v t x + ν • mixedD a w t x) :
    EffectiveFieldIn O (affineForce v w ν) := by
  obtain ⟨E₀, b₀, hE₀, hb₀, he₀, hbound₀⟩ := hv
  obtain ⟨E₁, b₁, hE₁, hb₁, he₁, hbound₁⟩ := hw
  obtain ⟨C, hC⟩ := exists_nat_ge |ν|
  let prec : MultiIndex × RationalPoint × ℕ → ℕ := fun s => s.2.2 + (C + b₁ s.1 + 2)
  have hb₁' : ComputableIn O (fun s : MultiIndex × RationalPoint × ℕ => b₁ s.1) :=
    computableIn_comp hb₁ ComputableIn.fst
  have hprec : ComputableIn O prec := by
    exact computableIn_comp₂ Primrec.nat_add.computableIn₂
      (computableIn_comp ComputableIn.snd ComputableIn.snd)
      (computableIn_comp₂ Primrec.nat_add.computableIn₂
        (computableIn_comp₂ Primrec.nat_add.computableIn₂ (ComputableIn.const C) hb₁')
        (ComputableIn.const 2))
  let arg : MultiIndex × RationalPoint × ℕ → MultiIndex × RationalPoint × ℕ :=
    fun s => (s.1, s.2.1, prec s)
  have harg : ComputableIn O arg := computableIn_pair ComputableIn.fst
    (computableIn_pair (computableIn_comp ComputableIn.fst ComputableIn.snd) hprec)
  let E : MultiIndex × RationalPoint × ℕ → Fin 3 → ℚ :=
    fun s i => E₀ (arg s) i + name (prec s) * E₁ (arg s) i
  have hi (i : Fin 3) : ComputableIn O (fun s => E s i) := by
    have h₀ : ComputableIn O (fun s => E₀ (arg s) i) :=
      computableIn_fin_eval (computableIn_comp hE₀ harg) i
    have h₁ : ComputableIn O (fun s => E₁ (arg s) i) :=
      computableIn_fin_eval (computableIn_comp hE₁ harg) i
    have hn' : ComputableIn O (fun s => name (prec s)) := computableIn_comp hc hprec
    exact computableIn_rat_add h₀ (computableIn_rat_mul hn' h₁)
  have hE : ComputableIn O E := by
    refine computableIn_of_eq (computableIn_fin_triple _ _ _ (hi 0) (hi 1) (hi 2)) ?_
    intro s
    ext i
    fin_cases i <;> rfl
  let b : MultiIndex → ℕ := fun a => b₀ a + C * b₁ a
  have hb : ComputableIn O b := computableIn_comp₂ Primrec.nat_add.computableIn₂ hb₀
    (computableIn_comp₂ Primrec.nat_mul.computableIn₂ (ComputableIn.const C) hb₁)
  refine ⟨E, b, hE, hb, ?_, ?_⟩
  · intro a z n hz i
    let k := prec (a,z,n)
    have h₀ := he₀ a z k hz i
    have h₁ := he₁ a z k hz i
    have hν := hn k
    have hνb : |(name k : ℝ)| ≤ C + 1 := by
      have htriangle : |(name k : ℝ)| ≤ |(name k : ℝ) - ν| + |ν| := by
        simpa only [sub_add_cancel] using abs_add_le ((name k : ℝ) - ν) ν
      linarith [error_le_one k]
    have hwval : |mixedD a w (z.1 : ℝ) (rationalSpace z.2) i| ≤ b₁ a :=
      (norm_le_pi_norm _ i).trans (hbound₁ a _ (by exact_mod_cast hz) _)
    have hid : (E (a,z,n) i : ℝ) -
        mixedD a (affineForce v w ν) (z.1 : ℝ) (rationalSpace z.2) i =
        ((E₀ (a,z,k) i : ℝ) - mixedD a v (z.1 : ℝ) (rationalSpace z.2) i) +
        (name k : ℝ) * ((E₁ (a,z,k) i : ℝ) - mixedD a w (z.1 : ℝ) (rationalSpace z.2) i) +
        ((name k : ℝ) - ν) * mixedD a w (z.1 : ℝ) (rationalSpace z.2) i := by
      rw [hlin a _ (by exact_mod_cast hz)]
      dsimp [E, arg, k]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ (error k + (C + 1) * error k) + error k * (b₁ a : ℝ) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_add_le _ _).trans (add_le_add h₀ ?_)
          rw [abs_mul]
          exact mul_le_mul hνb h₁ (abs_nonneg _) (by positivity)
        · rw [abs_mul]
          exact mul_le_mul hν hwval (abs_nonneg _) (error_nonneg k)
      _ = (C + b₁ a + 2 : ℕ) * error (n + (C + b₁ a + 2)) := by
        dsimp [k, prec]
        push_cast
        ring
      _ ≤ error n := nat_mul_error_shift n _
  · intro a t ht x
    rw [hlin a t ht x]
    calc
      _ ≤ ‖mixedD a v t x‖ + ‖ν • mixedD a w t x‖ := norm_add_le _ _
      _ ≤ (b₀ a : ℝ) + C * (b₁ a : ℝ) := by
        apply add_le_add (hbound₀ a t ht x)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul hC (hbound₁ a t ht x) (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (b a : ℝ) := by simp [b]

theorem effective_viscosity_clauses {v w V W : Velocity}
    (hv : Geometry.JointSmooth V) (hw : Geometry.JointSmooth W)
    (hev : Geometry.ForwardEq V v) (hew : Geometry.ForwardEq W w)
    (ev : EffectiveFieldIn ∅ v) (ew : EffectiveFieldIn ∅ w) (ν : ℝ) :
    (ComputableReal ν → EffectiveFieldIn ∅ (affineForce v w ν)) ∧
    (∀ name : ℕ → ℚ, RealName name ν →
      EffectiveFieldIn {nameOracle name} (affineForce v w ν)) := by
  have hlin := Geometry.mixedD_affineForce_of_extensions hv hw hev hew ν
  constructor
  · rintro ⟨name, hc, hn⟩
    exact effective_affine_force ev ew hc.computableIn hn hlin
  · intro name hn
    have lift {f : Velocity} (hf : EffectiveFieldIn ∅ f) (O : Set (ℕ →. ℕ)) :
        EffectiveFieldIn O f := by
      obtain ⟨E,b,hE,hb,heval,hbound⟩ := hf
      refine ⟨E,b,?_,?_,heval,hbound⟩
      · exact hE.mono (Set.empty_subset O)
      · exact hb.mono (Set.empty_subset O)
    exact effective_affine_force (lift ev _) (lift ew _)
      (realName_oracle_computable name) hn hlin

theorem residual_effective_viscosity {U : Family Velocity}
    (hU : ∀ M w, Geometry.JointSmooth (U M w))
    (ef₀ : EffectiveFamily (fun M w => inertialCoefficient (U M w)))
    (ef₁ : EffectiveFamily (fun M w => viscousCoefficient (U M w)))
    (M : FiniteMachine) (w : Input M) (ν : ℝ) :
    (ComputableReal ν → EffectiveFieldIn ∅
      (affineForce (inertialCoefficient (U M w)) (viscousCoefficient (U M w)) ν)) ∧
    (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name}
      (affineForce (inertialCoefficient (U M w)) (viscousCoefficient (U M w)) ν)) :=
  effective_viscosity_clauses (hU M w).fullInertial (hU M w).viscousCoefficient
    (Geometry.fullInertial_forwardEq (hU M w)) (fun _ _ => rfl)
    (family_effective_field ef₀ M w ∅) (family_effective_field ef₁ M w ∅) ν

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

def rhoCoeffStep (cs : List ℤ) : List ℤ :=
  0 :: 0 :: (List.range cs.length).map (fun j =>
    cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0)

def rhoCoeffs : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => rhoCoeffStep (rhoCoeffs n)

lemma primrec_rhoCoeffStep : Primrec rhoCoeffStep := by
  have h : Primrec₂ (fun cs : List ℤ => fun j : ℕ =>
      cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0) := by
    have h₁ : Primrec (fun p : List ℤ × ℕ => (p.2 + 1 : ℤ)) := by
      exact (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)).of_eq
        (fun _ => by simp)
    exact (primrec_int_add.comp (Primrec.list_getD 0)
      (primrec_int_neg.comp (primrec_int_mul.comp h₁
        ((Primrec.list_getD 0).comp Primrec.fst (Primrec.succ.comp Primrec.snd))))).of_eq
          (fun _ => (sub_eq_add_neg _ _).symm)
  exact Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp
    (Primrec.const 0) (Primrec.list_map (Primrec.list_range.comp Primrec.list_length) h))

lemma primrec_rhoCoeffs : Primrec rhoCoeffs := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => List ℤ)
      [1] (fun _ cs => rhoCoeffStep cs) n) :=
    Primrec.nat_rec (Primrec.const [1])
      (primrec_rhoCoeffStep.comp (Primrec.snd.comp Primrec.snd)).to₂
  refine (h.comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg rhoCoeffStep ih

lemma getD_zero_of_length_le {cs : List ℤ} {j : ℕ} (h : cs.length ≤ j) :
    cs.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma rhoCoeffStep_getD (cs : List ℤ) (j : ℕ) :
    (rhoCoeffStep cs).getD (j + 2) 0 =
      cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0 := by
  simp only [rhoCoeffStep, List.getD_cons_succ]
  by_cases hj : j < cs.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  · have hj' : cs.length ≤ j := le_of_not_gt hj
    rw [getD_zero_of_length_le (by simpa using hj'), getD_zero_of_length_le hj',
      getD_zero_of_length_le (by omega)]
    simp

lemma rhoCoeffs_spec (n j : ℕ) : (rhoCoeffs n).getD j 0 = (rhoPolynomial n).coeff j := by
  induction n generalizing j with
  | zero =>
    cases j <;> simp [rhoCoeffs, rhoPolynomial, List.getD_eq_getElem?_getD, coeff_one]
  | succ n ih =>
    cases j with
    | zero => simp [rhoCoeffs, rhoCoeffStep, rhoPolynomial]
    | succ j =>
      cases j with
      | zero => simp [rhoCoeffs, rhoCoeffStep, rhoPolynomial, coeff_X_pow_mul']
      | succ j =>
        rw [show j + 1 + 1 = j + 2 by omega, rhoCoeffs, rhoCoeffStep_getD,
          rhoPolynomial, coeff_X_pow_mul, coeff_sub, coeff_derivative, ← ih, ← ih]
        ring

lemma rhoCoeffs_length (n : ℕ) : (rhoCoeffs n).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rhoCoeffs, rhoCoeffStep, List.length_cons, List.length_map,
      List.length_range, ih]; omega

lemma rhoPolynomial_coeff_zero (n j : ℕ) (h : (rhoCoeffs n).length ≤ j) :
    (rhoPolynomial n).coeff j = 0 := by
  rw [← rhoCoeffs_spec, getD_zero_of_length_le h]

lemma rhoPolynomial_support_subset (n : ℕ) :
    (rhoPolynomial n).support ⊆ Finset.range (rhoCoeffs n).length := by
  intro j hj
  rw [Finset.mem_range]
  by_contra h
  exact (mem_support_iff.mp hj) (rhoPolynomial_coeff_zero _ _ (le_of_not_gt h))

def rhoBound (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (rhoCoeffs n).length,
    ((rhoCoeffs n).getD j 0).natAbs * (j + k).factorial

lemma primrec_sum_range_nat {α : Type*} [Primcodable α]
    {f : α → ℕ → ℕ} (hf : Primrec₂ f) :
    Primrec₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hh : Primrec₂ (fun a n => Nat.rec (motive := fun _ => ℕ) 0
      (fun j r => r + f a j) n) :=
    Primrec.nat_rec (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
        (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂
  refine hh.of_eq ?_
  intro a n
  induction n with
  | zero => simp
  | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun r => r + f a n) ih

lemma primrec_rhoBound : Primrec₂ rhoBound := by
  have hh : Primrec₂ (fun p : ℕ × ℕ => fun j =>
      ((rhoCoeffs p.1).getD j 0).natAbs * (j + p.2).factorial) :=
    Primrec.nat_mul.comp
      (primrec_int_natAbs.comp ((Primrec.list_getD 0).comp
        (primrec_rhoCoeffs.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (primrec_nat_factorial.comp (Primrec.nat_add.comp Primrec.snd
        (Primrec.snd.comp Primrec.fst)))
  exact (primrec_sum_range_nat hh).comp Primrec.id
    (Primrec.list_length.comp (primrec_rhoCoeffs.comp Primrec.fst))

lemma rhoBound_eq (n k : ℕ) : rhoBound n k = rhoWeight (rhoPolynomial n) k := by
  unfold rhoBound rhoWeight
  simp only [rhoCoeffs_spec]
  exact (Finset.sum_subset (rhoPolynomial_support_subset n) (by
    intro j _ hj
    have hz : (rhoPolynomial n).coeff j = 0 := notMem_support_iff.mp hj
    simp [hz])).symm

lemma rhoJet_bound_computable (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoBound n 0 : ℝ) := by
  rw [rhoBound_eq]
  exact rhoJet_bound n x

def rhoPolyValue (n : ℕ) (q : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (rhoCoeffs n).length, ((rhoCoeffs n).getD j 0 : ℚ) * q ^ j

lemma computable_rhoPolyValue : Computable₂ rhoPolyValue := by
  have hh : Computable₂ (fun p : ℕ × ℚ => fun j =>
      ((rhoCoeffs p.1).getD j 0 : ℚ) * p.2 ^ j) :=
    computable_rat_mul.comp
      (computable_rat_intCast.comp ((Primrec.list_getD 0).to_comp.comp
        (primrec_rhoCoeffs.to_comp.comp (Computable.fst.comp Computable.fst)) Computable.snd))
      (computable_rat_pow.comp (Computable.snd.comp Computable.fst) Computable.snd)
  exact (computable_sum_range hh).comp Computable.id
    (Primrec.list_length.to_comp.comp (primrec_rhoCoeffs.to_comp.comp Computable.fst))

lemma rhoPolyValue_cast (n : ℕ) (q : ℚ) :
    (rhoPolyValue n q : ℝ) = (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) (q : ℝ) := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp only [rhoPolyValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_pow,
    rhoCoeffs_spec]
  change (∑ j ∈ Finset.range (rhoCoeffs n).length, ((rhoPolynomial n).coeff j : ℝ) * (q : ℝ) ^ j) = _
  exact (Finset.sum_subset (rhoPolynomial_support_subset n) (by
    intro j _ hj
    have hz : (rhoPolynomial n).coeff j = 0 := notMem_support_iff.mp hj
    simp [hz])).symm

lemma rat_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
  have ha : ((q.num.natAbs : ℕ) : ℝ) = |(q.num : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun a : ℤ => (a : ℝ)) (Int.natCast_natAbs q.num)
  rw [← ha]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < q.den)).mpr
    (le_mul_of_one_le_right (by positivity) hden)

noncomputable def rhoApprox (n : ℕ) (q : ℚ) (p : ℕ) : ℚ :=
  if q ≤ 0 then 0 else
    rhoPolyValue n q⁻¹ * expApprox (-q⁻¹) (p + (rhoPolyValue n q⁻¹).num.natAbs)

lemma computable_rhoApprox : Computable (fun s : ℕ × ℚ × ℕ => rhoApprox s.1 s.2.1 s.2.2) := by
  have hq : Computable (fun s : ℕ × ℚ × ℕ => s.2.1⁻¹) :=
    computable_rat_inv.comp (Computable.fst.comp Computable.snd)
  have hv : Computable (fun s : ℕ × ℚ × ℕ => rhoPolyValue s.1 s.2.1⁻¹) :=
    computable_rhoPolyValue.comp Computable.fst hq
  exact computable_ite (computable_rat_le.comp (Computable.fst.comp Computable.snd)
    (Computable.const 0)) (Computable.const 0)
    (computable_rat_mul.comp hv (computable_expApprox.comp (computable_rat_neg.comp hq)
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
        (primrec_int_natAbs.to_comp.comp (computable_rat_num.comp hv)))))

lemma rhoApprox_spec (n : ℕ) (q : ℚ) (p : ℕ) :
    |(rhoApprox n q p : ℝ) - rhoJet n (q : ℝ)| ≤ error p := by
  by_cases hq : q ≤ 0
  · simp [rhoApprox, hq, rhoJet_zero_of_nonpos n (Rat.cast_nonpos.mpr hq), error_nonneg]
  · have hqp : (0 : ℝ) < q := Rat.cast_pos.mpr (lt_of_not_ge hq)
    rw [rhoApprox, ite_eq_right hq, Rat.cast_mul]
    have hid : rhoJet n (q : ℝ) = (rhoPolyValue n q⁻¹ : ℝ) * Real.exp (-((q : ℝ)⁻¹)) := by
      rw [rhoJet, expNegInvGlue, ite_eq_right hqp.not_ge, rhoPolyValue_cast, Rat.cast_inv]
    rw [hid, ← mul_sub, abs_mul]
    have he := expApprox_spec (-q⁻¹) (p + (rhoPolyValue n q⁻¹).num.natAbs)
    simp only [Rat.cast_neg, Rat.cast_inv] at he
    exact (mul_le_mul (rat_abs_le_num _) he (abs_nonneg _) (by positivity)).trans
      (nat_mul_error_shift _ _)

lemma rhoJet_lipschitz (n : ℕ) : LipschitzWith (rhoBound (n + 1) 0 : ℝ≥0) (rhoJet n) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (rhoJet_hasDerivAt n x).differentiableAt)
  intro x
  rw [(rhoJet_hasDerivAt n x).deriv]
  exact_mod_cast rhoJet_bound_computable (n + 1) x

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

lemma computable_rat_lt : Computable₂ (fun a b : ℚ => decide (a < b)) := by
  exact (Computable.cond (computable_rat_le.comp Computable.snd Computable.fst)
    (Computable.const false) (Computable.const true)).of_eq
      (fun p => by
        by_cases h : p.2 ≤ p.1
        · simp [h, not_lt.mpr h]
        · simp [h, lt_of_not_ge h])

noncomputable def logBracket (q : ℚ) (n c : ℕ) : Prop :=
  let r := Denumerable.ofNat ℚ c.unpair.1
  let k := c.unpair.2
  expApprox (r - (1 / 2 : ℚ) ^ n) k + (1 / 2 : ℚ) ^ k < q ∧
    q < expApprox (r + (1 / 2 : ℚ) ^ n) k - (1 / 2 : ℚ) ^ k

noncomputable instance (q : ℚ) (n : ℕ) : DecidablePred (logBracket q n) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma computable_logBracket :
    Computable₂ (fun p : ℚ × ℕ => fun c => decide (logBracket p.1 p.2 c)) := by
  have hr : Computable (fun p : (ℚ × ℕ) × ℕ => Denumerable.ofNat ℚ p.2.unpair.1) :=
    (Computable.ofNat ℚ).comp (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.snd))
  have hk : Computable (fun p : (ℚ × ℕ) × ℕ => p.2.unpair.2) :=
    Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd)
  have he : Computable (fun p : (ℚ × ℕ) × ℕ => (1 / 2 : ℚ) ^ p.1.2) :=
    computable_rat_pow.comp (Computable.const (1 / 2)) (Computable.snd.comp Computable.fst)
  have hd : Computable (fun p : (ℚ × ℕ) × ℕ => (1 / 2 : ℚ) ^ p.2.unpair.2) :=
    computable_rat_pow.comp (Computable.const (1 / 2)) hk
  exact computable_decide_and
    (computable_rat_lt.comp
      (computable_rat_add.comp (computable_expApprox.comp (computable_rat_sub.comp hr he) hk) hd)
      (Computable.fst.comp Computable.fst))
    (computable_rat_lt.comp (Computable.fst.comp Computable.fst)
      (computable_rat_sub.comp (computable_expApprox.comp (computable_rat_add.comp hr he) hk) hd))

lemma cast_error (n : ℕ) : (((1 / 2 : ℚ) ^ n : ℚ) : ℝ) = error n := by
  simp [error, one_div]

lemma error_tendsto : Tendsto error atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma exists_logBracket {q : ℚ} (hq : 0 < q) (n : ℕ) : ∃ c, logBracket q n c := by
  have he : 0 < error n := by unfold error; positivity
  obtain ⟨r, hr₀, hr₁⟩ := exists_rat_btwn
    (show Real.log (q : ℝ) - error n < Real.log (q : ℝ) + error n by linarith)
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have h₀ : Real.exp ((r : ℝ) - error n) < (q : ℝ) := by
    rw [← Real.exp_log hq', Real.exp_lt_exp]
    linarith
  have h₁ : (q : ℝ) < Real.exp ((r : ℝ) + error n) := by
    rw [← Real.exp_log hq', Real.exp_lt_exp]
    linarith
  have hd : Tendsto (fun k => 2 * error k) atTop (𝓝 0) := by
    simpa using error_tendsto.const_mul 2
  obtain ⟨k, hk₀, hk₁⟩ := ((hd.eventually_lt_const (sub_pos.mpr h₀)).and
    (hd.eventually_lt_const (sub_pos.mpr h₁))).exists
  refine ⟨Nat.pair (@Encodable.encode ℚ (inferInstance : Primcodable ℚ).toEncodable r) k, ?_⟩
  simp only [logBracket, Nat.unpair_pair, Denumerable.ofNat_encode]
  have hl := (abs_le.mp (expApprox_spec (r - (1 / 2 : ℚ) ^ n) k)).2
  have hu := (abs_le.mp (expApprox_spec (r + (1 / 2 : ℚ) ^ n) k)).1
  simp only [Rat.cast_sub, Rat.cast_add, cast_error] at hl hu
  constructor
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [Rat.cast_add, cast_error]
    linarith
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [Rat.cast_sub, cast_error]
    linarith

lemma logBracket_spec {q : ℚ} (hq : 0 < q) {n c : ℕ} (hc : logBracket q n c) :
    |(Denumerable.ofNat ℚ c.unpair.1 : ℝ) - Real.log (q : ℝ)| ≤ error n := by
  let r := Denumerable.ofNat ℚ c.unpair.1
  let k := c.unpair.2
  have he₀ := (abs_le.mp (expApprox_spec (r - (1 / 2 : ℚ) ^ n) k)).1
  have he₁ := (abs_le.mp (expApprox_spec (r + (1 / 2 : ℚ) ^ n) k)).2
  simp only [Rat.cast_sub, Rat.cast_add, cast_error] at he₀ he₁
  have hb₀ := (Rat.cast_lt (K := ℝ)).mpr hc.1
  have hb₁ := (Rat.cast_lt (K := ℝ)).mpr hc.2
  change ((expApprox (r - (1 / 2 : ℚ) ^ n) k + (1 / 2 : ℚ) ^ k : ℚ) : ℝ) < _ at hb₀
  change (q : ℝ) < ((expApprox (r + (1 / 2 : ℚ) ^ n) k - (1 / 2 : ℚ) ^ k : ℚ) : ℝ) at hb₁
  simp only [Rat.cast_add, Rat.cast_sub, cast_error] at hb₀ hb₁
  have hl : (r : ℝ) - error n < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt (Rat.cast_pos.mpr hq)).mpr (by linarith)
  have hu : Real.log (q : ℝ) < (r : ℝ) + error n :=
    (Real.log_lt_iff_lt_exp (Rat.cast_pos.mpr hq)).mpr (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def logSearchPredicate (p : ℚ × ℕ) (c : ℕ) : Prop :=
  if 0 < p.1 then logBracket p.1 p.2 c else True

noncomputable instance : DecidableRel logSearchPredicate := by
  intro p c
  unfold logSearchPredicate
  infer_instance

lemma exists_logSearchPredicate (p : ℚ × ℕ) : ∃ c, logSearchPredicate p c := by
  by_cases hq : 0 < p.1
  · simpa [logSearchPredicate, hq] using exists_logBracket hq p.2
  · exact ⟨0, by simp [logSearchPredicate, hq]⟩

noncomputable def logCutoff (p : ℚ × ℕ) : ℕ := Nat.find (exists_logSearchPredicate p)

lemma computable_logCutoff : Computable logCutoff := by
  apply computable_find (hex := exists_logSearchPredicate)
  exact (Computable.cond (computable_rat_lt.comp (Computable.const 0)
    (Computable.fst.comp Computable.fst)) computable_logBracket (Computable.const true)).of_eq
      (fun p => by by_cases hq : 0 < p.1.1 <;> simp [logSearchPredicate, hq])

noncomputable def logApprox (q : ℚ) (n : ℕ) : ℚ :=
  if 0 < q then Denumerable.ofNat ℚ (logCutoff (q,n)).unpair.1 else 0

lemma computable_logApprox : Computable₂ logApprox := by
  exact computable_ite (computable_rat_lt.comp (Computable.const 0) Computable.fst)
    ((Computable.ofNat ℚ).comp (Computable.fst.comp
      (Primrec.unpair.to_comp.comp computable_logCutoff))) (Computable.const 0)

lemma logApprox_spec {q : ℚ} (hq : 0 < q) (n : ℕ) :
    |(logApprox q n : ℝ) - Real.log (q : ℝ)| ≤ error n := by
  rw [logApprox, ite_eq_left hq]
  apply logBracket_spec hq
  have hh := Nat.find_spec (exists_logSearchPredicate (q,n))
  simpa only [logSearchPredicate, ite_eq_left hq, logCutoff] using hh

lemma log_abs_bound {q : ℚ} (hq : 0 < q) :
    |Real.log (q : ℝ)| ≤ (q.num.natAbs + q⁻¹.num.natAbs : ℕ) := by
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have h₀ := Real.log_le_sub_one_of_pos hq'
  have h₁ := Real.log_le_sub_one_of_pos (inv_pos.mpr hq')
  rw [Real.log_inv] at h₁
  have ha := rat_abs_le_num q
  have hb := rat_abs_le_num q⁻¹
  rw [Rat.cast_inv] at hb
  rw [abs_of_pos hq'] at ha
  rw [abs_of_pos (inv_pos.mpr hq')] at hb
  apply abs_le.mpr
  push_cast
  constructor <;> linarith [Nat.cast_nonneg q.num.natAbs (α := ℝ),
    Nat.cast_nonneg q⁻¹.num.natAbs (α := ℝ)]

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    [Inhabited β] {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s,b)) (g a)) := by
  have hc : Computable (fun a => Nat.rec (motive := fun _ => σ) (g a)
      (fun j v => h a (v, (f a).getD j default)) (f a).length) :=
    Computable.nat_rec (Computable.list_length.comp hf) hg
      (hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair
        ((Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))).to₂
  apply hc.of_eq
  intro a
  have he (n : ℕ) (hn : n ≤ (f a).length) : Nat.rec (motive := fun _ => σ) (g a)
      (fun j v => h a (v, (f a).getD j default)) n =
      ((f a).take n).foldl (fun s b => h a (s,b)) (g a) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hl : n < (f a).length := by omega
      change h a (Nat.rec (motive := fun _ => σ) (g a)
        (fun j v => h a (v, (f a).getD j default)) n, (f a).getD n default) = _
      rw [ih (by omega), List.take_succ_eq_append_getElem hl,
        List.foldl_concat]
      rw [List.getD_eq_getElem _ _ hl]
  simpa using he (f a).length le_rfl

lemma computable_fin_cases {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {n : ℕ} {i : α → Fin n} {f : Fin n → α → β}
    (hi : Computable i) (hf : ∀ j, Computable (f j)) :
    Computable (fun a => f (i a) a) := by
  have hl : Computable (fun a => List.ofFn (fun j => f j a)) :=
    Computable.list_ofFn hf
  exact ((Primrec.list_getD default).to_comp.comp hl (Primrec.fin_val.to_comp.comp hi)).of_eq
    (fun a => by simp)

abbrev NumericOp := Fin 9 × ℚ × ℕ × ℕ

abbrev NumericProgram := List NumericOp

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

def tag (o : NumericOp) : Fin 9 := o.1

def rat (o : NumericOp) : ℚ := o.2.1

def left (o : NumericOp) : ℕ := o.2.2.1

def right (o : NumericOp) : ℕ := o.2.2.2

noncomputable def real (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s : List ℝ) : ℝ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  match o.tag with
  | 0 => q
  | 1 => x (Fin.ofNat d a)
  | 2 => s.getD a 0 + s.getD b 0
  | 3 => s.getD a 0 * s.getD b 0
  | 4 => -s.getD a 0
  | 5 => (s.getD a 0)⁻¹
  | 6 => rhoJet a (s.getD b 0)
  | 7 => Real.exp (s.getD a 0)
  | 8 => if 0 < q then Real.log (q : ℝ) else 0

noncomputable def rationalCase (d : ℕ) [NeZero d] (j : Fin 9) (o : NumericOp) (x : Fin d → ℚ)
    (p : ℕ) (s : List ℚ) : ℚ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  match j with
  | 0 => q
  | 1 => x (Fin.ofNat d a)
  | 2 => s.getD a 0 + s.getD b 0
  | 3 => s.getD a 0 * s.getD b 0
  | 4 => -s.getD a 0
  | 5 => (max ((b + 1 : ℕ) : ℚ)⁻¹ (s.getD a 0))⁻¹
  | 6 => rhoApprox a (s.getD b 0) p
  | 7 => expApprox (s.getD a 0) p
  | 8 => logApprox q p

noncomputable def rational (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p : ℕ) (s : List ℚ) : ℚ := rationalCase d o.tag o x p s

def boundCase (j : Fin 9) (o : NumericOp) (C : ℕ) (s : List (ℕ × ℕ)) : ℕ × ℕ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  let A := (s.getD a (0,0)).1
  let E := (s.getD a (0,0)).2
  let B := (s.getD b (0,0)).1
  let F := (s.getD b (0,0)).2
  match j with
  | 0 => (q.num.natAbs, 0)
  | 1 => (C, 0)
  | 2 => (A + B, E + F)
  | 3 => (A * B, (A + E) * F + B * E)
  | 4 => (A, E)
  | 5 => (b + 1, (b + 1)^2 * E)
  | 6 => (rhoBound a 0, 1 + rhoBound (a+1) 0 * F)
  | 7 => (3^A, 1 + 3^(A+E) * E)
  | 8 => (q.num.natAbs + q⁻¹.num.natAbs, 1)

def bound (o : NumericOp) (C : ℕ) (s : List (ℕ × ℕ)) : ℕ × ℕ :=
  boundCase o.tag o C s

def Valid (o : NumericOp) (s : List ℝ) : Prop :=
  o.tag = 5 → ((o.right + 1 : ℕ) : ℝ)⁻¹ ≤ s.getD o.left 0

lemma computable_rational (d : ℕ) [NeZero d] :
    Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ =>
      rational d z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have ha : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.left) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.right) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hq : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.1.rat) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hp : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ => z.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hva := (Primrec.list_getD (0 : ℚ)).to_comp.comp hs ha
  have hvb := (Primrec.list_getD (0 : ℚ)).to_comp.comp hs hb
  have hi : Primrec (fun a : ℕ => Fin.ofNat d a) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const d))
  have hmax : Computable₂ (fun a b : ℚ => max a b) := by
    exact (computable_ite computable_rat_le Computable.snd Computable.fst).of_eq
      (fun p => by split_ifs with h <;> simp [max_def, h])
  have hc (j : Fin 9) : Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ =>
      rationalCase d j z.1 z.2.1 z.2.2.1 z.2.2.2) := by
    fin_cases j <;> dsimp only [rationalCase, rat, left, right]
    · simpa only [left, right, rat] using hq
    · simpa only [left, right, rat, id_eq] using Computable.fin_app.comp (Computable.fst.comp Computable.snd) (hi.to_comp.comp ha)
    · simpa only [left, right, rat] using computable_rat_add.comp hva hvb
    · simpa only [left, right, rat] using computable_rat_mul.comp hva hvb
    · simpa only [left, right, rat] using computable_rat_neg.comp hva
    · simpa only [left, right, rat] using computable_rat_inv.comp (hmax.comp
        (computable_rat_inv.comp (computable_rat_natCast.comp (Computable.succ.comp hb))) hva)
    · simpa only [left, right, rat] using computable_rhoApprox.comp (ha.pair (hvb.pair hp))
    · simpa only [left, right, rat] using computable_expApprox.comp hva hp
    · simpa only [left, right, rat] using computable_logApprox.comp hq hp
  have H := computable_fin_cases (i := fun z => z.1.tag)
    (Computable.fst.comp Computable.fst) hc
  simpa only [rational] using H

lemma computable_bound : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) =>
    bound z.1 z.2.1 z.2.2) := by
  have ha : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.left) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hb : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.right) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hq : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.1.rat) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hva := (Primrec.list_getD (0,0)).to_comp.comp hs ha
  have hvb := (Primrec.list_getD (0,0)).to_comp.comp hs hb
  have hA := Computable.fst.comp hva
  have hE := Computable.snd.comp hva
  have hB := Computable.fst.comp hvb
  have hF := Computable.snd.comp hvb
  have hadd := Primrec.nat_add.to_comp
  have hmul := Primrec.nat_mul.to_comp
  have hpow : Computable₂ (fun a b : ℕ => a ^ b) := by
    exact (((Primrec.nat_iff.mpr Nat.Primrec.pow).comp Primrec.encode).of_eq
      (fun p => by rcases p with ⟨a,b⟩; change (Nat.unpair (Nat.pair a b)).1 ^ (Nat.unpair (Nat.pair a b)).2 = a ^ b; rw [Nat.unpair_pair])).to_comp
  have hn := primrec_int_natAbs.to_comp.comp (computable_rat_num.comp hq)
  have hc (j : Fin 9) : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) =>
      boundCase j z.1 z.2.1 z.2.2) := by
    fin_cases j <;> dsimp only [boundCase, rat, left, right]
    · simpa only [left, right, rat] using hn.pair (Computable.const 0)
    · simpa only [left, right, rat] using (Computable.fst.comp Computable.snd).pair (Computable.const 0)
    · simpa only [left, right, rat] using (hadd.comp hA hB).pair (hadd.comp hE hF)
    · simpa only [left, right, rat] using (hmul.comp hA hB).pair
        (hadd.comp (hmul.comp (hadd.comp hA hE) hF) (hmul.comp hB hE))
    · simpa only [left, right, rat] using hva
    · simpa only [left, right, rat] using (Computable.succ.comp hb).pair
        (hmul.comp (hpow.comp (Computable.succ.comp hb) (Computable.const 2)) hE)
    · simpa only [left, right, rat] using (primrec_rhoBound.to_comp.comp ha (Computable.const 0)).pair
        (hadd.comp (Computable.const 1) (hmul.comp
          (primrec_rhoBound.to_comp.comp (Computable.succ.comp ha) (Computable.const 0)) hF))
    · simpa only [left, right, rat] using (hpow.comp (Computable.const 3) hA).pair
        (hadd.comp (Computable.const 1) (hmul.comp
          (hpow.comp (Computable.const 3) (hadd.comp hA hE)) hE))
    · simpa only [left, right, rat] using (hadd.comp hn (primrec_int_natAbs.to_comp.comp
        (computable_rat_num.comp (computable_rat_inv.comp hq)))).pair (Computable.const 1)
  have H := computable_fin_cases (i := fun z => z.1.tag)
    (Computable.fst.comp Computable.fst) hc
  simpa only [bound] using H

end BalancedTransport.Effectivity.NumericOp
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ComputableRules
attribute [fun_prop] Computable
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] lemma identity : Computable (fun x : α => x) := Computable.id

@[fun_prop] lemma constant (b : β) : Computable (fun _ : α => b) := Computable.const b

@[fun_prop] lemma compose (f : β → γ) (g : α → β) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => f (g x)) := hf.comp hg

@[fun_prop] lemma fst (f : α → β × γ) (hf : Computable f) :
    Computable (fun x => (f x).1) := Computable.fst.comp hf

@[fun_prop] lemma snd (f : α → β × γ) (hf : Computable f) :
    Computable (fun x => (f x).2) := Computable.snd.comp hf

@[fun_prop] lemma pair (f : α → β) (g : α → γ) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => (f x, g x)) := hf.pair hg

@[fun_prop] lemma addNat : Computable (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add.to_comp

@[fun_prop] lemma mulNat : Computable (fun p : ℕ × ℕ => p.1 * p.2) := Primrec.nat_mul.to_comp

@[fun_prop] lemma subNat : Computable (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub.to_comp

@[fun_prop] lemma succNat : Computable Nat.succ := Computable.succ

@[fun_prop] lemma constAddRat : Computable (fun p : ℚ × ℚ => p.1 + p.2) := computable_rat_add

@[fun_prop] lemma constMulRat : Computable (fun p : ℚ × ℚ => p.1 * p.2) := computable_rat_mul

@[fun_prop] lemma negRat : Computable (fun q : ℚ => -q) := computable_rat_neg

@[fun_prop] lemma invRat : Computable (fun q : ℚ => q⁻¹) := computable_rat_inv

@[fun_prop] lemma absNat : Computable Int.natAbs := primrec_int_natAbs.to_comp

@[fun_prop] lemma ratNum : Computable Rat.num := computable_rat_num

@[fun_prop] lemma consList : Computable (fun p : β × List β => p.1 :: p.2) := Primrec.list_cons.to_comp

@[fun_prop] lemma appendList : Computable (fun p : List β × List β => p.1 ++ p.2) := Primrec.list_append.to_comp

@[fun_prop] lemma lengthList : Computable (fun p : List β => p.length) := Computable.list_length

@[fun_prop] lemma getDList (b : β) : Computable (fun p : List β × ℕ => p.1.getD p.2 b) :=
  (Primrec.list_getD b).to_comp

@[fun_prop] lemma valFin {n : ℕ} : Computable (fun i : Fin n => i.val) := Primrec.fin_val.to_comp

@[fun_prop] lemma appFin {n : ℕ} : Computable (fun p : (Fin n → β) × Fin n => p.1 p.2) := Computable.fin_app

@[fun_prop] lemma ofFnList {n : ℕ} (f : α → Fin n → β) (hf : ∀ i, Computable (fun a => f a i)) :
    Computable (fun a => List.ofFn (f a)) := Computable.list_ofFn hf

lemma mapList [Inhabited β] {f : α → List β} {g : α → β → γ} (hf : Computable f)
    (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (f a).map (g a)) := by
  have h := computable_foldl hf (Computable.const ([] : List γ))
    (h := fun a p => p.1 ++ [g a p.2]) (by change Computable (fun p : α × (List γ × β) => _); fun_prop)
  apply h.of_eq
  intro a
  have hh : ∀ (l : List β) (s : List γ), l.foldl (fun s b => s ++ [g a b]) s = s ++ l.map (g a) := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => intro s; simp only [List.foldl_cons, List.map_cons, ih, List.append_assoc, List.singleton_append]
  simpa using hh (f a) []

lemma flatMapList [Inhabited β] {f : α → List β} {g : α → β → List γ} (hf : Computable f)
    (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (f a).flatMap (g a)) := by
  have h := computable_foldl hf (Computable.const ([] : List γ))
    (h := fun a p => p.1 ++ g a p.2) (by change Computable (fun p : α × (List γ × β) => _); fun_prop)
  apply h.of_eq
  intro a
  have hh : ∀ (l : List β) (s : List γ), l.foldl (fun s b => s ++ g a b) s = s ++ l.flatMap (g a) := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => intro s; simp only [List.foldl_cons, List.flatMap_cons, ih, List.append_assoc]
  simpa using hh (f a) []

end BalancedTransport.Effectivity.ComputableRules
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Effectivity
open Effectivity.ComputableRules

abbrev RawInstruction := ℕ × ℕ × ℕ

abbrev RawMachine := ℕ × ℕ × ℕ × ℕ × List (List (Option RawInstruction))

abbrev RawState := ℕ × ℤ × List (ℤ × ℕ)

abbrev RawRun := RawMachine × List ℕ × RawState

def serialize (M : FiniteMachine) : RawMachine :=
  (M.states, M.symbols, M.initial.val, M.blank.val,
    (List.finRange (M.states + 1)).map fun q =>
      (List.finRange (M.symbols + 1)).map fun a =>
        (M.transition q a).map fun v => (v.state.val, v.write.val, v.move.number))

def rawBase (blank : ℕ) (w : List ℕ) (z : ℤ) : ℕ :=
  if (z.toNat : ℤ) = z then w.getD z.toNat blank else blank

def rawRead (blank : ℕ) (w : List ℕ) (writes : List (ℤ × ℕ)) (z : ℤ) : ℕ :=
  writes.foldl (fun value p => if z = p.1 then p.2 else value) (rawBase blank w z)

def rawMove (d : ℕ) : ℤ := if d = 0 then 0 else if d = 1 then -1 else 1

def rawStep (r : RawRun) : Option RawRun :=
  let m := r.1
  let w := r.2.1
  let c := r.2.2
  ((m.2.2.2.2.getD c.1 []).getD (rawRead m.2.2.2.1 w c.2.2 c.2.1) none).map
    fun v => (m, w, v.1, c.2.1 + rawMove v.2.2, c.2.2 ++ [(c.2.1, v.2.1)])

def rawInit (n : ℕ) : RawRun :=
  let p := (Encodable.decode (α := ℕ × List ℕ) n).getD (0, [])
  let m := (Encodable.decode (α := RawMachine) p.1).getD (0,0,0,0,[])
  (m, p.2, m.2.2.1, 0, [])

@[fun_prop] lemma computable_int_toNat : Computable Int.toNat := primrec_int_toNat.to_comp

@[fun_prop] lemma computable_int_ofNat : Computable (Int.ofNat : ℕ → ℤ) := primrec_int_ofNat.to_comp

@[fun_prop] lemma computable_int_add : Computable (fun p : ℤ × ℤ => p.1 + p.2) := primrec_int_add.to_comp

lemma primrec_rawBase : Primrec (fun p : ℕ × List ℕ × ℤ => rawBase p.1 p.2.1 p.2.2) := by
  unfold rawBase
  exact Primrec.ite
    (Primrec.eq.comp (primrec_int_ofNat.comp (primrec_int_toNat.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
      (primrec_int_toNat.comp (Primrec.snd.comp Primrec.snd))) Primrec.fst)
    Primrec.fst

lemma computable_rawRead : Computable (fun p : ℕ × List ℕ × List (ℤ × ℕ) × ℤ =>
    rawRead p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold rawRead
  apply Primrec.to_comp
  apply Primrec.list_foldl (h := fun (p : ℕ × List ℕ × List (ℤ × ℕ) × ℤ) (v : ℕ × (ℤ × ℕ)) =>
      if p.2.2.2 = v.2.1 then v.2.2 else v.1) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (primrec_rawBase.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)).to₂

lemma computable_rawMove : Computable rawMove := by
  unfold rawMove
  exact (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const (0:ℤ))
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
      (Primrec.const (-1:ℤ)) (Primrec.const (1:ℤ)))).to_comp

lemma computable_rawSymbol : Computable (fun r : RawRun =>
    rawRead r.1.2.2.2.1 r.2.1 r.2.2.2.2 r.2.2.2.1) := by
  have hM : Computable (fun r : RawRun => r.1) := Computable.fst
  have hw : Computable (fun r : RawRun => r.2.1) := Computable.fst.comp Computable.snd
  have hc : Computable (fun r : RawRun => r.2.2) := Computable.snd.comp Computable.snd
  have hh : Computable (fun r : RawRun => r.2.2.2.1) := Computable.fst.comp (Computable.snd.comp hc)
  have hs : Computable (fun r : RawRun => r.2.2.2.2) := Computable.snd.comp (Computable.snd.comp hc)
  have hb : Computable (fun r : RawRun => r.1.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hM)))
  exact computable_rawRead.comp
    (g := fun r : RawRun => (r.1.2.2.2.1,r.2.1,r.2.2.2.2,r.2.2.2.1))
    (hb.pair (hw.pair (hs.pair hh)))

lemma computable_rawInstruction : Computable (fun r : RawRun =>
    (r.1.2.2.2.2.getD r.2.2.1 []).getD
      (rawRead r.1.2.2.2.1 r.2.1 r.2.2.2.2 r.2.2.2.1) none) := by
  have hq : Computable (fun r : RawRun => r.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun r : RawRun => r.1.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  exact (Primrec.list_getD (none : Option RawInstruction)).to_comp.comp
    ((Primrec.list_getD ([] : List (Option RawInstruction))).to_comp.comp ht hq) computable_rawSymbol

lemma computable_rawAdvanceState : Computable (fun p : RawState × RawInstruction =>
    (p.2.1, p.1.2.1 + rawMove p.2.2.2, p.1.2.2 ++ [(p.1.2.1,p.2.2.1)])) := by
  have hh : Computable (fun p : RawState × RawInstruction => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun p : RawState × RawInstruction => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hw : Computable (fun p : RawState × RawInstruction => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hd : Computable (fun p : RawState × RawInstruction => rawMove p.2.2.2) :=
    computable_rawMove.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact (Computable.fst.comp Computable.snd).pair
    ((primrec_int_add.to_comp.comp hh hd).pair
      (Primrec.list_append.to_comp.comp hs
        (Primrec.list_cons.to_comp.comp (hh.pair hw) (Computable.const []))))

lemma computable_rawAdvance : Computable (fun p : RawRun × RawInstruction =>
    (p.1.1, p.1.2.1, p.2.1, p.1.2.2.2.1 + rawMove p.2.2.2,
      p.1.2.2.2.2 ++ [(p.1.2.2.2.1,p.2.2.1)])) := by
  have hc : Computable (fun p : RawRun × RawInstruction => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  exact (Computable.fst.comp Computable.fst).pair
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (computable_rawAdvanceState.comp (g := fun p : RawRun × RawInstruction => (p.1.2.2,p.2))
        (hc.pair Computable.snd)))

lemma computable_rawStep : Computable rawStep :=
  Computable.option_map computable_rawInstruction computable_rawAdvance.to₂

lemma computable_rawInit : Computable rawInit := by
  have hp : Computable (fun n : ℕ => (Encodable.decode (α := ℕ × List ℕ) n).getD (0,[])) :=
    Computable.option_getD Computable.decode (Computable.const _)
  have hm : Computable (fun n : ℕ =>
      (Encodable.decode (α := RawMachine) ((Encodable.decode (α := ℕ × List ℕ) n).getD (0,[])).1).getD (0,0,0,0,[])) :=
    Computable.option_getD (Computable.decode.comp (Computable.fst.comp hp)) (Computable.const _)
  exact hm.pair ((Computable.snd.comp hp).pair
    ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hm))).pair
      ((Computable.const (0 : ℤ)).pair (Computable.const []))))

@[simp] lemma rawInit_inputCode (M : FiniteMachine) (w : Input M) :
    rawInit (inputCode M w) = (serialize M, w.map Fin.val, M.initial.val, 0, []) := by
  simp [rawInit, inputCode, FiniteMachine.code, serialize]

@[simp] lemma rawMove_number (d : Recorder.Direction) : rawMove d.number =
    match d with | .stay => 0 | .left => -1 | .right => 1 := by
  cases d <;> simp [rawMove, Recorder.Direction.number]

lemma rawBase_initial (M : FiniteMachine) (w : Input M) (z : ℤ) :
    rawBase M.blank.val (w.map Fin.val) z = ((initialConfiguration M w).tape z).val := by
  have hz : ((z.toNat : ℤ) = z) ↔ 0 ≤ z := by omega
  simp only [rawBase, initialConfiguration, hz]
  split_ifs with h
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[z.toNat]? <;> rfl
  · rfl

lemma rawRead_append (b : ℕ) (w : List ℕ) (s : List (ℤ × ℕ)) (z k : ℤ) (a : ℕ) :
    rawRead b w (s ++ [(k,a)]) z = if z = k then a else rawRead b w s z := by
  simp [rawRead, List.foldl_append]

lemma serialize_instruction (M : FiniteMachine) (q : Fin (M.states+1)) (a : Fin (M.symbols+1)) :
    (((serialize M).2.2.2.2.getD q.val []).getD a.val none) =
      (M.transition q a).map (fun v => (v.state.val, v.write.val, v.move.number)) := by
  have hq : q.val < (List.finRange (M.states+1)).length := by simpa using q.isLt
  have ha : a.val < (List.finRange (M.symbols+1)).length := by simpa using a.isLt
  simp [serialize, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
    List.getElem?_eq_getElem ha]

def RawRel (M : FiniteMachine) (w : Input M) (c : TapeConfiguration M) (r : RawRun) : Prop :=
  r.1 = serialize M ∧ r.2.1 = w.map Fin.val ∧ r.2.2.1 = c.state.val ∧ r.2.2.2.1 = c.head ∧
    ∀ z, rawRead M.blank.val (w.map Fin.val) r.2.2.2.2 z = (c.tape z).val

lemma rawRel_initial (M : FiniteMachine) (w : Input M) :
    RawRel M w (initialConfiguration M w) (rawInit (inputCode M w)) := by
  rw [rawInit_inputCode]
  exact ⟨rfl,rfl,rfl,rfl, fun z => rawBase_initial M w z⟩

lemma rawStep_rel (M : FiniteMachine) (w : Input M) (c : TapeConfiguration M) (r : RawRun)
    (hr : RawRel M w c r) :
    match machineStep M c with
    | none => rawStep r = none
    | some c' => ∃ r', rawStep r = some r' ∧ RawRel M w c' r' := by
  rcases r with ⟨m,w',q,h,s⟩
  rcases hr with ⟨rfl,rfl,hq,hh,hs⟩
  dsimp at hq hh
  subst q; subst h
  have hi := serialize_instruction M c.state (c.tape c.head)
  dsimp only [rawStep]
  rw [show (serialize M).2.2.2.1 = M.blank.val from rfl, hs, hi]
  unfold machineStep
  cases hv : M.transition c.state (c.tape c.head) with
  | none => rfl
  | some v =>
    simp only [Option.map_some, rawMove_number]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro z
    rw [rawRead_append, hs]
    by_cases hz : z = c.head
    · subst z; simp
    · simp [hz]

lemma raw_respects (M : FiniteMachine) (w : Input M) :
    StateTransition.Respects (machineStep M) rawStep (RawRel M w) := by
  intro c r hr
  have h := rawStep_rel M w c r hr
  cases he : machineStep M c with
  | none => simpa [he] using h
  | some c' =>
    simp only [he] at h
    obtain ⟨r',hs,hr'⟩ := h
    exact ⟨r',hr', Relation.TransGen.single hs⟩

lemma halts_iff_eval_dom (M : FiniteMachine) (w : Input M) :
    Halts M w ↔ (StateTransition.eval (machineStep M) (initialConfiguration M w)).Dom := by
  rw [Part.dom_iff_mem]
  simp only [StateTransition.mem_eval]
  rfl

lemma raw_eval_dom (M : FiniteMachine) (w : Input M) :
    (StateTransition.eval rawStep (rawInit (inputCode M w))).Dom ↔ Halts M w := by
  exact (StateTransition.tr_eval_dom (raw_respects M w) (rawRel_initial M w)).trans
    (halts_iff_eval_dom M w).symm

lemma partrec_raw_eval : Partrec (StateTransition.eval rawStep) := by
  unfold StateTransition.eval
  apply Partrec.fix
  apply Computable.partrec
  exact (Computable.option_casesOn computable_rawStep Computable.sumInl
    (Computable.sumInr.comp Computable.snd).to₂).of_eq (fun r => by
      cases rawStep r <;> rfl)

def universalPartial (n : ℕ) : Part ℕ :=
  (StateTransition.eval rawStep (rawInit n)).map (fun _ => 0)

lemma universalPartial_partrec : Partrec universalPartial :=
  (partrec_raw_eval.comp computable_rawInit).map (Computable.const 0).to₂

lemma universalPartial_dom (M : FiniteMachine) (w : Input M) :
    (universalPartial (inputCode M w)).Dom ↔ Halts M w := raw_eval_dom M w

lemma exists_universal_code : ∃ c : Turing.ToPartrec.Code, ∀ n,
    (c.eval [n]).Dom ↔ (universalPartial n).Dom := by
  obtain ⟨c,hc⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr universalPartial_partrec)
  refine ⟨c, fun n => ?_⟩
  have h := hc ⟨[n],rfl⟩
  simpa [List.Vector.head] using congrArg Part.Dom h

end BalancedTransport.Universal
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {α : Type*} [Fintype α]

def finiteIndex (a : α) : Fin (Fintype.card α + 1) := (Fintype.equivFin α a).castSucc

def finiteUnindex (a₀ : α) (i : Fin (Fintype.card α + 1)) : α :=
  if h : i.val < Fintype.card α then (Fintype.equivFin α).symm ⟨i.val,h⟩ else a₀

@[simp] lemma finiteUnindex_index (a₀ a : α) : finiteUnindex a₀ (finiteIndex a) = a := by
  simp [finiteUnindex, finiteIndex]

lemma finiteIndex_injective : Function.Injective (finiteIndex (α := α)) :=
  fun a b h => by simpa using congrArg (finiteUnindex a) h

end BalancedTransport.Universal
end

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Inhabited Λ]
variable (P : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports P S)

def stateIndex (q : Λ) : Fin (Fintype.card {q : Λ // q ∈ S} + 1) :=
  finiteIndex (if h : q ∈ S then (⟨q,h⟩ : {q : Λ // q ∈ S}) else ⟨default,ss.1⟩)

omit [Fintype Γ] [Inhabited Γ] in
lemma stateIndex_decode {q : Λ} (hq : q ∈ S) :
    (finiteUnindex ⟨default,ss.1⟩ (stateIndex P S ss q) : {q : Λ // q ∈ S}).val = q := by
  simp [stateIndex, hq]

def postInstruction (a : Fin (Fintype.card Γ + 1)) (v : Λ × TM0.Stmt Γ) :
    Recorder.Transition (Fin (Fintype.card {q : Λ // q ∈ S} + 1)) (Fin (Fintype.card Γ + 1)) :=
  ⟨stateIndex P S ss v.1,
    (match v.2 with | .write b => finiteIndex b | .move _ => a),
    (match v.2 with | .write _ => .stay | .move .left => .left | .move .right => .right)⟩

abbrev finitePostMachine : FiniteMachine where
  states := Fintype.card {q : Λ // q ∈ S}
  symbols := Fintype.card Γ
  initial := stateIndex P S ss default
  blank := finiteIndex (default : Γ)
  transition q a := (P (finiteUnindex ⟨default,ss.1⟩ q : {q : Λ // q ∈ S}).val (finiteUnindex default a)).map
    (postInstruction P S ss a)

lemma finitePostMachine_instruction (q : Λ) (hq : q ∈ S) (a : Γ) :
    (finitePostMachine P S ss).transition (stateIndex P S ss q) (finiteIndex a) =
      (P q a).map (postInstruction P S ss (finiteIndex a)) := by
  simp [finitePostMachine, stateIndex_decode P S ss hq]

def PostRel (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss)) : Prop :=
  c.q ∈ S ∧ d.state = stateIndex P S ss c.q ∧
    ∀ i : ℤ, d.tape (d.head + i) = finiteIndex (c.Tape.nth i)

lemma post_initial_rel (w : List Γ) : PostRel P S ss (TM0.init w)
    (initialConfiguration (finitePostMachine P S ss) (w.map finiteIndex)) := by
  refine ⟨ss.1, rfl, ?_⟩
  intro i
  simp only [initialConfiguration, zero_add, TM0.init, Tape.mk₁, Tape.mk₂]
  by_cases hi : 0 ≤ i
  · rw [ite_eq_left hi, ← Int.toNat_of_nonneg hi]
    simp only [Tape.mk'_nth_nat, ListBlank.nth_mk, List.getI_eq_getElem?_getD,
      List.getElem?_map, Int.toNat_natCast]
    cases w[i.toNat]? <;> rfl
  · have hi' : i < 0 := lt_of_not_ge hi
    rw [ite_eq_right hi]
    cases i with
    | ofNat n => exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hi')
    | negSucc n =>
      change finiteIndex (default : Γ) = finiteIndex ((ListBlank.mk []).nth n)
      rw [ListBlank.nth_mk]
      rfl

lemma post_tape_head {c : TM0.Cfg Γ Λ} {d : TapeConfiguration (finitePostMachine P S ss)}
    (h : PostRel P S ss c d) : d.tape d.head = finiteIndex c.Tape.head := by
  simpa using h.2.2 0

lemma post_step (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss))
    (h : PostRel P S ss c d) :
    match TM0.step P c with
    | none => machineStep (finitePostMachine P S ss) d = none
    | some c' => ∃ d', machineStep (finitePostMachine P S ss) d = some d' ∧ PostRel P S ss c' d' := by
  have ht : (finitePostMachine P S ss).transition d.state (d.tape d.head) =
      (P c.q c.Tape.head).map (postInstruction P S ss (finiteIndex c.Tape.head)) := by
    rw [h.2.1, post_tape_head P S ss h, finitePostMachine_instruction P S ss _ h.1]
  unfold machineStep
  rw [ht]
  simp only [TM0.step]
  cases hp : P c.q c.Tape.head with
  | none => rfl
  | some v =>
    rcases v with ⟨q', act⟩
    have hq' : q' ∈ S := ss.2 hp h.1
    cases act with
    | write b =>
      simp only [Option.map_some, postInstruction]
      refine ⟨_,rfl,hq',rfl,?_⟩
      intro i
      change Function.update d.tape d.head (finiteIndex b) (d.head + 0 + i) =
        finiteIndex ((c.Tape.write b).nth i)
      simp only [Int.add_zero, Tape.write_nth]
      by_cases hi : i = 0
      · subst i; simp
      · have hi' : d.head + i ≠ d.head := by omega
        rw [ite_eq_right hi, Function.update_of_ne hi']
        exact h.2.2 i
    | move dir =>
      have hu : Function.update d.tape d.head (finiteIndex c.Tape.head) = d.tape := by
        rw [← post_tape_head P S ss h, Function.update_eq_self]
      cases dir with
      | left =>
        simp only [Option.map_some, postInstruction]
        refine ⟨_,rfl,hq',rfl,?_⟩
        intro i
        change Function.update d.tape d.head (finiteIndex c.Tape.head) (d.head + (-1) + i) =
          finiteIndex ((c.Tape.move .left).nth i)
        rw [hu, Tape.move_left_nth]
        convert h.2.2 (i-1) using 1
        congr 1
        ring
      | right =>
        simp only [Option.map_some, postInstruction]
        refine ⟨_,rfl,hq',rfl,?_⟩
        intro i
        change Function.update d.tape d.head (finiteIndex c.Tape.head) (d.head + 1 + i) =
          finiteIndex ((c.Tape.move .right).nth i)
        rw [hu, Tape.move_right_nth]
        convert h.2.2 (i+1) using 1
        congr 1
        ring

lemma post_respects : StateTransition.Respects (TM0.step P) (machineStep (finitePostMachine P S ss))
    (PostRel P S ss) := by
  intro c d hr
  have h := post_step P S ss c d hr
  cases he : TM0.step P c with
  | none => simpa [he] using h
  | some c' =>
    simp only [he] at h
    obtain ⟨d',hd,hr'⟩ := h
    exact ⟨d',hr',Relation.TransGen.single hd⟩

lemma halts_finitePostMachine (w : List Γ) :
    Halts (finitePostMachine P S ss) (w.map finiteIndex) ↔ (TM0.eval P w).Dom := by
  exact (halts_iff_eval_dom _ _).trans
    (StateTransition.tr_eval_dom (post_respects P S ss) (post_initial_rel P S ss w))

end BalancedTransport.Universal
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing PartrecToTM2
open scoped Classical

instance : Fintype K' := ⟨{.main,.rev,.aux,.stack}, by intro k; cases k <;> simp⟩

instance : Primcodable Γ' := Primcodable.ofEquiv (Fin (Fintype.card Γ')) (Fintype.equivFin Γ')

lemma trNat_rec (n : ℕ) : trNat n =
    if n = 0 then [] else (if n % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat (n / 2) := by
  have h (p : Num) : trNat (p : ℕ) =
      if (p : ℕ) = 0 then [] else
        (if (p : ℕ) % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat ((p : ℕ) / 2) := by
    cases p with
    | zero => simp [trNat,trNum]
    | pos p =>
      have hp := PosNum.to_nat_pos p
      cases p with
      | one => norm_num [trNat,trNum,trPosNum]
      | bit0 p =>
        have hp := PosNum.to_nat_pos p
        have he : ((Num.pos (PosNum.bit0 p) : Num) : ℕ) = (p : ℕ) + (p : ℕ) := rfl
        rw [he]
        have hdiv : ((p : ℕ) + (p : ℕ)) / 2 = (p : ℕ) := by omega
        have hmod : ((p : ℕ) + (p : ℕ)) % 2 = 0 := by omega
        rw [ite_eq_right (by omega),ite_eq_left hmod,hdiv]
        change trNum (((Num.pos (PosNum.bit0 p) : Num) : ℕ) : Num) =
          Γ'.bit0 :: trNum (((Num.pos p : Num) : ℕ) : Num)
        rw [Num.of_to_nat, Num.of_to_nat]
        rfl
      | bit1 p =>
        have hp := PosNum.to_nat_pos p
        have he : ((Num.pos (PosNum.bit1 p) : Num) : ℕ) = (p : ℕ) + (p : ℕ) + 1 := rfl
        rw [he]
        have hdiv : ((p : ℕ) + (p : ℕ) + 1) / 2 = (p : ℕ) := by omega
        have hmod : ((p : ℕ) + (p : ℕ) + 1) % 2 ≠ 0 := by omega
        rw [ite_eq_right (by omega),ite_eq_right hmod,hdiv]
        change trNum (((Num.pos (PosNum.bit1 p) : Num) : ℕ) : Num) =
          Γ'.bit1 :: trNum (((Num.pos p : Num) : ℕ) : Num)
        rw [Num.of_to_nat, Num.of_to_nat]
        rfl
  simpa using h (n : Num)

lemma computable_trNat : Computable trNat := by
  let g : Unit → List (List Γ') → Option (List Γ') := fun _ l =>
    some (if l.length = 0 then [] else
      (if l.length % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: (l.getD (l.length / 2) []))
  have hg : Primrec₂ g := by
    change Primrec (fun z : Unit × List (List Γ') => g z.1 z.2)
    dsimp only [g]
    apply Primrec.option_some.comp
    apply Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0))
      (Primrec.const [])
    apply Primrec.list_cons.comp
    · exact Primrec.ite (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
        (Primrec.const 0)) (Primrec.const Γ'.bit0) (Primrec.const Γ'.bit1)
    · exact (Primrec.list_getD ([] : List Γ')).comp Primrec.snd
        (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
  have hh := Primrec.nat_strong_rec (fun (_ : Unit) => trNat) hg (by
    intro u n
    dsimp [g]
    simp only [List.length_map,List.length_range]
    by_cases hn : n = 0
    · subst n; simp
    · rw [ite_eq_right hn, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega : n / 2 < n)]
      simp only [Option.map_some,Option.getD_some]
      rw [trNat_rec n,ite_eq_right hn])
  exact hh.to_comp.comp (Computable.const ()) Computable.id

abbrev StackAlphabet := TM2to1.Γ' K' (fun _ => Γ')

instance : Primcodable (Bool × (K' → Option Γ')) :=
  Primcodable.ofEquiv (Fin (Fintype.card StackAlphabet)) (Fintype.equivFin StackAlphabet)

instance : Primcodable StackAlphabet :=
  (inferInstance : Primcodable (Bool × (K' → Option Γ')))

lemma computable_trInit : Computable (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main) := by
  have hm : Computable (fun L : List Γ' => L.reverse.map
      (fun a => ((false, Function.update (fun _ : K' => (none : Option Γ')) K'.main (some a)) : StackAlphabet))) :=
    (Primrec.list_map Primrec.list_reverse ((Primrec.dom_finite
      (fun a : Γ' => ((false, Function.update (fun _ : K' => (none : Option Γ')) K'.main (some a)) : StackAlphabet))).comp Primrec.snd).to₂).to_comp
  exact Primrec.list_cons.to_comp.comp
    ((Primrec.dom_finite (fun a : StackAlphabet => ((true,a.2) : StackAlphabet))).to_comp.comp
      (Primrec.list_headI.to_comp.comp hm))
    (Primrec.list_tail.to_comp.comp hm)

lemma computable_translatedInput : Computable (fun n : ℕ =>
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n])).map finiteIndex) := by
  have ht : Computable (fun n : ℕ => trList [n]) :=
    Primrec.list_append.to_comp.comp computable_trNat (Computable.const [Γ'.cons])
  exact (Primrec.list_map Primrec.id ((Primrec.dom_finite finiteIndex).comp Primrec.snd).to₂).to_comp.comp
    (computable_trInit.comp ht)

end BalancedTransport.Universal
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing PartrecToTM2 StateTransition
open scoped Classical

theorem finite_machine_of_code (c : ToPartrec.Code) :
    ∃ M : FiniteMachine, ∃ δ : ℕ → Input M,
      Computable δ ∧ ∀ n, Halts M (δ n) ↔ (c.eval [n]).Dom := by
  let : Inhabited PartrecToTM2.Λ' := ⟨trNormal c Cont'.halt⟩
  let P₁ := TM2to1.tr PartrecToTM2.tr
  let S₁ := TM2to1.trSupp PartrecToTM2.tr (codeSupp c Cont'.halt)
  have ss₁ : TM1.Supports P₁ S₁ := TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports c Cont'.halt)
  let P₀ := TM1to0.tr P₁
  let S₀ := TM1to0.trStmts P₁ S₁
  have ss₀ : TM0.Supports P₀ S₀ := TM1to0.tr_supports P₁ ss₁
  let δ : ℕ → List (Fin (Fintype.card StackAlphabet + 1)) := fun n =>
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n])).map
      (finiteIndex (α := StackAlphabet))
  refine ⟨finitePostMachine P₀ S₀ ss₀, δ, computable_translatedInput, ?_⟩
  intro n
  rw [halts_finitePostMachine, TM1to0.tr_eval]
  refine (TM2to1.tr_eval_dom PartrecToTM2.tr K'.main (trList [n])).trans ?_
  have hi : (TM2.init K'.main (trList [n]) : TM2.Cfg (fun _ : K' => Γ') PartrecToTM2.Λ' (Option Γ')) =
      PartrecToTM2.init c [n] := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> simp [K'.elim,Function.update]
  change (eval (TM2.step PartrecToTM2.tr) (TM2.init K'.main (trList [n]))).Dom ↔ _
  rw [hi, PartrecToTM2.tr_eval]
  rfl

theorem exists_universal_machine :
    ∃ N : FiniteMachine, ∃ δ : ℕ → Input N,
      Computable δ ∧ ∀ M w, Halts N (δ (inputCode M w)) ↔ Halts M w := by
  obtain ⟨c,hc⟩ := exists_universal_code
  obtain ⟨N,δ,hδ,hh⟩ := finite_machine_of_code c
  exact ⟨N,δ,hδ, fun M w => (hh _).trans ((hc _).trans (universalPartial_dom M w))⟩

end BalancedTransport.Universal
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma exp_difference_bound {x y T : ℝ} (hx : x ≤ T) (hy : y ≤ T) :
    |Real.exp x - Real.exp y| ≤ Real.exp T * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Iic T).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => Real.differentiableAt_exp) (fun z hz => by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr hz) hy hx

lemma exp_nat_bound (n : ℕ) : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
  rw [← mul_one (n : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _

lemma clipped_inverse_bound {x q c : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    |(max c q)⁻¹ - x⁻¹| ≤ c⁻¹ ^ 2 * |q - x| := by
  have hm : c ≤ max c q := le_max_left _ _
  have hmp := hc.trans_le hm
  have hxp := hc.trans_le hx
  have hdist : |max c q - x| ≤ |q - x| := by
    rcases le_total c q with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_of_nonpos (sub_nonpos.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr (h.trans hx))]
      linarith
  have hlow : c*c ≤ max c q * x := mul_le_mul hm hx hc.le hmp.le
  calc
    |(max c q)⁻¹ - x⁻¹| = |max c q - x| / (max c q * x) := by
      rw [inv_sub_inv hmp.ne' hxp.ne', abs_div,
        abs_of_pos (mul_pos hmp hxp), abs_sub_comm]
    _ ≤ |q - x| / (c*c) := div_le_div₀ (abs_nonneg _) hdist (mul_pos hc hc) hlow
    _ = c⁻¹ ^ 2 * |q - x| := by rw [div_eq_mul_inv, mul_inv_rev]; ring

structure RegisterEstimate (p : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ)) : Prop where
  magnitude : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ)
  accuracy : ∀ j, |(q.getD j 0 : ℝ) - s.getD j 0| ≤ ((b.getD j (0,0)).2 : ℝ) * error p

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma estimate (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p C : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hb : RegisterEstimate p s q b) (hv : Valid o s) :
    |real d o (fun i => (x i : ℝ)) s| ≤ ((bound o C b).1 : ℝ) ∧
    |(rational d o x p q : ℝ) - real d o (fun i => (x i : ℝ)) s| ≤
      ((bound o C b).2 : ℝ) * error p := by
  rcases o with ⟨j,r,a,b'⟩
  have hA := hb.magnitude a
  have hB := hb.magnitude b'
  have hE := hb.accuracy a
  have hF := hb.accuracy b'
  have herr := error_nonneg p
  have herr1 := error_le_one p
  have hsize : |(q.getD a 0 : ℝ)| ≤ ((b.getD a (0,0)).1 : ℝ) +
      ((b.getD a (0,0)).2 : ℝ) := by
    calc
      _ ≤ |(q.getD a 0 : ℝ) - s.getD a 0| + |s.getD a 0| :=
        by simpa only [sub_add_cancel] using abs_add_le ((q.getD a 0 : ℝ) - s.getD a 0) (s.getD a 0)
      _ ≤ ((b.getD a (0,0)).2 : ℝ) * error p + ((b.getD a (0,0)).1 : ℝ) :=
        add_le_add hE hA
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (b.getD a (0,0)).2 (α := ℝ)]
  fin_cases j <;> simp only [real, rational, rationalCase, bound, boundCase, tag, rat, left, right, Valid] at hv ⊢
  · exact ⟨rat_abs_le_num r, by simp⟩
  · exact ⟨hi _, by simp⟩
  · constructor
    · simpa only [Nat.cast_add] using (abs_add_le _ _).trans (add_le_add hA hB)
    · push_cast
      have he : (q.getD a 0 : ℝ) + (q.getD b' 0 : ℝ) - (s.getD a 0 + s.getD b' 0) =
          ((q.getD a 0 : ℝ) - s.getD a 0) + ((q.getD b' 0 : ℝ) - s.getD b' 0) := by ring
      rw [he, add_mul]
      exact (abs_add_le _ _).trans (add_le_add hE hF)
  · constructor
    · simpa only [Nat.cast_mul, abs_mul] using
        mul_le_mul hA hB (abs_nonneg _) (by positivity)
    · push_cast
      have he : (q.getD a 0 : ℝ) * (q.getD b' 0 : ℝ) - s.getD a 0 * s.getD b' 0 =
          (q.getD a 0 : ℝ) * ((q.getD b' 0 : ℝ) - s.getD b' 0) +
          s.getD b' 0 * ((q.getD a 0 : ℝ) - s.getD a 0) := by ring
      rw [he]
      calc
        _ ≤ |(q.getD a 0 : ℝ)| * |(q.getD b' 0 : ℝ) - s.getD b' 0| +
            |s.getD b' 0| * |(q.getD a 0 : ℝ) - s.getD a 0| := by
          simpa only [abs_mul] using abs_add_le
            ((q.getD a 0 : ℝ) * ((q.getD b' 0 : ℝ) - s.getD b' 0))
            (s.getD b' 0 * ((q.getD a 0 : ℝ) - s.getD a 0))
        _ ≤ (((b.getD a (0,0)).1 : ℝ) + (b.getD a (0,0)).2) *
            ((b.getD b' (0,0)).2 * error p) +
            (b.getD b' (0,0)).1 * ((b.getD a (0,0)).2 * error p) :=
          add_le_add (mul_le_mul hsize hF (abs_nonneg _) (by positivity))
            (mul_le_mul hB hE (abs_nonneg _) (by positivity))
        _ = _ := by ring
  · constructor
    · simpa only [abs_neg] using hA
    · simpa only [Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hE
  · have hh := hv rfl
    have hpos : (0 : ℝ) < ((b' + 1 : ℕ) : ℝ)⁻¹ := by positivity
    constructor
    · rw [abs_inv, abs_of_pos (hpos.trans_le hh)]
      have h := inv_anti₀ hpos hh
      simpa only [inv_inv] using h
    · push_cast
      have hh' := clipped_inverse_bound (q := (q.getD a 0 : ℝ)) hpos hh
      simp only [inv_inv] at hh'
      have hcast : max ((b' : ℝ) + 1)⁻¹ (q.getD a 0 : ℝ) =
          max (((b'+1 : ℕ) : ℝ)⁻¹) (q.getD a 0 : ℝ) := by norm_cast
      rw [hcast]
      calc
        _ ≤ (((b'+1 : ℕ) : ℝ) ^ 2) * |(q.getD a 0 : ℝ) - s.getD a 0| := hh'
        _ ≤ (((b'+1 : ℕ) : ℝ) ^ 2) * ((b.getD a (0,0)).2 * error p) :=
          mul_le_mul_of_nonneg_left hE (sq_nonneg _)
        _ = _ := by push_cast; ring
  · constructor
    · exact rhoJet_bound_computable _ _
    · have hL := (rhoJet_lipschitz a).dist_le_mul (q.getD b' 0 : ℝ) (s.getD b' 0)
      simp only [Real.dist_eq, NNReal.coe_natCast] at hL
      calc
        _ ≤ |(rhoApprox a (q.getD b' 0) p : ℝ) - rhoJet a (q.getD b' 0 : ℝ)| +
            |rhoJet a (q.getD b' 0 : ℝ) - rhoJet a (s.getD b' 0)| := abs_sub_le _ _ _
        _ ≤ error p + (rhoBound (a + 1) 0 : ℝ) * |(q.getD b' 0 : ℝ) - s.getD b' 0| :=
          add_le_add (rhoApprox_spec _ _ _) hL
        _ ≤ error p + (rhoBound (a + 1) 0 : ℝ) * ((b.getD b' (0,0)).2 * error p) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)) _
        _ = _ := by push_cast; ring
  · constructor
    · rw [abs_of_pos (Real.exp_pos _), Nat.cast_pow, Nat.cast_ofNat]
      exact (Real.exp_le_exp.mpr (le_abs_self _ |>.trans hA)).trans (exp_nat_bound _)
    · have hL := exp_difference_bound (le_abs_self _ |>.trans hsize)
        ((le_abs_self _ |>.trans hA).trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
      have hL' : |Real.exp (q.getD a 0 : ℝ) - Real.exp (s.getD a 0)| ≤
          (3 : ℝ)^((b.getD a (0,0)).1 + (b.getD a (0,0)).2) *
            ((b.getD a (0,0)).2 * error p) := by
        have hh : Real.exp ((b.getD a (0,0)).1 + (b.getD a (0,0)).2) ≤
            (3 : ℝ) ^ ((b.getD a (0,0)).1 + (b.getD a (0,0)).2) := by
          simpa only [Nat.cast_add] using exp_nat_bound ((b.getD a (0,0)).1 + (b.getD a (0,0)).2)
        exact hL.trans (mul_le_mul hh hE (abs_nonneg _) (by positivity))
      calc
        _ ≤ |(expApprox (q.getD a 0) p : ℝ) - Real.exp (q.getD a 0 : ℝ)| +
            |Real.exp (q.getD a 0 : ℝ) - Real.exp (s.getD a 0)| := abs_sub_le _ _ _
        _ ≤ error p + (3 : ℝ)^((b.getD a (0,0)).1 + (b.getD a (0,0)).2) *
            ((b.getD a (0,0)).2 * error p) := add_le_add (expApprox_spec _ _) hL'
        _ = _ := by push_cast; ring
  · change (|if 0 < r then Real.log (r : ℝ) else 0| ≤ ↑(r.num.natAbs + r⁻¹.num.natAbs)) ∧
      (|(logApprox r p : ℝ) - (if 0 < r then Real.log (r : ℝ) else 0)| ≤ ((1 : ℕ) : ℝ) * error p)
    by_cases hr : 0 < r
    · rw [ite_eq_left hr]
      exact ⟨log_abs_bound hr, by simpa using logApprox_spec hr p⟩
    · rw [ite_eq_right hr]
      exact ⟨by simpa only [abs_zero] using
        (Nat.cast_nonneg (r.num.natAbs + r⁻¹.num.natAbs) (α := ℝ)),
        by simp [logApprox, hr, error_nonneg]⟩

end BalancedTransport.Effectivity.NumericOp
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma magnitude (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (C : ℕ) (s : List ℝ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |x i| ≤ C) (hb : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ))
    (hv : Valid o s) : |real d o x s| ≤ ((bound o C b).1 : ℝ) := by
  rcases o with ⟨j,r,a,b'⟩
  have hA := hb a
  have hB := hb b'
  fin_cases j <;>
    dsimp +instances only [real, bound, boundCase, tag, rat, left, right, Valid] at hv ⊢
  · exact rat_abs_le_num r
  · exact hi _
  · simpa only [Nat.cast_add] using (abs_add_le _ _).trans (add_le_add hA hB)
  · simpa only [Nat.cast_mul, abs_mul] using mul_le_mul hA hB (abs_nonneg _) (by positivity)
  · simpa only [abs_neg] using hA
  · have hh := hv rfl
    have hpos : (0 : ℝ) < ((b' + 1 : ℕ) : ℝ)⁻¹ := by positivity
    rw [abs_inv, abs_of_pos (hpos.trans_le hh)]
    simpa only [inv_inv] using inv_anti₀ hpos hh
  · exact rhoJet_bound_computable _ _
  · rw [abs_of_pos (Real.exp_pos _), Nat.cast_pow, Nat.cast_ofNat]
    exact (Real.exp_le_exp.mpr (le_abs_self _ |>.trans hA)).trans (exp_nat_bound _)
  · split_ifs with hr
    · exact log_abs_bound hr
    · simpa only [abs_zero] using (Nat.cast_nonneg (r.num.natAbs + r⁻¹.num.natAbs) (α := ℝ))

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def realFrom (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) : List ℝ :=
  p.foldl (fun s o => o.real d x s :: s) s

def rationalFrom (p : NumericProgram) (x : Fin d → ℚ) (n : ℕ) (s : List ℚ) : List ℚ :=
  p.foldl (fun s o => o.rational d x n s :: s) s

def boundFrom (p : NumericProgram) (C : ℕ) (s : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  p.foldl (fun s o => o.bound C s :: s) s

def ValidFrom (x : Fin d → ℝ) : NumericProgram → List ℝ → Prop
  | [], _ => True
  | o :: p, s => o.Valid s ∧ ValidFrom x p (o.real d x s :: s)

def Valid (p : NumericProgram) (x : Fin d → ℝ) : Prop := ValidFrom x p []

def real (p : NumericProgram) (x : Fin d → ℝ) : ℝ := (p.realFrom x []).getD 0 0

def bound (p : NumericProgram) (C : ℕ) : ℕ × ℕ := (p.boundFrom C []).getD 0 (0,0)

def approximation (p : NumericProgram) (C : ℕ) (x : Fin d → ℚ) (n : ℕ) : ℚ :=
  (p.rationalFrom x (n + (p.bound C).2) []).getD 0 0

lemma boundFrom_estimate (p : NumericProgram) (x : Fin d → ℚ) (s : List ℝ)
    (q : List ℚ) (b : List (ℕ × ℕ)) (n C : ℕ) (hi : ∀ i, |(x i : ℝ)| ≤ C)
    (hh : RegisterEstimate n s q b) (hv : p.ValidFrom (fun i => (x i : ℝ)) s) :
    RegisterEstimate n (p.realFrom (fun i => (x i : ℝ)) s) (p.rationalFrom x n q)
      (p.boundFrom C b) := by
  induction p generalizing s q b with
  | nil => exact hh
  | cons o p ih =>
    apply ih _ _ _ ?_ hv.2
    have hb := o.estimate d x n C s q b hi hh hv.1
    constructor
    · intro j
      cases j with
      | zero => exact hb.1
      | succ j => exact hh.magnitude j
    · intro j
      cases j with
      | zero => exact hb.2
      | succ j => exact hh.accuracy j

lemma boundFrom_magnitude (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ)
    (b : List (ℕ × ℕ)) (C : ℕ) (hi : ∀ i, |x i| ≤ C)
    (hh : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ))
    (hv : p.ValidFrom x s) :
    ∀ j, |(p.realFrom x s).getD j 0| ≤ (((p.boundFrom C b).getD j (0,0)).1 : ℝ) := by
  induction p generalizing s b with
  | nil => exact hh
  | cons o p ih =>
    apply ih _ _ ?_ hv.2
    intro j
    cases j with
    | zero => exact o.magnitude d x C s b hi hh hv.1
    | succ j => exact hh j

lemma approximation_spec (p : NumericProgram) (C : ℕ) (x : Fin d → ℚ) (n : ℕ)
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hv : p.Valid (fun i => (x i : ℝ))) :
    |(p.approximation C x n : ℝ) - p.real (fun i => (x i : ℝ))| ≤ error n := by
  have hb := p.boundFrom_estimate x [] [] [] (n + (p.bound C).2) C hi
    ⟨by simp, by simp⟩ hv
  exact (hb.accuracy 0).trans (nat_mul_error_shift _ _)

lemma magnitude (p : NumericProgram) (C : ℕ) (x : Fin d → ℝ)
    (hi : ∀ i, |x i| ≤ C) (hv : p.Valid x) : |p.real x| ≤ ((p.bound C).1 : ℝ) :=
  p.boundFrom_magnitude x [] [] C hi (by simp) hv 0

lemma computable_rationalStep (d : ℕ) [NeZero d] :
    Computable (fun z : (NumericProgram × (Fin d → ℚ) × ℕ × List ℚ) × (List ℚ × NumericOp) =>
      z.2.2.rational d z.1.2.1 z.1.2.2.1 z.2.1 :: z.2.1) := by
  let A := NumericProgram × (Fin d → ℚ) × ℕ × List ℚ
  have ho : Computable (fun z : A × (List ℚ × NumericOp) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hx : Computable (fun z : A × (List ℚ × NumericOp) => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hp : Computable (fun z : A × (List ℚ × NumericOp) => z.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hs : Computable (fun z : A × (List ℚ × NumericOp) => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hh := (NumericOp.computable_rational d).comp (ho.pair (hx.pair (hp.pair hs)))
  exact Primrec.list_cons.to_comp.comp hh hs

lemma computable_rationalFrom (d : ℕ) [NeZero d] :
    Computable (fun z : NumericProgram × (Fin d → ℚ) × ℕ × List ℚ =>
      rationalFrom z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let A := NumericProgram × (Fin d → ℚ) × ℕ × List ℚ
  have hf : Computable (fun z : A => z.1) := Computable.fst
  have hg : Computable (fun z : A => z.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact computable_foldl hf hg (computable_rationalStep d).to₂

lemma computable_boundStep : Computable
    (fun z : (NumericProgram × ℕ × List (ℕ × ℕ)) × (List (ℕ × ℕ) × NumericOp) =>
      z.2.2.bound z.1.2.1 z.2.1 :: z.2.1) := by
  let A := NumericProgram × ℕ × List (ℕ × ℕ)
  have ho : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hC : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hh := NumericOp.computable_bound.comp (ho.pair (hC.pair hs))
  exact Primrec.list_cons.to_comp.comp hh hs

lemma computable_boundFrom : Computable
    (fun z : NumericProgram × ℕ × List (ℕ × ℕ) => boundFrom z.1 z.2.1 z.2.2) := by
  let A := NumericProgram × ℕ × List (ℕ × ℕ)
  have hf : Computable (fun z : A => z.1) := Computable.fst
  have hg : Computable (fun z : A => z.2.2) := Computable.snd.comp Computable.snd
  exact computable_foldl hf hg computable_boundStep.to₂

lemma computable_bound : Computable₂ bound := by
  exact ((Primrec.list_getD (0,0)).to_comp.comp
    (computable_boundFrom.comp (Computable.fst.pair (Computable.snd.pair (Computable.const []))))
    (Computable.const 0))

lemma computable_approximation (d : ℕ) [NeZero d] : Computable
    (fun z : NumericProgram × ℕ × (Fin d → ℚ) × ℕ =>
      approximation z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have herr : Computable (fun z : NumericProgram × ℕ × (Fin d → ℚ) × ℕ => (z.1.bound z.2.1).2) := Computable.snd.comp (computable_bound.comp Computable.fst (Computable.fst.comp Computable.snd))
  exact (Primrec.list_getD (0 : ℚ)).to_comp.comp
    ((computable_rationalFrom d).comp (Computable.fst.pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        ((Primrec.nat_add.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)) herr).pair
          (Computable.const []))))) (Computable.const 0)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

def differential (k : Fin d) (o : NumericOp) (s v : ℕ → ℝ) : ℝ :=
  let a := o.left
  let b := o.right
  match o.tag with
  | 0 => 0
  | 1 => if Fin.ofNat d a = k then 1 else 0
  | 2 => v a + v b
  | 3 => v a * s b + s a * v b
  | 4 => -v a
  | 5 => -(v a * (s a)⁻¹ ^ 2)
  | 6 => rhoJet (a+1) (s b) * v b
  | 7 => Real.exp (s a) * v a
  | 8 => 0

lemma hasDerivAt (k : Fin d) (o : NumericOp) (x : ℝ → Fin d → ℝ)
    (s : ℝ → List ℝ) (v : ℕ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (v a) t)
    (hv : o.Valid (s t)) :
    HasDerivAt (fun t => o.real d (x t) (s t))
      (o.differential d k (fun a => (s t).getD a 0) v) t := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> dsimp only [real, differential, tag, rat, left, right, Valid] at hv ⊢
  · exact hasDerivAt_const t _
  · exact hx _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · have hh : (s t).getD a 0 ≠ 0 := ne_of_gt ((by positivity : (0 : ℝ) < ((b+1 : ℕ) : ℝ)⁻¹).trans_le (hv rfl))
    apply HasDerivAt.congr_deriv ((hs a).inv hh)
    simp only [div_eq_mul_inv, inv_pow, neg_mul]
  · exact (rhoJet_hasDerivAt a ((s t).getD b 0)).comp t (hs b)
  · simpa only [mul_comm] using (hs a).exp
  · exact hasDerivAt_const t _

def dualCase (k : Fin d) (j : Fin 9) (o : NumericOp) : NumericProgram :=
  let a := o.left
  let b := o.right
  let z : NumericOp := (0,0,0,0)
  match j with
  | 0 => [o,z,z,z,z]
  | 1 => [o,z,z,z,(0,(if Fin.ofNat d a = k then 1 else 0),0,0)]
  | 2 => [(2,0,5*a+4,5*b+4),z,z,z,(2,0,5*a+4,5*b+4)]
  | 3 => [(3,0,5*a+4,5*b+4),(3,0,5*a+1,5*b+5),
      (3,0,5*a+6,5*b+2),z,(2,0,2,1)]
  | 4 => [(4,0,5*a+4,0),z,z,z,(4,0,5*a+4,0)]
  | 5 => [(5,0,5*a+4,b),z,(3,0,1,1),(3,0,5*a+3,0),(4,0,0,0)]
  | 6 => [(6,0,a,5*b+4),(6,0,a+1,5*b+5),z,z,(3,0,2,5*b+4)]
  | 7 => [(7,0,5*a+4,0),z,z,z,(3,0,3,5*a+4)]
  | 8 => [o,z,z,z,z]

def dual (k : Fin d) (o : NumericOp) : NumericProgram := dualCase d k o.tag o

lemma dual_drop (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (q : List ℝ) :
    ((o.dual d k).realFrom x q).drop 5 = q := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, tag]

lemma dual_value (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 4 0 = o.real d x s := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, real, tag, rat, left, right, h]

lemma dual_differential (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 0 0 =
      o.differential d k (fun a => s.getD a 0) (fun a => q.getD (5*a) 0) := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.realFrom, real, differential, tag, rat, left, right,
      Nat.add_assoc, h, pow_two]
  change (((if Fin.ofNat d a = k then 1 else 0) : ℚ) : ℝ) =
    (if Fin.ofNat d a = k then 1 else 0)
  by_cases hh : Fin.ofNat d a = k <;>
    simp only [hh, ite_true, ite_false, Rat.cast_one, Rat.cast_zero]

lemma dual_valid (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : o.Valid s) :
    (o.dual d k).ValidFrom x q := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ValidFrom, Valid, real, tag, rat, left, right, h] at hv ⊢
  exact hv

lemma differentiableAt (o : NumericOp) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : o.Valid (s x)) : DifferentiableAt ℝ (fun y => o.real d y (s y)) x := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> dsimp only [real, tag, rat, left, right, Valid] at hv ⊢
  · exact differentiableAt_const _
  · exact (differentiable_apply _).differentiableAt
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · have hh : (s x).getD a 0 ≠ 0 := ne_of_gt ((by positivity : (0 : ℝ) < ((b+1 : ℕ) : ℝ)⁻¹).trans_le (hv rfl))
    exact (hs a).inv hh
  · exact (rhoJet_hasDerivAt a _).differentiableAt.comp x (hs b)
  · exact (hs a).exp
  · exact differentiableAt_const _

end BalancedTransport.Effectivity.NumericOp
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

def Scoped (o : NumericOp) (n : ℕ) : Prop :=
  let a := o.left
  let b := o.right
  match o.tag with
  | 0 => True
  | 1 => True
  | 2 => a < n ∧ b < n
  | 3 => a < n ∧ b < n
  | 4 => a < n
  | 5 => a < n
  | 6 => b < n
  | 7 => a < n
  | 8 => True

lemma real_append (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s q : List ℝ) (hs : o.Scoped s.length) : o.real d x (s ++ q) = o.real d x s := by
  have he (i : ℕ) (hi : i < s.length) : (s ++ q).getD i 0 = s.getD i 0 := by
    simp [List.getD, List.getElem?_append_left hi]
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp only [Scoped, real, tag, rat, left, right] at hs ⊢
  all_goals first | rfl | exact he _ hs | simp only [he _ hs] | simp only [he _ hs.1, he _ hs.2]

lemma valid_append (o : NumericOp) (s q : List ℝ) (hs : o.Scoped s.length) :
    o.Valid (s ++ q) ↔ o.Valid s := by
  by_cases ht : o.tag = 5
  · have hh : o.left < s.length := by unfold Scoped at hs; rw [ht] at hs; exact hs
    simp only [Valid, ht, forall_const]
    simp only [List.getD, List.getElem?_append_left hh]
  · simp [Valid, ht]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def ScopedFrom : NumericProgram → ℕ → Prop
  | [], _ => True
  | o::p, n => o.Scoped n ∧ ScopedFrom p (n+1)

def Closed (p : NumericProgram) : Prop := p.ScopedFrom 0

lemma realFrom_length (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (realFrom p x s).length = p.length + s.length := by
  induction p generalizing s with
  | nil => simp [realFrom]
  | cons o p ih => simpa [realFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (o.real d x s :: s)

lemma realFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : realFrom p x (s ++ q) = realFrom p x s ++ q := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change realFrom p x (o.real d x (s ++ q) :: (s ++ q)) =
      realFrom p x (o.real d x s :: s) ++ q
    rw [o.real_append d x s q hs.1]
    exact ih (o.real d x s :: s) hs.2

lemma validFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : ValidFrom x p (s ++ q) ↔ ValidFrom x p s := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change o.Valid (s ++ q) ∧ ValidFrom x p (o.real d x (s ++ q) :: (s ++ q)) ↔
      o.Valid s ∧ ValidFrom x p (o.real d x s :: s)
    rw [o.valid_append s q hs.1, o.real_append d x s q hs.1]
    exact and_congr_right (fun _ => ih (o.real d x s :: s) hs.2)

lemma realFrom_empty_append (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    realFrom p x s = realFrom p x [] ++ s :=
  realFrom_append p x [] s hp

lemma validFrom_of_closed (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    ValidFrom x p s ↔ p.Valid x := p.validFrom_append x [] s hp

lemma realFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).realFrom x s = q.realFrom x (realFrom p x s) := List.foldl_append

lemma validFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).ValidFrom x s ↔ ValidFrom x p s ∧ q.ValidFrom x (realFrom p x s) := by
  induction p generalizing s with
  | nil => simp [ValidFrom, realFrom]
  | cons o p ih => simpa only [List.cons_append, ValidFrom, realFrom,
      List.foldl_cons, and_assoc] using and_congr_right (fun _ => ih _)

lemma scopedFrom_mono (p : NumericProgram) {n m : ℕ} (hnm : n ≤ m) :
    p.ScopedFrom n → p.ScopedFrom m := by
  intro h
  induction p generalizing n m with
  | nil => trivial
  | cons o p ih =>
    refine ⟨?_, ih (Nat.add_le_add_right hnm 1) h.2⟩
    rcases o with ⟨j,r,a,b⟩
    have ho := h.1
    fin_cases j <;> dsimp only [NumericOp.Scoped, NumericOp.tag, NumericOp.rat,
      NumericOp.left, NumericOp.right] at ho ⊢
    all_goals first | trivial | exact ho.trans_le hnm | exact ⟨ho.1.trans_le hnm,ho.2.trans_le hnm⟩

lemma scopedFrom_concat (p q : NumericProgram) (n : ℕ) :
    (p ++ q).ScopedFrom n ↔ p.ScopedFrom n ∧ q.ScopedFrom (n+p.length) := by
  induction p generalizing n with
  | nil => simp [ScopedFrom]
  | cons o p ih =>
    simp only [List.cons_append, ScopedFrom, List.length_cons]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1, and_assoc]

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_register (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s : List ℝ) (a : ℕ) :
    ((o.dual d k).realFrom x s).getD (5+a) 0 = s.getD a 0 := by
  have h := congrArg (fun l : List ℝ => l.getD a 0) (o.dual_drop d k x s)
  simpa [List.getD, List.getElem?_drop] using h

lemma dual_length (k : Fin d) (o : NumericOp) : (o.dual d k).length = 5 := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> rfl

lemma dual_scoped (k : Fin d) (o : NumericOp) {n : ℕ} (h : o.Scoped n) :
    (o.dual d k).ScopedFrom (5*n) := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ScopedFrom, Scoped, tag, left, right] at h ⊢
  all_goals omega

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def jetStep (k : Fin d) (p : NumericProgram) : NumericProgram :=
  p.flatMap (NumericOp.dual d k)

lemma jetStep_length (k : Fin d) (p : NumericProgram) : (p.jetStep k).length = 5*p.length := by
  induction p with
  | nil => rfl
  | cons o p ih => simp only [jetStep, List.flatMap_cons, List.length_append,
      NumericOp.dual_length, List.length_cons] at ih ⊢; omega

lemma jetStep_scoped (k : Fin d) (p : NumericProgram) {n : ℕ} (h : p.ScopedFrom n) :
    (p.jetStep k).ScopedFrom (5*n) := by
  induction p generalizing n with
  | nil => trivial
  | cons o p ih =>
    rw [jetStep, List.flatMap_cons, scopedFrom_concat, NumericOp.dual_length]
    exact ⟨o.dual_scoped d k h.1, by simpa [jetStep, Nat.mul_add] using ih h.2⟩

lemma jetStep_closed (k : Fin d) (p : NumericProgram) (h : p.Closed) :
    (p.jetStep k).Closed := p.jetStep_scoped k h

lemma jetStep_validFrom (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ)
    (s q : List ℝ) (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : p.ValidFrom x s) :
    (p.jetStep k).ValidFrom x q ∧
      ∀ a, ((p.jetStep k).realFrom x q).getD (5*a+4) 0 = (p.realFrom x s).getD a 0 := by
  induction p generalizing s q with
  | nil => exact ⟨trivial, h⟩
  | cons o p ih =>
    have ho := o.dual_valid d k x s q h hv.1
    have hh (a : ℕ) : ((o.dual d k).realFrom x q).getD (5*a+4) 0 =
        (o.real d x s :: s).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k x s q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5,
          List.getD_cons_succ] using (o.dual_register d k x q (5*a+4)).trans (h a)
    have hi := ih _ _ hh hv.2
    refine ⟨?_, ?_⟩
    · exact (validFrom_concat _ _ x q).mpr ⟨ho, hi.1⟩
    · simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
        List.foldl_cons, List.foldl_append] using hi.2

lemma jetStep_valid (k : Fin d) (p : NumericProgram) {x : Fin d → ℝ} (hv : p.Valid x) :
    (p.jetStep k).Valid x := (p.jetStep_validFrom k x [] [] (by simp) hv).1

lemma jetStep_hasDerivAtFrom (k : Fin d) (p : NumericProgram)
    (x : ℝ → Fin d → ℝ) (s : ℝ → List ℝ) (q : List ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (h : ∀ a, q.getD (5*a+4) 0 = (s t).getD a 0)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (q.getD (5*a) 0) t)
    (hv : p.ValidFrom (x t) (s t)) :
    ∀ a, HasDerivAt (fun t => (p.realFrom (x t) (s t)).getD a 0)
      (((p.jetStep k).realFrom (x t) q).getD (5*a) 0) t := by
  induction p generalizing s q with
  | nil => exact hs
  | cons o p ih =>
    let s' : ℝ → List ℝ := fun v => o.real d (x v) (s v) :: s v
    let q' : List ℝ := (o.dual d k).realFrom (x t) q
    have hh (a : ℕ) : q'.getD (5*a+4) 0 = (s' t).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k (x t) (s t) q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5, s', q',
          List.getD_cons_succ] using (o.dual_register d k (x t) q (5*a+4)).trans (h a)
    have hd (a : ℕ) : HasDerivAt (fun v => (s' v).getD a 0) (q'.getD (5*a) 0) t := by
      cases a with
      | zero =>
        change HasDerivAt (fun v => o.real d (x v) (s v))
          (((o.dual d k).realFrom (x t) q).getD 0 0) t
        rw [o.dual_differential d k (x t) (s t) q h]
        exact o.hasDerivAt d k x s _ t hx hs hv.1
      | succ a =>
        change HasDerivAt (fun v => (s v).getD a 0)
          (((o.dual d k).realFrom (x t) q).getD (5*(a+1)) 0) t
        rw [show 5*(a+1)=5+5*a by omega, o.dual_register d k]
        exact hs a
    have hi := ih s' q' hh hd hv.2
    simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
      List.foldl_cons, List.foldl_append, s', q'] using hi

lemma differentiableAtFrom (p : NumericProgram) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : p.ValidFrom x (s x)) :
    ∀ a, DifferentiableAt ℝ (fun y => (p.realFrom y (s y)).getD a 0) x := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun y => o.real d y (s y) :: s y) ?_ hv.2
    intro a
    cases a with
    | zero => exact o.differentiableAt d x s hs hv.1
    | succ a => exact hs a

lemma differentiableAt (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    DifferentiableAt ℝ p.real x :=
  p.differentiableAtFrom x (fun _ => []) (fun _ => differentiableAt_const _) hv 0

lemma jetStep_real (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    (p.jetStep k).real x = fderiv ℝ p.real x (Pi.single k 1) := by
  let y : ℝ → Fin d → ℝ := fun t => x + t • Pi.single k 1
  have hy (i : Fin d) : HasDerivAt (fun t => y t i) (if i=k then 1 else 0) 0 := by
    have h := (hasDerivAt_const (0:ℝ) (x i)).add ((hasDerivAt_id (0:ℝ)).mul_const ((Pi.single k (1:ℝ) : Fin d → ℝ) i))
    simpa only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Function.const_apply, Pi.mul_apply, id_eq, mul_ite, mul_one, mul_zero, eq_comm, Pi.add_def, zero_add] using h
  have he : y 0 = x := by simp [y]
  have hh := p.jetStep_hasDerivAtFrom k y (fun _ => []) [] 0 hy (by simp)
    (by intro a; simpa using hasDerivAt_const (0:ℝ) (0:ℝ)) (by change p.Valid (y 0); rw [he]; exact hv) 0
  have hf := (p.differentiableAt x hv).hasFDerivAt.hasLineDerivAt (Pi.single k 1)
  exact HasDerivAt.unique (by simpa only [real, he, Nat.mul_zero] using hh) hf

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma computable_dual : Computable (fun z : Fin d × NumericOp => z.2.dual d z.1) := by
  have hi : Computable (fun a : ℕ => Fin.ofNat d a) :=
    (Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const d))).to_comp
  have he : Computable (fun z : Fin d × NumericOp => decide (Fin.ofNat d z.2.left = z.1)) :=
    Primrec.eq.decide.to_comp.comp (hi.comp (by unfold left; fun_prop)) Computable.fst
  have hb : Computable (fun z : Fin d × NumericOp =>
      if Fin.ofNat d z.2.left = z.1 then (1:ℚ) else 0) :=
    computable_ite he (Computable.const 1) (Computable.const 0)
  have hc (j : Fin 9) : Computable (fun z : Fin d × NumericOp =>
      dualCase d z.1 j z.2) := by
    fin_cases j <;> dsimp only [dualCase, left, right] <;> fun_prop
  exact computable_fin_cases (i := fun z => z.2.tag) (by unfold tag; fun_prop) hc

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma computable_jetStep : Computable (fun z : Fin d × NumericProgram => z.2.jetStep z.1) := by
  unfold jetStep
  have hd : Computable (fun z : (Fin d × NumericProgram) × NumericOp => z.2.dual d z.1.1) :=
    Computable.comp (f := fun z : Fin d × NumericOp => z.2.dual d z.1)
      (g := fun z : (Fin d × NumericProgram) × NumericOp => (z.1.1,z.2))
      (NumericOp.computable_dual d) (by fun_prop)
  exact ComputableRules.flatMapList (f := fun z : Fin d × NumericProgram => z.2)
    (g := fun z o => o.dual d z.1) Computable.snd
    hd

def literal (q : ℚ) : NumericProgram := [(0,q,0,0)]

def coordinate (k : Fin d) : NumericProgram := [(1,0,k.val,0)]

def unary (j : Fin 9) (n : ℕ) (p : NumericProgram) : NumericProgram := p ++ [(j,0,0,n)]

def binary (j : Fin 9) (p q : NumericProgram) : NumericProgram :=
  (p ++ q) ++ [(j,0,q.length,0)]

lemma literal_closed (q : ℚ) : (literal q).Closed := by trivial

lemma literal_valid (q : ℚ) (x : Fin d → ℝ) : (literal q).Valid x := by
  simp [literal, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

lemma literal_real (q : ℚ) (x : Fin d → ℝ) : (literal q).real x = q := rfl

omit [NeZero d] in
lemma coordinate_closed (k : Fin d) : (coordinate k).Closed := by trivial

lemma coordinate_valid (k : Fin d) (x : Fin d → ℝ) : (coordinate k).Valid x := by
  simp [coordinate, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

lemma coordinate_real (k : Fin d) (x : Fin d → ℝ) : (coordinate k).real x = x k := by
  simp [coordinate, real, realFrom, NumericOp.real, NumericOp.tag, NumericOp.left, Fin.ofNat_eq_cast]

lemma unary_real (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ) :
    (unary j n p).real x = NumericOp.real d (j,0,0,n) x (p.realFrom x []) := by
  simp [unary, real, realFrom, List.foldl_append]

lemma unary_valid (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ)
    (hp : p.Valid x) (hi : j = 5 → ((n+1:ℕ):ℝ)⁻¹ ≤ p.real x) :
    (unary j n p).Valid x := by
  exact (validFrom_concat _ _ _ _).mpr ⟨hp, ⟨hi, trivial⟩⟩

lemma unary_closed (j : Fin 9) (n : ℕ) (p : NumericProgram) (hp : p.Closed)
    (hne : p ≠ []) (hj : j = 4 ∨ j = 5 ∨ j = 7) : (unary j n p).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hne
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨hp, ?_⟩
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.left] using hn,trivial⟩

lemma realFrom_head {s : List ℝ} (hs : 0 < s.length) (t : List ℝ) :
    (s ++ t).getD 0 0 = s.getD 0 0 := by
  simp only [List.getD, List.getElem?_append_left hs]

lemma binary_real (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ [])
    (x : Fin d → ℝ) :
    (binary j p q).real x =
      NumericOp.real d (j,0,q.length,0) x (q.realFrom x [] ++ p.realFrom x []) := by
  cases q with
  | nil => exact (hne rfl).elim
  | cons head tail =>
    simp only [binary, real, realFrom_concat]
    rw [realFrom_empty_append (head :: tail) hq]
    rfl

lemma binary_register_left (p q : NumericProgram) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD q.length 0 = p.real x := by
  have he := q.realFrom_length x []
  simp only [List.length_nil, Nat.add_zero] at he
  rw [← he]
  simp only [List.getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

lemma binary_register_right (p q : NumericProgram) (hne : q ≠ []) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD 0 0 = q.real x := by
  apply realFrom_head
  simpa only [realFrom_length, List.length_nil, Nat.add_zero] using List.length_pos_iff.mpr hne

lemma binary_valid (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hj : j ≠ 5)
    (x : Fin d → ℝ) (hpv : p.Valid x) (hqv : q.Valid x) : (binary j p q).Valid x := by
  apply (validFrom_concat _ _ _ _).mpr
  refine ⟨(validFrom_concat _ _ _ _).mpr ⟨hpv,
    (validFrom_of_closed q hq x _).mpr hqv⟩, ?_⟩
  exact ⟨fun h => (hj h).elim, trivial⟩

lemma binary_closed (j : Fin 9) (p q : NumericProgram) (hp : p.Closed) (hq : q.Closed)
    (hnep : p ≠ []) (hneq : q ≠ []) (hj : j = 2 ∨ j = 3) : (binary j p q).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hnep
  have hqn : 0 < q.length := List.length_pos_iff.mpr hneq
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨(scopedFrom_concat _ _ _).mpr ⟨hp, q.scopedFrom_mono (Nat.zero_le _) hq⟩, ?_⟩
  rcases hj with rfl | rfl <;>
    simp only [ScopedFrom, NumericOp.Scoped, NumericOp.tag, NumericOp.left,
      NumericOp.right, List.length_append]
  all_goals exact ⟨⟨by omega, by omega⟩,trivial⟩

lemma binary_add_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 2 p q).real x = p.real x + q.real x := by
  rw [binary_real 2 p q hq hne]
  exact congrArg₂ (· + ·) (binary_register_left p q x) (binary_register_right p q hne x)

lemma binary_mul_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 3 p q).real x = p.real x * q.real x := by
  rw [binary_real 3 p q hq hne]
  exact congrArg₂ (· * ·) (binary_register_left p q x) (binary_register_right p q hne x)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

def Elementary {d : ℕ} [NeZero d] (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ p : NumericProgram, p ≠ [] ∧ p.Closed ∧ (∀ x : Fin d → ℝ, p.Valid x) ∧ p.real = f

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

lemma literal (q : ℚ) : Elementary (fun _ : Fin d → ℝ => (q : ℝ)) :=
  ⟨NumericProgram.literal q, by simp [NumericProgram.literal],
    NumericProgram.literal_closed q, NumericProgram.literal_valid q, rfl⟩

lemma coordinate (k : Fin d) : Elementary (fun z : Fin d → ℝ => z k) :=
  ⟨NumericProgram.coordinate k, by simp [NumericProgram.coordinate],
    NumericProgram.coordinate_closed k, NumericProgram.coordinate_valid k,
    funext (NumericProgram.coordinate_real k)⟩

lemma add (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x + g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 2 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 2 p q hpc hqc hpn hqn (Or.inl rfl),
    fun x => NumericProgram.binary_valid 2 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_add_real p q hqc hqn)⟩

lemma mul (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x * g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 3 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 3 p q hpc hqc hpn hqn (Or.inr rfl),
    fun x => NumericProgram.binary_valid 3 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_mul_real p q hqc hqn)⟩

lemma neg (hf : Elementary f) : Elementary (fun x => -f x) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 4 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 4 0 p hc hn (Or.inl rfl),
    fun x => NumericProgram.unary_valid 4 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma sub (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma inv (hf : Elementary f) (n : ℕ) (hn : ∀ x, ((n+1:ℕ):ℝ)⁻¹ ≤ f x) :
    Elementary (fun x => (f x)⁻¹) := by
  obtain ⟨p, hne, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 5 n p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 5 n p hc hne (Or.inr (Or.inl rfl)),
    fun x => NumericProgram.unary_valid 5 n p x (hv x) (fun _ => hn x), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma exp (hf : Elementary f) : Elementary (fun x => Real.exp (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 7 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 7 0 p hc hn (Or.inr (Or.inr rfl)),
    fun x => NumericProgram.unary_valid 7 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma rho (n : ℕ) (hf : Elementary f) : Elementary (fun x => rhoJet n (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p ++ [(6,0,n,0)], by simp, ?_, ?_, ?_⟩
  · apply (NumericProgram.scopedFrom_concat _ _ _).mpr
    exact ⟨hc, ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.right] using List.length_pos_iff.mpr hn, trivial⟩⟩
  · intro x
    exact (NumericProgram.validFrom_concat _ _ _ _).mpr ⟨hv x, ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩⟩
  · funext x
    simp only [NumericProgram.real, NumericProgram.realFrom_concat]
    rfl

lemma logLiteral (q : ℚ) : Elementary (fun _ : Fin d → ℝ => if 0 < q then Real.log (q : ℝ) else 0) := by
  refine ⟨[(8,q,0,0)], by simp, by simp [NumericProgram.Closed, NumericProgram.ScopedFrom, NumericOp.Scoped, NumericOp.tag], ?_, rfl⟩
  intro x
  exact ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩

lemma log_rat {q : ℚ} (hq : 0 < q) : Elementary (fun _ : Fin d → ℝ => Real.log (q : ℝ)) := by
  simpa only [ite_eq_left hq] using (logLiteral (d := d) q)

lemma differentiable (hf : Elementary f) : Differentiable ℝ f := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact fun x => p.differentiableAt x (hv x)

lemma coordinateDerivative (hf : Elementary f) (k : Fin d) :
    Elementary (fun x => fderiv ℝ f x (Pi.single k 1)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p.jetStep k, ?_, p.jetStep_closed k hc, fun x => p.jetStep_valid k (hv x), ?_⟩
  · apply List.length_pos_iff.mp
    rw [NumericProgram.jetStep_length]
    exact Nat.mul_pos (by decide) (List.length_pos_iff.mpr hn)
  · funext x
    exact p.jetStep_real k x (hv x)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i ∈ s, Elementary (f i)) : Elementary (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (literal (d := d) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma prod {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i ∈ s, Elementary (f i)) : Elementary (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (literal (d := d) 1)
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).mul (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

lemma zero : Elementary (fun _ : Fin d → ℝ => (0 : ℝ)) := by simpa using (literal (d := d) 0)

lemma one : Elementary (fun _ : Fin d → ℝ => (1 : ℝ)) := by simpa using (literal (d := d) 1)

lemma const_nat (n : ℕ) : Elementary (fun _ : Fin d → ℝ => (n : ℝ)) := by
  simpa using literal (d := d) (n : ℚ)

lemma div_rat (q : ℚ) {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => f x / (q : ℝ)) := by
  simpa [div_eq_mul_inv] using hf.mul (literal q⁻¹)

lemma operation (o : NumericOp) (g : (Fin d → ℝ) → (Fin e → ℝ))
    (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, o.Valid (s x)) : Elementary (fun x => o.real e (g x) (s x)) := by
  rcases o with ⟨j,q,a,b⟩
  fin_cases j <;> dsimp only [NumericOp.real, NumericOp.tag, NumericOp.rat,
    NumericOp.left, NumericOp.right]
  · exact literal q
  · exact hg _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · exact (hs a).inv b (fun x => hv x rfl)
  · exact (hs b).rho a
  · exact (hs a).exp
  · exact logLiteral q

lemma program_registers (p : NumericProgram)
    (g : (Fin d → ℝ) → (Fin e → ℝ)) (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, p.ValidFrom (g x) (s x)) :
    ∀ n, Elementary (fun x => (p.realFrom (g x) (s x)).getD n 0) := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun x => o.real e (g x) (s x) :: s x)
    · intro n
      cases n with
      | zero => exact operation o g s hg hs (fun x => (hv x).1)
      | succ n => exact hs n
    · exact fun x => (hv x).2

lemma comp {f : (Fin e → ℝ) → ℝ} (hf : Elementary f)
    (g : (Fin d → ℝ) → (Fin e → ℝ))
    (hg : ∀ k, Elementary (fun x => g x k)) : Elementary (fun x => f (g x)) := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact program_registers p g (fun _ => []) hg (fun n => by simpa using (zero (d:=d)))
    (fun x => hv (g x)) 0

lemma smoothTransition {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => Real.smoothTransition (f x)) := by
  have hρ : Elementary (fun x => expNegInvGlue (f x)) := by
    simpa only [rhoJet_zero] using hf.rho 0
  have hρ' : Elementary (fun x => expNegInvGlue (1 - f x)) := by
    simpa only [rhoJet_zero] using (one.sub hf).rho 0
  have hi := (hρ.add hρ').inv 8 (fun x => by
    simpa using transition_denom_lower (f x))
  simpa only [Real.smoothTransition, div_eq_mul_inv] using hρ.mul hi

end BalancedTransport.Effectivity.Elementary
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal

def coordinateL2 (i : Fin 3) :
    Lp Space 2 (volume : Measure Space) →L[ℝ] Lp ℝ 2 (volume : Measure Space) :=
  ContinuousLinearMap.compLpL 2 volume (ContinuousLinearMap.proj i)

lemma coordinateL2_coe (i : Fin 3) (V : Lp Space 2 (volume : Measure Space)) :
    (coordinateL2 i V : Space → ℝ) =ᵐ[volume] fun x => (V : Space → Space) x i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma coordinateL2_hasDerivWithinAt
    {V W : ℝ → Lp Space 2 (volume : Measure Space)} {t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt V (W t) s t) (i : Fin 3) :
    HasDerivWithinAt (fun t => coordinateL2 i (V t)) (coordinateL2 i (W t)) s t :=
  (coordinateL2 i).hasFDerivAt.comp_hasDerivWithinAt t h

def l2Energy (V : Lp Space 2 (volume : Measure Space)) : ℝ :=
  ∑ i : Fin 3, ‖coordinateL2 i V‖ ^ 2

def l2EnergyRate (V W : Lp Space 2 (volume : Measure Space)) : ℝ :=
  2 * ∑ i : Fin 3, inner ℝ (coordinateL2 i V) (coordinateL2 i W)

lemma l2Energy_nonneg (V : Lp Space 2 (volume : Measure Space)) : 0 ≤ l2Energy V :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma l2Energy_continuous : Continuous l2Energy := by
  unfold l2Energy
  fun_prop

lemma l2Energy_hasDerivWithinAt
    {V W : ℝ → Lp Space 2 (volume : Measure Space)} {t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt V (W t) s t) :
    HasDerivWithinAt (fun t => l2Energy (V t)) (l2EnergyRate (V t) (W t)) s t := by
  simpa only [l2Energy, l2EnergyRate, Finset.mul_sum] using
    HasDerivWithinAt.fun_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) =>
      (coordinateL2_hasDerivWithinAt h i).norm_sq)

lemma l2Inner_integral {V W : Lp Space 2 (volume : Measure Space)}
    {v w : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v)
    (hw : (W : Space → Space) =ᵐ[volume] w) (i : Fin 3) :
    inner ℝ (coordinateL2 i V) (coordinateL2 i W) = ∫ x, v x i * w x i := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coordinateL2_coe i V, coordinateL2_coe i W, hv, hw] with x hv' hw' hx hy
  simp only [hv', hw', hx, hy, RCLike.inner_apply, conj_trivial]
  ring

lemma l2Energy_integral {V : Lp Space 2 (volume : Measure Space)}
    {v : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v) :
    l2Energy V = ∑ i : Fin 3, ∫ x, (v x i)^2 := by
  unfold l2Energy
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq, l2Inner_integral hv hv]
  simp only [pow_two]

lemma l2Energy_eq_zero_of_bound
    {V W : ℝ → Lp Space 2 (volume : Measure Space)}
    (hV : ContinuousOn V (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt V (W t) (Ici 0) t)
    (hzero : V 0 = 0) {T K : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Ico (0 : ℝ) T, l2EnergyRate (V t) (W t) ≤ K * l2Energy (V t)) :
    l2Energy (V T) = 0 := by
  have hec : ContinuousOn (fun t => l2Energy (V t)) (Icc 0 T) :=
    l2Energy_continuous.comp_continuousOn (hV.mono (fun _ ht => ht.1))
  have he0 : l2Energy (V 0) ≤ 0 := by simp [hzero, l2Energy]
  have he' : ∀ x ∈ Ico (0 : ℝ) T, ∀ r : ℝ, l2EnergyRate (V x) (W x) < r →
      ∃ᶠ z in 𝓝[>] x, (z-x)⁻¹ * (l2Energy (V z) - l2Energy (V x)) < r := by
    intro x hx r hr
    have hh : HasDerivWithinAt (fun t => l2Energy (V t))
        (l2EnergyRate (V x) (W x)) (Ici x) x :=
      (l2Energy_hasDerivWithinAt (hderiv x hx.1)).mono (Ici_subset_Ici.mpr hx.1)
    simpa only [slope_def_field, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh.liminf_right_slope_le hr
  have H := le_gronwallBound_of_liminf_deriv_right_le (K := K) (ε := 0) hec he' he0
    (fun t ht => by simpa only [add_zero] using hbound t ht) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at H
  exact le_antisymm H (l2Energy_nonneg _)

lemma l2Energy_zero_pointwise {V : Lp Space 2 (volume : Measure Space)}
    {v : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v) (hc : Continuous v)
    (he : l2Energy V = 0) : v = 0 := by
  have hz (i : Fin 3) : coordinateL2 i V = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖coordinateL2 j V‖)).mp he i (Finset.mem_univ _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  ext x i
  have hae : (fun x => v x i) =ᵐ[volume] (0 : Space → ℝ) := by
    filter_upwards [coordinateL2_coe i V, hv, Lp.coeFn_zero ℝ 2 (volume : Measure Space)] with x h₁ h₂ h₃
    rw [hz, h₃, h₂] at h₁
    exact h₁.symm
  have hi := ((Continuous.ae_eq_iff_eq volume ((continuous_apply i).comp hc) continuous_const).mp hae)
  exact congrFun hi x

end BalancedTransport.Analysis
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
lemma SpatiallySupported.hasCompactSupport {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hs : SpatiallySupported K v) (t : ℝ) : HasCompactSupport (v t) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal (fun x hx => by
    by_contra hn
    exact hx (hs t x hn)) hK.isClosed

lemma JointSmooth.memLp {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) (t : ℝ) :
    MemLp (v t) 2 (volume : Measure Space) :=
  (hv.slice t).continuous.memLp_of_hasCompactSupport (hs.hasCompactSupport hK t)

def supportedL2Curve {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) : ℝ → Lp F 2 (volume : Measure Space) :=
  fun t => (hv.memLp hK hs t).toLp (v t)

lemma supportedL2Curve_coe {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) (t : ℝ) :
    (supportedL2Curve hK hv hs t : Space → F) =ᵐ[volume] v t := MemLp.coeFn_toLp _

def supportL2Size (K : Set Space) (hK : IsCompact K) : ℝ :=
  ‖indicatorConstLp (μ := (volume : Measure Space)) 2 hK.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖

lemma supportL2Size_nonneg (K : Set Space) (hK : IsCompact K) : 0 ≤ supportL2Size K hK :=
  norm_nonneg _

omit [NormedSpace ℝ F] in
lemma lp_norm_bound_of_support {K : Set Space} (hK : IsCompact K)
    {f : Lp F 2 (volume : Measure Space)} {g : Space → F} {C : ℝ}
    (he : (f : Space → F) =ᵐ[volume] g) (hs : ∀ x, x ∉ K → g x = 0)
    (hb : ∀ x, ‖g x‖ ≤ C) : ‖f‖ ≤ C * supportL2Size K hK := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [he, indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure Space))
      (hs := hK.measurableSet) (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hfx hix
  rw [hfx, hix]
  by_cases hx : x ∈ K
  · simpa only [indicator_of_mem hx, norm_one, mul_one] using hb x
  · simp only [indicator_of_notMem hx, hs x hx, norm_zero, mul_zero, le_refl]

lemma time_difference_bound {v : Field F} (hv : JointSmooth v) {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Space) :
    ‖v s x - v t x‖ ≤ C * ‖s - t‖ :=
  (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun r _ => (hv.timeSlice x).differentiable (by simp) r)
    (fun r hr => hb r hr x) ht hs

lemma time_remainder_bound {v : Field F} (hv : JointSmooth v) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Space) :
    ‖v s x - v t x - (s - t) • fullTimeD v t x‖ ≤ B * ‖s - t‖ * ‖s - t‖ := by
  let r : ℝ → F := fun q => v q x - v t x - (q - t) • fullTimeD v t x
  have hdr (q : ℝ) : HasDerivAt r (fullTimeD v q x - fullTimeD v t x) q := by
    convert (((hv.timeSlice x).differentiable (by simp) q).hasDerivAt.sub_const (v t x)).sub
        (((hasDerivAt_id q).sub_const t).smul_const (fullTimeD v t x)) using 1 <;>
      simp only [r, fullTimeD, id_eq, one_smul]
    rfl
  have hbound (q : ℝ) (hq : q ∈ uIcc t s) :
      ‖deriv r q‖ ≤ B * ‖s - t‖ := by
    rw [(hdr q).deriv]
    have hq₀ : 0 ≤ q := (le_min ht hs).trans hq.1
    refine (time_difference_bound hv.fullTimeD hb hq₀ ht x).trans ?_
    apply mul_le_mul_of_nonneg_left _ hB
    simpa only [Real.dist_eq, ← Real.norm_eq_abs, norm_sub_rev] using
      Real.dist_left_le_of_mem_uIcc hq
  have h := (convex_uIcc t s).norm_image_sub_le_of_norm_deriv_le
    (fun q _ => (hdr q).differentiableAt) hbound (left_mem_uIcc) (right_mem_uIcc)
  simpa only [r, sub_self, zero_smul, sub_zero] using h

lemma supportedL2Curve_difference_bound {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C)
    {s t : ℝ} (hs₀ : 0 ≤ s) (ht₀ : 0 ≤ t) :
    ‖supportedL2Curve hK hv hs s - supportedL2Curve hK hv hs t‖ ≤
      C * ‖s - t‖ * supportL2Size K hK := by
  apply lp_norm_bound_of_support hK
  · exact (Lp.coeFn_sub _ _).trans ((supportedL2Curve_coe hK hv hs s).sub
      (supportedL2Curve_coe hK hv hs t))
  · intro x hx
    change v s x - v t x = 0
    simp only [hs s x hx, hs t x hx, sub_self]
  · exact fun x => time_difference_bound hv hb hs₀ ht₀ x

lemma supportedL2Curve_continuousOn {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C) :
    ContinuousOn (supportedL2Curve hK hv hs) (Ici 0) := by
  let L : ℝ≥0 := ⟨C * supportL2Size K hK, mul_nonneg hC (supportL2Size_nonneg K hK)⟩
  apply LipschitzOnWith.continuousOn (K := L)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs₀ t ht₀
  simp only [dist_eq_norm]
  change ‖supportedL2Curve hK hv hs s - supportedL2Curve hK hv hs t‖ ≤
    C * supportL2Size K hK * ‖s - t‖
  convert supportedL2Curve_difference_bound hK hv hs hb hs₀ ht₀ using 1
  ring

lemma supportedL2Curve_hasDerivWithinAt {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (supportedL2Curve hK hv hs)
      (supportedL2Curve hK hv.fullTimeD hs.fullTimeD t) (Ici 0) t := by
  let V := supportedL2Curve hK hv hs
  let W := supportedL2Curve hK hv.fullTimeD hs.fullTimeD
  have hrem (s : ℝ) (hs₀ : 0 ≤ s) :
      ‖V s - V t - (s-t) • W t‖ ≤ B * ‖s-t‖ * ‖s-t‖ * supportL2Size K hK := by
    apply lp_norm_bound_of_support hK
    · exact (Lp.coeFn_sub _ _).trans (((Lp.coeFn_sub _ _).trans
        ((supportedL2Curve_coe hK hv hs s).sub (supportedL2Curve_coe hK hv hs t))).sub
        ((Lp.coeFn_smul _ _).trans ((supportedL2Curve_coe hK hv.fullTimeD hs.fullTimeD t).const_smul _)))
    · intro x hx
      change v s x - v t x - (s-t) • fullTimeD v t x = 0
      simp only [hs s x hx, hs t x hx, hs.fullTimeD t x hx, sub_self, smul_zero]
    · exact fun x => time_remainder_bound hv hB hb hs₀ ht x
  apply HasDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hc : ContinuousAt (fun s : ℝ => B * supportL2Size K hK * ‖s-t‖) t := by fun_prop
  have hn : ∀ᶠ s in 𝓝[Ici 0] t, B * supportL2Size K hK * ‖s-t‖ < ε :=
    mem_nhdsWithin_of_mem_nhds (hc.eventually (gt_mem_nhds (by simpa using hε)))
  filter_upwards [self_mem_nhdsWithin, hn] with s hs₀ hsε
  exact (hrem s hs₀).trans (by nlinarith [norm_nonneg (s-t)])

lemma spatialD_eq_fullMixedD (a : List (Fin 3)) (v : Field F) :
    spatialD a v = fullMixedD (a.map some) v := by
  induction a with
  | nil => rfl
  | cons i a ha => simp only [spatialD, List.map_cons, fullMixedD, ha]

theorem CH_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v)
    (k : ℕ) : CH k v := by
  intro a _
  let d := fullMixedD (a.map some) v
  have hd : JointSmooth d := hv.fullMixedD _
  have hds : SpatiallySupported K d := hs.fullMixedD hK.isClosed _
  obtain ⟨C, hC, hbound⟩ := hb (none :: a.map some)
  have he (t : ℝ) (ht : 0 ≤ t) (x : Space) :
      fullTimeD d t x = mixedD (none :: a.map some) v t x :=
    fullMixedD_eq_mixedD hv (none :: a.map some) t ht x
  have hb' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD d t x‖ ≤ C := by
    intro t ht x
    rw [he t ht x]
    exact hbound t ht x
  refine ⟨supportedL2Curve hK hd hds,
    supportedL2Curve_continuousOn hK hd hds hC hb', fun t _ => ?_⟩
  simpa only [spatialD_eq_fullMixedD] using supportedL2Curve_coe hK hd hds t

theorem C1L2_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v) :
    C1L2 v := by
  obtain ⟨C, hC, hc⟩ := hb [none]
  obtain ⟨B, hB, hb'⟩ := hb [none, none]
  have hc' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C := by
    intro t ht x
    rw [show fullTimeD v t x = mixedD [none] v t x from fullMixedD_eq_mixedD hv [none] t ht x]
    exact hc t ht x
  have hb'' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B := by
    intro t ht x
    rw [show fullTimeD (fullTimeD v) t x = mixedD [none,none] v t x from
      fullMixedD_eq_mixedD hv [none, none] t ht x]
    exact hb' t ht x
  refine ⟨supportedL2Curve hK hv hs, supportedL2Curve hK hv.fullTimeD hs.fullTimeD,
    supportedL2Curve_continuousOn hK hv hs hC hc',
    supportedL2Curve_continuousOn hK hv.fullTimeD hs.fullTimeD hB hb'', fun t ht => ?_⟩
  refine ⟨supportedL2Curve_coe hK hv hs t, ?_,
    supportedL2Curve_hasDerivWithinAt hK hv hs hB hb'' ht⟩
  apply (supportedL2Curve_coe hK hv.fullTimeD hs.fullTimeD t).trans
  exact Eventually.of_forall (fun x => fullMixedD_eq_mixedD hv [none] t ht x)

lemma boundedOnFiniteSlabs_of_boundedMixed {v : Velocity} (hv : BoundedMixed v) :
    BoundedOnFiniteSlabs v := by
  obtain ⟨C, hC, hb⟩ := hv []
  have hd : ∀ i : Fin 3, ∃ D : ℝ, 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ x, ‖spaceD i v t x‖ ≤ D :=
    fun i => hv [some i]
  choose D hD hd using hd
  intro T _
  refine ⟨C + ∑ i, D i, add_nonneg hC (Finset.sum_nonneg (fun i _ => hD i)), ?_⟩
  intro t ht x
  constructor
  · exact (hb t ht.1 x).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hD i)))
  · intro i
    exact (hd i t ht.1 x).trans
      ((Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hC))

lemma spatialD_zero (a : List (Fin 3)) : spatialD a (0 : Field F) = 0 := by
  induction a with
  | nil => rfl
  | cons i a ha =>
    simp only [spatialD, ha]
    ext t x
    simp [spaceD]

lemma CH_zero (k : ℕ) : CH k (0 : Field F) := by
  intro a _
  refine ⟨0, continuousOn_const, fun t _ => ?_⟩
  rw [spatialD_zero]
  exact Lp.coeFn_zero F 2 (volume : Measure Space)

theorem comparisonClass_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Velocity} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v) :
    ComparisonClass v (fun _ _ => 0) := by
  refine ⟨CH_of_compact_boundedMixed hK hv hs hb 2,
    C1L2_of_compact_boundedMixed hK hv hs hb,
    boundedOnFiniteSlabs_of_boundedMixed hb, fun _ => 0, ?_⟩
  convert CH_zero (F := ℝ) 1 using 1
  ext t x
  exact sub_zero 0

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma Smooth.slice {v : Field F} (hv : Smooth v) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (v t) := by
  apply contDiffOn_univ.mp
  exact hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩)

lemma Smooth.sub {v w : Field F} (hv : Smooth v) (hw : Smooth w) :
    Smooth (fun t x => v t x - w t x) := hv.sub hw

lemma CH.memLp {v : Field F} {k : ℕ} (hv : CH k v)
    (a : List (Fin 3)) (ha : a.length ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (spatialD a v t) 2 (volume : Measure Space) := by
  obtain ⟨V, _, he⟩ := hv a ha
  exact (Lp.memLp (V t)).ae_eq (he t ht)

lemma membrane_component {f : Space → Space} (hf : MemLp f 2 (volume : Measure Space))
    (hc : Continuous f) (i : Fin 3) : MemLp (fun x => f x i) 2 (volume : Measure Space) := by
  apply hf.of_le ((continuous_apply i).comp hc).aestronglyMeasurable
  exact Eventually.of_forall (fun x => norm_le_pi_norm (f x) i)

lemma integrable_bounded_mul_l2_mul_l2 {a f g : Space → ℝ} {C : ℝ}
    (ha : Continuous a) (hab : ∀ x, ‖a x‖ ≤ C)
    (hf : MemLp f 2 (volume : Measure Space)) (hg : MemLp g 2 (volume : Measure Space)) :
    Integrable (fun x => a x * f x * g x) (volume : Measure Space) := by
  convert (hf.integrable_mul hg).bdd_mul ha.aestronglyMeasurable
      (Eventually.of_forall hab) using 1
  ext x
  simp only [Pi.mul_apply, mul_assoc]

lemma integral_mul_pd_eq_neg_pd_mul {f g : Space → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3)
    (hdg : Integrable (fun x => pd j f x * g x) (volume : Measure Space))
    (hfd : Integrable (fun x => f x * pd j g x) (volume : Measure Space))
    (hfg : Integrable (fun x => f x * g x) (volume : Measure Space)) :
    (∫ x, f x * pd j g x) = - ∫ x, pd j f x * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdg hfd hfg
    (fun x _ => hf x) (fun x _ => hg x)

lemma transport_component {a w : Space → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (j : Fin 3) {C : ℝ} (hc : ∀ x, ‖a x‖ ≤ C) (hd : ∀ x, ‖pd j a x‖ ≤ C)
    (hw₂ : MemLp w 2 (volume : Measure Space))
    (hdw₂ : MemLp (pd j w) 2 (volume : Measure Space)) :
    2 * (∫ x, a x * pd j w x * w x) = - ∫ x, pd j a x * w x * w x := by
  have Hi := integrable_bounded_mul_l2_mul_l2 ha.continuous hc hdw₂ hw₂
  have Hj := integrable_bounded_mul_l2_mul_l2 (pd_contDiff j ha).continuous hd hw₂ hw₂
  have Hk := integrable_bounded_mul_l2_mul_l2 ha.continuous hc hw₂ hw₂
  have he (x : Space) : pd j (fun x => w x * w x) x = 2 * (pd j w x * w x) := by
    rw [pd_mul j (hw.differentiable (by simp) x) (hw.differentiable (by simp) x)]
    ring
  have hdg : Integrable (fun x => pd j a x * (w x * w x)) (volume : Measure Space) := by
    simpa only [mul_assoc] using Hj
  have hfg : Integrable (fun x => a x * (w x * w x)) (volume : Measure Space) := by
    simpa only [mul_assoc] using Hk
  have hfd : Integrable (fun x => a x * pd j (fun x => w x * w x) x)
      (volume : Measure Space) := by
    convert Hi.const_mul 2 using 1
    ext x
    rw [he]
    ring
  have H := integral_mul_pd_eq_neg_pd_mul (ha.differentiable (by simp))
    ((hw.mul hw).differentiable (by simp)) j hdg hfd hfg
  have he' : (fun x => a x * pd j (fun x => w x * w x) x) =
      (fun x => 2 * (a x * pd j w x * w x)) := by
    ext x
    rw [he]
    ring
  rw [he', integral_const_mul] at H
  simpa only [mul_assoc] using H

theorem transport_cancellation {v : Space → Space} {w : Space → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {C : ℝ} (hb : ∀ x, ‖v x‖ ≤ C) (hdb : ∀ x j, ‖pd j v x‖ ≤ C)
    (hdiv : ∀ x, ∑ j, pd j v x j = 0)
    (hw₂ : MemLp w 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (pd j w) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, v x j * pd j w x * w x) = 0 := by
  have he (j : Fin 3) (x : Space) : pd j (fun x => v x j) x = pd j v x j :=
    pd_apply j j (hv.differentiable (by simp) x)
  have H (j : Fin 3) := transport_component (contDiff_pi.mp hv j) hw j
    (fun x => (norm_le_pi_norm (v x) j).trans (hb x))
    (fun x => by rw [he]; exact (norm_le_pi_norm (pd j v x) j).trans (hdb x j))
    hw₂ (hdw₂ j)
  have hdj (j : Fin 3) : Integrable (fun x => pd j v x j * w x * w x) (volume : Measure Space) := by
    apply integrable_bounded_mul_l2_mul_l2
      ((continuous_apply j).comp (pd_contDiff j hv).continuous)
      (fun x => (norm_le_pi_norm (pd j v x) j).trans (hdb x j)) hw₂ hw₂
  have hsum : (∑ j, ∫ x, pd j v x j * w x * w x) = 0 := by
    rw [← integral_finsetSum _ (fun j _ => hdj j)]
    have hz (x : Space) : (∑ j, pd j v x j * w x * w x) = 0 := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hdiv x, zero_mul, zero_mul]
    simp only [hz, integral_zero]
  have Hsum := congrArg (fun f : Fin 3 → ℝ => ∑ j, f j) (funext H)
  simp only [he, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum, neg_zero] at Hsum
  linarith

lemma diffusion_component {w : Space → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (j : Fin 3) (hw₂ : MemLp w 2 (volume : Measure Space))
    (hd₂ : MemLp (pd j w) 2 (volume : Measure Space))
    (hdd₂ : MemLp (pd j (pd j w)) 2 (volume : Measure Space)) :
    (∫ x, w x * pd j (pd j w) x) = - ∫ x, (pd j w x) ^ 2 := by
  simpa only [pow_two] using integral_mul_pd_eq_neg_pd_mul
    (hw.differentiable (by simp)) ((pd_contDiff j hw).differentiable (by simp)) j
    (hd₂.integrable_mul hd₂) (hw₂.integrable_mul hdd₂) (hw₂.integrable_mul hd₂)

theorem pressure_cancellation {w : Space → Space} {p : Space → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hdiv : ∀ x, ∑ j, pd j w x j = 0)
    (hw₂ : ∀ j, MemLp (fun x => w x j) 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (fun x => pd j w x j) 2 (volume : Measure Space))
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hdp₂ : ∀ j, MemLp (pd j p) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, w x j * pd j p x) = 0 := by
  have he (j : Fin 3) (x : Space) : pd j (fun x => w x j) x = pd j w x j :=
    pd_apply j j (hw.differentiable (by simp) x)
  have hdj (j : Fin 3) : Integrable (fun x => pd j w x j * p x) (volume : Measure Space) :=
    (hdw₂ j).integrable_mul hp₂
  have H (j : Fin 3) : (∫ x, w x j * pd j p x) = -∫ x, pd j w x j * p x := by
    have hdj' : Integrable (fun x => pd j (fun x => w x j) x * p x) (volume : Measure Space) := by
      simpa only [he] using hdj j
    simpa only [he] using integral_mul_pd_eq_neg_pd_mul
      ((contDiff_pi.mp hw j).differentiable (by simp)) (hp.differentiable (by simp)) j
      hdj' ((hw₂ j).integrable_mul (hdp₂ j)) ((hw₂ j).integrable_mul hp₂)
  simp only [H, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun j _ => hdj j)]
  have hz (x : Space) : (∑ j, pd j w x j * p x) = 0 := by
    rw [← Finset.sum_mul, hdiv x, zero_mul]
  simp only [hz, integral_zero, neg_zero]

end BalancedTransport.Analysis
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry

structure SliceH2 (w : Space → Space) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) w
  l2 : ∀ i, MemLp (fun x => w x i) 2 (volume : Measure Space)
  d_l2 : ∀ i j, MemLp (fun x => pd j w x i) 2 (volume : Measure Space)
  dd_l2 : ∀ i j, MemLp (fun x => pd j (pd j w) x i) 2 (volume : Measure Space)

lemma sliceH2_of_CH {u : Velocity} (hu : Smooth u) (hH : CH 2 u) {t : ℝ} (ht : 0 ≤ t) :
    SliceH2 (u t) := by
  have hs := Smooth.slice hu ht
  exact ⟨hs, fun i => membrane_component (CH.memLp hH [] (by simp) ht) hs.continuous i,
    fun i j => membrane_component (CH.memLp hH [j] (by simp) ht) (pd_contDiff j hs).continuous i,
    fun i j => membrane_component (CH.memLp hH [j,j] (by simp) ht)
      (pd_contDiff j (pd_contDiff j hs)).continuous i⟩

lemma SliceH2.sub {u v : Space → Space} (hu : SliceH2 u) (hv : SliceH2 v) :
    SliceH2 (fun x => u x - v x) := by
  have he (j : Fin 3) : pd j (fun x => u x - v x) = fun x => pd j u x - pd j v x := by
    ext x i
    rw [pd_sub _ (hu.smooth.differentiable (by simp) x) (hv.smooth.differentiable (by simp) x)]
  refine ⟨hu.smooth.sub hv.smooth, fun i => (hu.l2 i).sub (hv.l2 i), ?_, ?_⟩
  · intro i j
    rw [he]
    exact (hu.d_l2 i j).sub (hv.d_l2 i j)
  · intro i j
    rw [he]
    have hh : pd j (fun x => pd j u x - pd j v x) =
        fun x => pd j (pd j u) x - pd j (pd j v) x :=
      funext (fun x => pd_sub j ((pd_contDiff j hu.smooth).differentiable (by simp) x)
        ((pd_contDiff j hv.smooth).differentiable (by simp) x))
    rw [hh]
    exact (hu.dd_l2 i j).sub (hv.dd_l2 i j)

lemma SliceH2.scalar_d {w : Space → Space} (hw : SliceH2 w) (i j : Fin 3) :
    MemLp (pd j (fun x => w x i)) 2 (volume : Measure Space) := by
  have he : pd j (fun x => w x i) = fun x => pd j w x i :=
    funext (fun x => pd_apply j i (hw.smooth.differentiable (by simp) x))
  rw [he]
  exact hw.d_l2 i j

lemma SliceH2.scalar_dd {w : Space → Space} (hw : SliceH2 w) (i j : Fin 3) :
    MemLp (pd j (pd j (fun x => w x i))) 2 (volume : Measure Space) := by
  have he : pd j (fun x => w x i) = fun x => pd j w x i :=
    funext (fun x => pd_apply j i (hw.smooth.differentiable (by simp) x))
  have he' : pd j (fun x => pd j w x i) = fun x => pd j (pd j w) x i :=
    funext (fun x => pd_apply j i ((pd_contDiff j hw.smooth).differentiable (by simp) x))
  rw [he, he']
  exact hw.dd_l2 i j

lemma minus_triple_bound {a x y C : ℝ} (ha : |a| ≤ C) (hC : 0 ≤ C) :
    -(a*x*y) ≤ C*(x^2+y^2) := by
  have hxy : |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y, sq_nonneg x, sq_nonneg y]
  calc
    -(a*x*y) ≤ |a*x*y| := neg_le_abs _
    _ = |a| * (|x| * |y|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ C * (|x| * |y|) := mul_le_mul_of_nonneg_right ha (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ C*(x^2+y^2) := mul_le_mul_of_nonneg_left hxy hC

lemma stretching_bound {a f g : Space → ℝ} {C : ℝ}
    (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ C) (hC : 0 ≤ C)
    (hf : MemLp f 2 (volume : Measure Space)) (hg : MemLp g 2 (volume : Measure Space)) :
    -(∫ x, a x * f x * g x) ≤ C * ((∫ x, (f x)^2) + ∫ x, (g x)^2) := by
  have hff : Integrable (fun x => (f x)^2) (volume : Measure Space) := by
    simpa only [pow_two, Pi.mul_def] using hf.integrable_mul hf
  have hgg : Integrable (fun x => (g x)^2) (volume : Measure Space) := by
    simpa only [pow_two, Pi.mul_def] using hg.integrable_mul hg
  rw [← integral_neg, ← integral_add hff hgg, ← integral_const_mul]
  apply integral_mono (integrable_bounded_mul_l2_mul_l2 ha hb hf hg).neg
    ((hff.add hgg).const_mul C)
  exact fun x => minus_triple_bound (hb x) hC

theorem energy_pairing_bound
    {w a v g : Space → Space} {p : Space → ℝ} {ν C A : ℝ}
    (hw : SliceH2 w) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (ha_b : ∀ x, ‖a x‖ ≤ A) (ha_d : ∀ x j, ‖pd j a x‖ ≤ A)
    (hv_d : ∀ x j, ‖pd j v x‖ ≤ C)
    (ha_div : ∀ x, ∑ j, pd j a x j = 0)
    (hw_div : ∀ x, ∑ j, pd j w x j = 0)
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hp_d : ∀ j, MemLp (pd j p) 2 (volume : Measure Space))
    (hPDE : ∀ x i, g x i = ν * (∑ j, pd j (pd j w) x i) -
      (∑ j, a x j * pd j w x i) - (∑ j, w x j * pd j v x i) - pd i p x) :
    (∑ i : Fin 3, ∫ x, w x i * g x i) ≤
      6 * C * (∑ i : Fin 3, ∫ x, (w x i)^2) := by
  let E : Fin 3 → ℝ := fun i => ∫ x, (w x i)^2
  let D : Fin 3 → Fin 3 → ℝ := fun i j => ∫ x, w x i * pd j (pd j w) x i
  let T : Fin 3 → Fin 3 → ℝ := fun i j => ∫ x, a x j * pd j w x i * w x i
  let S : Fin 3 → Fin 3 → ℝ := fun i j => ∫ x, pd j v x i * w x j * w x i
  let P : Fin 3 → ℝ := fun i => ∫ x, w x i * pd i p x
  have hdcomp (i j : Fin 3) : pd j (fun x => w x i) = fun x => pd j w x i :=
    funext (fun x => pd_apply j i (hw.smooth.differentiable (by simp) x))
  have hddcomp (i j : Fin 3) : pd j (fun x => pd j w x i) = fun x => pd j (pd j w) x i :=
    funext (fun x => pd_apply j i ((pd_contDiff j hw.smooth).differentiable (by simp) x))
  have hDe (i j : Fin 3) : D i j = -∫ x, (pd j w x i)^2 := by
    simpa only [D, hdcomp, hddcomp] using
      diffusion_component (contDiff_pi.mp hw.smooth i) j (hw.l2 i)
        (hw.scalar_d i j) (hw.scalar_dd i j)
  have hDn (i j : Fin 3) : D i j ≤ 0 := by
    rw [hDe]
    exact neg_nonpos.mpr (integral_nonneg (fun _ => sq_nonneg _))
  have hTe (i : Fin 3) : ∑ j, T i j = 0 := by
    simpa only [T, pd_apply _ i (hw.smooth.differentiable (by simp) _)] using
      transport_cancellation ha (contDiff_pi.mp hw.smooth i) ha_b ha_d ha_div (hw.l2 i)
        (hw.scalar_d i)
  have hPe : ∑ i, P i = 0 := pressure_cancellation hw.smooth hp hw_div hw.l2
    (fun i => hw.d_l2 i i) hp₂ hp_d
  have hSb (i j : Fin 3) : -(S i j) ≤ C * (E j + E i) :=
    stretching_bound ((continuous_apply i).comp (pd_contDiff j hv).continuous)
      (fun x => (norm_le_pi_norm (pd j v x) i).trans (hv_d x j)) hC (hw.l2 j) (hw.l2 i)
  have hdint (i j : Fin 3) : Integrable (fun x => w x i * pd j (pd j w) x i)
      (volume : Measure Space) := (hw.l2 i).integrable_mul (hw.dd_l2 i j)
  have htint (i j : Fin 3) : Integrable (fun x => a x j * pd j w x i * w x i)
      (volume : Measure Space) :=
    integrable_bounded_mul_l2_mul_l2 ((continuous_apply j).comp ha.continuous)
      (fun x => (norm_le_pi_norm (a x) j).trans (ha_b x)) (hw.d_l2 i j) (hw.l2 i)
  have hsint (i j : Fin 3) : Integrable (fun x => pd j v x i * w x j * w x i)
      (volume : Measure Space) :=
    integrable_bounded_mul_l2_mul_l2 ((continuous_apply i).comp (pd_contDiff j hv).continuous)
      (fun x => (norm_le_pi_norm (pd j v x) i).trans (hv_d x j)) (hw.l2 j) (hw.l2 i)
  have hpint (i : Fin 3) : Integrable (fun x => w x i * pd i p x)
      (volume : Measure Space) := (hw.l2 i).integrable_mul (hp_d i)
  have he (i : Fin 3) : (∫ x, w x i * g x i) =
      ν * (∑ j, D i j) - (∑ j, T i j) - (∑ j, S i j) - P i := by
    have hfun : (fun x => w x i * g x i) = fun x =>
        ν * (∑ j, w x i * pd j (pd j w) x i) -
          (∑ j, a x j * pd j w x i * w x i) -
          (∑ j, pd j v x i * w x j * w x i) - w x i * pd i p x := by
      ext x
      rw [hPDE]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring
    have hdI : Integrable (fun x => ν * ∑ j, w x i * pd j (pd j w) x i)
        (volume : Measure Space) :=
      (integrable_finsetSum Finset.univ (fun j _ => hdint i j)).const_mul ν
    have htI : Integrable (fun x => ∑ j, a x j * pd j w x i * w x i)
        (volume : Measure Space) := integrable_finsetSum Finset.univ (fun j _ => htint i j)
    have hsI : Integrable (fun x => ∑ j, pd j v x i * w x j * w x i)
        (volume : Measure Space) := integrable_finsetSum Finset.univ (fun j _ => hsint i j)
    have hdtI : Integrable (fun x => ν * (∑ j, w x i * pd j (pd j w) x i) -
        ∑ j, a x j * pd j w x i * w x i) (volume : Measure Space) := hdI.sub htI
    have hdtsI : Integrable (fun x => ν * (∑ j, w x i * pd j (pd j w) x i) -
        (∑ j, a x j * pd j w x i * w x i) - ∑ j, pd j v x i * w x j * w x i)
        (volume : Measure Space) := hdtI.sub hsI
    rw [hfun, integral_sub hdtsI (hpint i), integral_sub hdtI hsI, integral_sub hdI htI]
    rw [integral_const_mul,
      integral_finsetSum _ (fun j _ => hdint i j),
      integral_finsetSum _ (fun j _ => htint i j),
      integral_finsetSum _ (fun j _ => hsint i j)]

  simp only [he, hTe, sub_zero, Finset.sum_sub_distrib, hPe, sub_zero]
  have hdiff : ∑ i, ν * (∑ j, D i j) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos hν
      (Finset.sum_nonpos (fun j _ => hDn i j)))
  have hstr := Finset.sum_le_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (j : Fin 3) (_ : j ∈ Finset.univ) => hSb i j))
  have hdouble : (∑ i : Fin 3, ∑ j : Fin 3, C * (E j + E i)) = 6*C*(∑ i, E i) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hdouble] at hstr
  simp only [Finset.sum_neg_distrib] at hstr
  change _ ≤ 6*C*(∑ i, E i)
  linarith

end BalancedTransport.Analysis
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry

lemma difference_divergence {u U : Velocity} (hu : Smooth u) (hU : Smooth U)
    {t : ℝ} (ht : 0 ≤ t) (hdu : ∀ x, div u t x = 0) (hdU : ∀ x, div U t x = 0)
    (x : Space) : ∑ j, pd j (fun x => u t x - U t x) x j = 0 := by
  simp only [pd_sub _ ((Smooth.slice hu ht).differentiable (by simp) x)
      ((Smooth.slice hU ht).differentiable (by simp) x), Pi.sub_apply,
    Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr ((hdu x).trans (hdU x).symm)

lemma difference_equation {ν : ℝ} {f u U : Velocity} {p : Pressure}
    (hu : ZeroDataSolution ν f u p) (hU : ZeroDataSolution ν f U (fun _ _ => 0))
    {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (x : Space) (i : Fin 3) :
    timeD u t x i - timeD U t x i =
      ν * (∑ j, pd j (pd j (fun x => u t x - U t x)) x i) -
      (∑ j, u t x j * pd j (fun x => u t x - U t x) x i) -
      (∑ j, (u t x j - U t x j) * pd j (U t) x i) - pd i (fun x => p t x - c) x := by
  have hus := Smooth.slice hu.1 ht
  have hUs := Smooth.slice hU.1 ht
  have hd (j : Fin 3) : pd j (fun x => u t x - U t x) = fun x => pd j (u t) x - pd j (U t) x :=
    funext (fun x => pd_sub j (hus.differentiable (by simp) x) (hUs.differentiable (by simp) x))
  have hdu := congrFun (hu.2.2.2.2 t ht x) i
  have hdU := congrFun (hU.2.2.2.2 t ht x) i
  simp only [convection, laplacian, gradient, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul] at hdu hdU
  have hu' : timeD u t x i + (∑ j, u t x j * pd j (u t) x i) =
      -pd i (p t) x + ν * (∑ j, pd j (pd j (u t)) x i) + f t x i := hdu
  have hU' : timeD U t x i + (∑ j, U t x j * pd j (U t) x i) =
      ν * (∑ j, pd j (pd j (U t)) x i) + f t x i := by
    change timeD U t x i + (∑ j, U t x j * pd j (U t) x i) =
      -pd i (fun _ => (0 : ℝ)) x + ν * (∑ j, pd j (pd j (U t)) x i) + f t x i at hdU
    simpa only [pd_const, neg_zero, zero_add] using hdU
  simp only [hd, pd_sub _ ((pd_contDiff _ hus).differentiable (by simp) x)
      ((pd_contDiff _ hUs).differentiable (by simp) x), Pi.sub_apply, pd_sub_const]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hu' hU' ⊢
  linear_combination hu' - hU'

lemma constant_pressure_of_velocity_eq {ν : ℝ} {f u U : Velocity} {p : Pressure}
    (hu : ZeroDataSolution ν f u p) (hU : ZeroDataSolution ν f U (fun _ _ => 0))
    (he : ∀ t, 0 ≤ t → ∀ x, u t x = U t x) :
    ∀ t, 0 ≤ t → ∀ x y, p t x = p t y := by
  have hf : ForwardEq u U := fun t ht => funext (he t ht)
  intro t ht
  have hg (x : Space) : gradient p t x = 0 := by
    have hd := hu.2.2.2.2 t ht x
    have hD := hU.2.2.2.2 t ht x
    have heD := congrFun (hf.mixedD [none] t ht) x
    change timeD u t x = timeD U t x at heD
    have heL : laplacian u t x = laplacian U t x := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (hf.mixedD [some i, some i] t ht) x
    have heC : convection u t x = convection U t x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he t ht x, show spaceD i u t x = spaceD i U t x from
        congrFun (hf.mixedD [some i] t ht) x]
    have hz : gradient (fun _ _ => 0) t x = 0 := by ext i; simp [gradient, spaceD]
    rw [heD, heL, heC] at hd
    rw [hz, neg_zero, zero_add] at hD
    have hh : -gradient p t x = 0 := by
      exact add_left_cancel (a := ν • laplacian U t x + f t x)
        (by simpa only [add_assoc, zero_add, add_zero, add_comm, add_left_comm] using hd.symm.trans hD)
    exact neg_eq_zero.mp hh
  apply is_const_of_fderiv_eq_zero ((Smooth.slice hu.2.1 ht).differentiable (by simp))
  intro x
  ext y
  have hd (i : Fin 3) : fderiv ℝ (p t) x (Pi.single i 1) = 0 := congrFun (hg x) i
  have hy : y = ∑ i : Fin 3, y i • (Pi.single i (1 : ℝ) : Space) := by
    ext i
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    fin_cases i <;> simp
  rw [hy, map_sum]
  simp only [map_smul, hd, smul_zero, Finset.sum_const_zero, zero_apply]

theorem unique_in_comparison {ν : ℝ} (hν : 0 ≤ ν) {f U : Velocity}
    (hU : ZeroDataSolution ν f U (fun _ _ => 0)) (hUC : ComparisonClass U (fun _ _ => 0)) :
    UniqueInComparison ν f U := by
  intro u p hu hc
  obtain ⟨Vu, Wu, hVu, _, hdu⟩ := hc.2.1
  obtain ⟨VU, WU, hVU, _, hdU⟩ := hUC.2.1
  let V : ℝ → Lp Space 2 (volume : Measure Space) := fun t => Vu t - VU t
  let W : ℝ → Lp Space 2 (volume : Measure Space) := fun t => Wu t - WU t
  have hV : ContinuousOn V (Ici 0) := hVu.sub hVU
  have hv (t : ℝ) (ht : 0 ≤ t) : (V t : Space → Space) =ᵐ[volume] fun x => u t x - U t x :=
    (Lp.coeFn_sub _ _).trans ((hdu t ht).1.sub (hdU t ht).1)
  have hw (t : ℝ) (ht : 0 ≤ t) : (W t : Space → Space) =ᵐ[volume] fun x => timeD u t x - timeD U t x :=
    (Lp.coeFn_sub _ _).trans ((hdu t ht).2.1.sub (hdU t ht).2.1)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt V (W t) (Ici 0) t :=
    (hdu t ht).2.2.sub (hdU t ht).2.2
  have hzero : V 0 = 0 := by
    apply Lp.ext
    filter_upwards [hv 0 le_rfl, Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx hy
    rw [hx, hu.2.2.1, hU.2.2.1, sub_self, hy]
    rfl
  have he : ∀ t, 0 ≤ t → ∀ x, u t x = U t x := by
    intro T hT
    obtain ⟨C, hC, hbU⟩ := hUC.2.2.1 T hT
    obtain ⟨A, _, hbu⟩ := hc.2.2.1 T hT
    obtain ⟨c, hpc⟩ := hc.2.2.2
    have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
        l2EnergyRate (V t) (W t) ≤ (12 * C) * l2Energy (V t) := by
      have hpair := energy_pairing_bound
        ((sliceH2_of_CH hu.1 hc.1 ht.1).sub (sliceH2_of_CH hU.1 hUC.1 ht.1))
        (Smooth.slice hu.1 ht.1) (Smooth.slice hU.1 ht.1)
        ((Smooth.slice hu.2.1 ht.1).sub contDiff_const) hν hC
        (fun x => (hbu t ⟨ht.1, ht.2.le⟩ x).1)
        (fun x j => (hbu t ⟨ht.1, ht.2.le⟩ x).2 j)
        (fun x j => (hbU t ⟨ht.1, ht.2.le⟩ x).2 j)
        (hu.2.2.2.1 t ht.1)
        (difference_divergence hu.1 hU.1 ht.1 (hu.2.2.2.1 t ht.1) (hU.2.2.2.1 t ht.1))
        (CH.memLp hpc [] (by simp) ht.1) (fun j => CH.memLp hpc [j] (by simp) ht.1)
        (difference_equation hu hU ht.1 (c t))
      simp only [l2EnergyRate, l2Inner_integral (hv t ht.1) (hw t ht.1),
        l2Energy_integral (hv t ht.1), Pi.sub_apply]
      simpa only [Pi.sub_apply, ← mul_assoc, show (2 : ℝ) * 6 = 12 from by norm_num] using
        mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have hz := l2Energy_eq_zero_of_bound hV hd hzero hT hbound
    have hzv := l2Energy_zero_pointwise (hv T hT)
      ((Smooth.slice hu.1 hT).continuous.sub (Smooth.slice hU.1 hT).continuous) hz
    intro x
    exact sub_eq_zero.mp (congrFun hzv x)
  exact ⟨he, constant_pressure_of_velocity_eq hu hU he⟩

end BalancedTransport.Analysis
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set

def loadingSwitch (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

lemma loadingSwitch_contDiff : ContDiff ℝ (⊤ : ℕ∞) loadingSwitch := by
  unfold loadingSwitch
  fun_prop

lemma loadingSwitch_nonneg (t : ℝ) : 0 ≤ loadingSwitch t :=
  Real.smoothTransition.nonneg _

lemma loadingSwitch_le_one (t : ℝ) : loadingSwitch t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma loadingSwitch_zero {t : ℝ} (ht : t ≤ 1 / 4) : loadingSwitch t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma loadingSwitch_one {t : ℝ} (ht : 3 / 4 ≤ t) : loadingSwitch t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def loadingCenter (z : Space) (t : ℝ) : Space := loadingSwitch t • (z - fixedLabel)

def loadingVelocity (z : Space) (η : ℝ) : Velocity :=
  movingBoxVelocity fixedLabel fixedLabel (loadingCenter z) (fun _ => 1) η

def loadingPath (z : Space) : ℝ → Space :=
  affinePath (loadingCenter z) (fun _ => 1) fixedLabel

lemma loadingCenter_contDiff (z : Space) : ContDiff ℝ (⊤ : ℕ∞) (loadingCenter z) :=
  loadingSwitch_contDiff.smul contDiff_const

lemma loadingVelocity_jointSmooth (z : Space) (η : ℝ) :
    JointSmooth (loadingVelocity z η) :=
  movingBoxVelocity_jointSmooth (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) _ _ _

lemma loadingVelocity_divergence (z : Space) (η t : ℝ) (x : Space) :
    div (loadingVelocity z η) t x = 0 :=
  movingBoxVelocity_divergence (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) _ _ _ _ _

lemma loadingCenter_deriv_zero {z : Space} {t : ℝ} (ht : t < 1 / 4 ∨ 3 / 4 < t) :
    deriv (loadingCenter z) t = 0 := by
  rcases ht with ht | ht
  · have he : loadingCenter z =ᶠ[𝓝 t] fun _ => (0 : Space) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [loadingCenter, loadingSwitch_zero hs.le]
    rw [he.deriv_eq, deriv_const]
  · have he : loadingCenter z =ᶠ[𝓝 t] fun _ => z - fixedLabel := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [loadingCenter, loadingSwitch_one hs.le]
    rw [he.deriv_eq, deriv_const]

lemma loadingVelocity_zero {z : Space} {η t : ℝ} (ht : t < 1 / 4 ∨ 3 / 4 < t) :
    loadingVelocity z η t = 0 :=
  movingBoxVelocity_zero (loadingCenter_deriv_zero ht) (by intros; simp)

lemma loadingPath_hasDerivAt (z : Space) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (loadingPath z) (loadingVelocity z η t (loadingPath z t)) t :=
  affinePath_hasDerivAt hη (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) (by intros; simp) (by exact ⟨le_rfl, le_rfl⟩) t

lemma loadingPath_eq (z : Space) (t : ℝ) (i : Fin 3) :
    loadingPath z t i = (1 - loadingSwitch t) * fixedLabel i + loadingSwitch t * z i := by
  dsimp [loadingPath, affinePath, loadingCenter]
  ring

lemma loadingPath_start (z : Space) : loadingPath z 0 = fixedLabel := by
  ext i
  rw [loadingPath_eq, loadingSwitch_zero (by norm_num)]
  ring

lemma loadingPath_end (z : Space) : loadingPath z 1 = z := by
  ext i
  rw [loadingPath_eq, loadingSwitch_one (by norm_num)]
  ring

lemma loadingPath_between (z : Space) (t : ℝ) (i : Fin 3) :
    min (fixedLabel i) (z i) ≤ loadingPath z t i ∧
      loadingPath z t i ≤ max (fixedLabel i) (z i) := by
  rw [loadingPath_eq]
  have h₀ := loadingSwitch_nonneg t
  have h₁ := loadingSwitch_le_one t
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (min_le_right (fixedLabel i) (z i))) h₀]
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (le_max_right (fixedLabel i) (z i))) h₀]

def loadingSupport (z : Space) (η : ℝ) : Set Space :=
  closedEnlargement (fun i => min (fixedLabel i) (z i))
    (fun i => max (fixedLabel i) (z i)) (2 * η)

lemma loadingSupport_compact (z : Space) (η : ℝ) : IsCompact (loadingSupport z η) :=
  isCompact_Icc

lemma loadingVelocity_supported (z : Space) {η : ℝ} (hη : 0 < η) :
    SpatiallySupported (loadingSupport z η) (loadingVelocity z η) := by
  intro t x hx
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  apply hx
  have hh := tsupport_movingBoxVelocity_subset fixedLabel fixedLabel
      (loadingCenter z) (fun _ => 1) hη t ht
  unfold loadingSupport
  rw [mem_closedEnlargement] at hh ⊢
  intro i
  have hbound := loadingPath_between z t i
  have hpoint : lowerEndpoint fixedLabel (loadingCenter z) (fun _ => 1) t = loadingPath z t := rfl
  rw [hpoint] at hh
  constructor <;> linarith [(hh i).1, (hh i).2]

lemma loadingVelocity_repeats (z : Space) (η : ℝ) : RepeatsAfter 1 (loadingVelocity z η) := by
  intro t ht
  rw [loadingVelocity_zero (Or.inr (by linarith)),
    loadingVelocity_zero (Or.inr (by linarith))]

lemma loadingVelocity_boundedMixed (z : Space) {η : ℝ} (hη : 0 < η) :
    BoundedMixed (loadingVelocity z η) :=
  boundedMixed_of_compact_repeating (loadingSupport_compact z η)
    (loadingVelocity_jointSmooth z η) (loadingVelocity_supported z hη)
    (loadingVelocity_repeats z η)

theorem loadingPath_avoids_observer {z : Space} (hz : 4 ≤ z 0) (t : ℝ) :
    loadingPath z t ∉ observer := by
  intro h
  have hh : loadingPath z t 0 < 2 := (Set.mem_pi.mp h 0 (Set.mem_univ _)).2
  have hb := (loadingPath_between z t 0).1
  have hf : fixedLabel 0 = 4 := rfl
  rw [hf, min_eq_left hz] at hb
  linarith

theorem loading_realization (z : Space) {η : ℝ} (hη : 0 < η) :
    JointSmooth (loadingVelocity z η) ∧
    SpatiallySupported (loadingSupport z η) (loadingVelocity z η) ∧
    BoundedMixed (loadingVelocity z η) ∧
    (∀ x, loadingVelocity z η 0 x = 0) ∧
    loadingPath z 0 = fixedLabel ∧ loadingPath z 1 = z ∧
    (∀ t, HasDerivAt (loadingPath z) (loadingVelocity z η t (loadingPath z t)) t) ∧
    (4 ≤ z 0 → ∀ t, loadingPath z t ∉ observer) ∧
    ∀ ν : ℝ, ZeroDataSolution ν
      (affineForce (inertialCoefficient (loadingVelocity z η))
        (viscousCoefficient (loadingVelocity z η)) ν)
      (loadingVelocity z η) (fun _ _ => 0) := by
  have hzero : ∀ x, loadingVelocity z η 0 x = 0 := by
    intro x
    rw [loadingVelocity_zero (Or.inl (by norm_num))]
    rfl
  exact ⟨loadingVelocity_jointSmooth z η, loadingVelocity_supported z hη,
    loadingVelocity_boundedMixed z hη, hzero, loadingPath_start z, loadingPath_end z,
    loadingPath_hasDerivAt z hη, fun hz t => loadingPath_avoids_observer hz t,
    fun ν => residual_zero_pressure_solution ν _ (loadingVelocity_jointSmooth z η).smooth hzero
      (fun t _ x => loadingVelocity_divergence z η t x)⟩

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_curve_on_interval {v : ℝ → E → E} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => v t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖v t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧ Continuous γ ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt γ (v t (γ t)) (Icc 0 T) t := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  let R : ℝ≥0 := ⟨(L : ℝ) * T, mul_nonneg L.coe_nonneg hT⟩
  have hp : IsPicardLindelof v t₀ a R 0 L K := by
    constructor
    · intro t ht
      exact (hl t ht.1).lipschitzOnWith
    · intro x _
      exact (hc x).mono Icc_subset_Ici_self
    · intro t ht x _
      exact hb t ht.1 x
    · change (L : ℝ) * max (T - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (L : ℝ) * T - 0
      simp [t₀, max_eq_left hT]
  have ha : a ∈ closedBall a (0 : ℝ≥0) := by simp
  obtain ⟨γ, hγ⟩ := ODE.FunSpace.exists_isFixedPt_next hp ha
  have he : ∀ t ∈ Icc (0 : ℝ) T,
      γ.compProj t = ODE.picard v 0 a γ.compProj t := by
    intro t ht
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact (ODE.FunSpace.isFixedPt_next_iff hp ha).mp hγ ⟨t, ht⟩
  refine ⟨γ.compProj, ?_, γ.continuous_compProj, fun t ht => ?_⟩
  · rw [he 0 ⟨le_rfl, hT⟩, ODE.picard_apply₀]
  · exact (ODE.hasDerivWithinAt_picard_Icc ⟨le_rfl, hT⟩ hp.continuousOn_uncurry
      γ.continuous_compProj.continuousOn
      (fun s hs => γ.compProj_mem_closedBall hp.mul_max_le) a ht).congr
      he (he t ht)

omit [CompleteSpace E] in
lemma hasDerivWithinAt_forward_of_Icc {γ : ℝ → E} {d : E} {t T : ℝ}
    (hd : HasDerivWithinAt γ d (Icc 0 T) t) (ht : t < T) :
    HasDerivWithinAt γ d (Ici 0) t := by
  apply hd.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs₀ hs₁
  exact ⟨hs₀, hs₁.le⟩

omit [CompleteSpace E] in
lemma curves_agree_on_overlap {v : ℝ → E → E} {K : ℝ≥0}
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    {γ δ : ℝ → E} {S T : ℝ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) S))
    (hδ : ContinuousOn δ (Icc (0 : ℝ) T))
    (hdγ : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt γ (v t (γ t)) (Icc 0 S) t)
    (hdδ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt δ (v t (δ t)) (Icc 0 T) t)
    (hinit : γ 0 = δ 0) {t : ℝ} (ht : 0 ≤ t) (htS : t ≤ S) (htT : t ≤ T) :
    γ t = δ t := by
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
      (fun s hs => (hl s hs.1).lipschitzOnWith)
      (hγ.mono (Icc_subset_Icc_right htS)) _ (fun _ _ => mem_univ _)
      (hδ.mono (Icc_subset_Icc_right htT)) _ (fun _ _ => mem_univ _) hinit ⟨ht, le_rfl⟩
  · intro s hs
    exact (hasDerivWithinAt_forward_of_Icc (hdγ s ⟨hs.1, hs.2.le.trans htS⟩)
      (hs.2.trans_le htS)).mono (Ici_subset_Ici.mpr hs.1)
  · intro s hs
    exact (hasDerivWithinAt_forward_of_Icc (hdδ s ⟨hs.1, hs.2.le.trans htT⟩)
      (hs.2.trans_le htT)).mono (Ici_subset_Ici.mpr hs.1)

theorem exists_global_curve {v : ℝ → E → E} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => v t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖v t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t)) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧
      ∀ t, 0 ≤ t → HasDerivWithinAt γ (v t (γ t)) (Ici 0) t := by
  have hex (n : ℕ) := exists_curve_on_interval hc hb hl
    (T := (n : ℝ) + 1) (by positivity) a
  choose C hC₀ hCcts hCd using hex
  have hagree (m n : ℕ) {t : ℝ} (ht : 0 ≤ t)
      (htm : t ≤ (m : ℝ) + 1) (htn : t ≤ (n : ℝ) + 1) : C m t = C n t :=
    curves_agree_on_overlap hl (hCcts m).continuousOn (hCcts n).continuousOn
      (hCd m) (hCd n) ((hC₀ m).trans (hC₀ n).symm) ht htm htn
  let γ : ℝ → E := fun t => C ⌈t⌉₊ t
  have heq (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ (n : ℝ) + 1) : γ t = C n t :=
    hagree ⌈t⌉₊ n ht (by linarith [Nat.le_ceil t]) htn
  refine ⟨γ, hC₀ _, fun t ht => ?_⟩
  let n := ⌈t⌉₊
  have htlt : t < (n : ℝ) + 1 := by dsimp [n]; linarith [Nat.le_ceil t]
  have hd := hasDerivWithinAt_forward_of_Icc (hCd n t ⟨ht, htlt.le⟩) htlt
  have hne : γ =ᶠ[𝓝[Ici 0] t] C n := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlt)] with s hs₀ hs₁
    exact heq n hs₀ hs₁.le
  rw [heq n ht htlt.le]
  exact hd.congr_of_eventuallyEq hne (heq n ht htlt.le)

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric

theorem exists_materialFlow_of_bounded_lipschitz {U : Velocity} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => U t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖U t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (U t)) :
    ∃ X : MaterialFlow, IsMaterialFlow U X := by
  choose γ hγ₀ hγd using exists_global_curve hc hb hl
  exact ⟨fun t a => γ a t, hγ₀, hγd⟩

theorem materialFlow_unique {U : Velocity} {X Y : MaterialFlow} {K : ℝ≥0}
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (U t))
    (hX : IsMaterialFlow U X) (hY : IsMaterialFlow U Y)
    {t : ℝ} (ht : 0 ≤ t) (a : Space) : X t a = Y t a := by
  apply curves_agree_on_overlap hl
      (HasDerivWithinAt.continuousOn (fun s hs => (hX.2 a s hs.1).mono Icc_subset_Ici_self))
      (HasDerivWithinAt.continuousOn (fun s hs => (hY.2 a s hs.1).mono Icc_subset_Ici_self))
      (fun s hs => (hX.2 a s hs.1).mono Icc_subset_Ici_self)
      (fun s hs => (hY.2 a s hs.1).mono Icc_subset_Ici_self)
      ((hX.1 a).trans (hY.1 a).symm) ht le_rfl le_rfl

lemma norm_linearMap_le_sum_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Space →L[ℝ] F) : ‖A‖ ≤ ∑ i : Fin 3, ‖A (Pi.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have he : A x = ∑ i : Fin 3, x i • A (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [he]
  calc
    ‖∑ i : Fin 3, x i • A (Pi.single i 1)‖ ≤
        ∑ i : Fin 3, ‖x i • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (Pi.single i 1)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (Pi.single i 1)‖) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

lemma spatial_lipschitz_of_boundedMixed {U : Velocity}
    (hU : JointSmooth U) (hb : BoundedMixed U) :
    ∃ K : ℝ≥0, ∀ t, 0 ≤ t → LipschitzWith K (U t) := by
  choose C hC hbound using fun i : Fin 3 => hb [some i]
  let K : ℝ≥0 := ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i)⟩
  refine ⟨K, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    ((hU.slice t).differentiable (by simp)) (fun x => ?_)⟩
  change ‖fderiv ℝ (U t) x‖ ≤ ∑ i, C i
  apply (norm_linearMap_le_sum_basis _).trans
  exact Finset.sum_le_sum (fun i _ => hbound i t ht x)

theorem exists_materialFlow_of_boundedMixed {U : Velocity}
    (hU : JointSmooth U) (hb : BoundedMixed U) :
    ∃ X : MaterialFlow, IsMaterialFlow U X := by
  obtain ⟨L, hL, hbound⟩ := hb []
  obtain ⟨K, hK⟩ := spatial_lipschitz_of_boundedMixed hU hb
  apply exists_materialFlow_of_bounded_lipschitz (L := ⟨L, hL⟩) (K := K)
  · intro x
    exact (hU.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  · exact hbound
  · exact hK

theorem exists_materialFlow_of_compact_repeating {K : Set Space} (hK : IsCompact K)
    {U : Velocity} (hU : JointSmooth U) (hs : SpatiallySupported K U)
    (hp : RepeatsAfter 1 U) : ∃ X : MaterialFlow, IsMaterialFlow U X :=
  exists_materialFlow_of_boundedMixed hU (boundedMixed_of_compact_repeating hK hU hs hp)

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set

def TimeCollars {F : Type*} [Zero F] (v : Field F) : Prop :=
  ∀ t, t < 1 / 4 ∨ 3 / 4 < t → v t = 0

def repeatTemplate (v : Velocity) : Velocity :=
  fun t x => ∑' n : ℤ, v (t - n) x

lemma repeatTemplate_eq {v : Velocity} (hc : TimeCollars v) {t : ℝ} {n : ℤ}
    (ht : t - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4)) (x : Space) :
    repeatTemplate v t x = v (t - n) x := by
  apply tsum_eq_single n
  intro m hmn
  have hzero : v (t - m) = 0 := by
    apply hc
    rcases lt_or_gt_of_ne hmn with hm | hm
    · right
      have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast Int.add_one_le_iff.mpr hm
      linarith [ht.1]
    · left
      have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast Int.add_one_le_iff.mpr hm
      linarith [ht.2]
  rw [hzero]
  rfl

lemma repeatTemplate_zero_period (v : Velocity) : Function.Periodic (repeatTemplate v) 1 := by
  intro t
  funext x
  change (∑' n : ℤ, v (t + 1 - n) x) = ∑' n : ℤ, v (t - n) x
  have hh := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => v (t + 1 - n) x)
  simpa only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub] using hh.symm

lemma repeatTemplate_on_unit {v : Velocity} (hc : TimeCollars v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : repeatTemplate v t = v t := by
  funext x
  simpa using repeatTemplate_eq hc (n := 0) (by norm_num; constructor <;> linarith [ht.1, ht.2]) x

lemma repeatTemplate_jointSmooth {v : Velocity} (hv : JointSmooth v) (hc : TimeCollars v) :
    JointSmooth (repeatTemplate v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  let n : ℤ := ⌊z.1⌋
  have ht : z.1 - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4) := by
    have h₁ := Int.floor_le z.1
    have h₂ := Int.lt_floor_add_one z.1
    change -1 / 4 < z.1 - (⌊z.1⌋ : ℤ) ∧ z.1 - (⌊z.1⌋ : ℤ) < 5 / 4
    constructor <;> linarith
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × Space => v (y.1 - n) y.2) :=
    hv.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  apply hg.contDiffAt.congr_of_eventuallyEq
  have hnn : ∀ᶠ y : ℝ × Space in 𝓝 z, y.1 - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4) :=
    ((continuous_fst.sub continuous_const).continuousAt).eventually (isOpen_Ioo.mem_nhds ht)
  exact hnn.mono (fun y hy => repeatTemplate_eq hc hy y.2)

lemma repeatTemplate_supported {K : Set Space} {v : Velocity} (hs : SpatiallySupported K v) :
    SpatiallySupported K (repeatTemplate v) := by
  intro t x hx
  simp only [repeatTemplate, hs _ x hx, tsum_zero]

lemma repeatTemplate_divergence {v : Velocity} (hc : TimeCollars v)
    (hd : ∀ t x, div v t x = 0) (t : ℝ) (x : Space) :
    div (repeatTemplate v) t x = 0 := by
  have he : repeatTemplate v t = v (t - (⌊t⌋ : ℤ)) := by
    funext y
    apply repeatTemplate_eq hc
    have h₁ := Int.floor_le t
    have h₂ := Int.lt_floor_add_one t
    constructor <;> linarith
  simpa only [div, spaceD, he] using hd (t - (⌊t⌋ : ℤ)) x

def afterLoadingGate (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 3)

def loadedRepeat (load template : Velocity) : Velocity :=
  fun t x => load t x + afterLoadingGate t • repeatTemplate template t x

lemma loadedRepeat_jointSmooth {load v : Velocity} (hl : JointSmooth load)
    (hv : JointSmooth v) (hc : TimeCollars v) : JointSmooth (loadedRepeat load v) := by
  have hg : JointSmooth (fun t (_ : Space) => afterLoadingGate t) := by
    dsimp [JointSmooth, afterLoadingGate]
    fun_prop
  exact hl.add (hg.smul (repeatTemplate_jointSmooth hv hc))

lemma loadedRepeat_before {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : loadedRepeat load v t = load t := by
  have hs : afterLoadingGate t • repeatTemplate v t = (0 : Space → Space) := by
    by_cases ht : t ≤ 3 / 4
    · have he : afterLoadingGate t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [he, zero_smul]
    · rw [repeatTemplate_on_unit hc ⟨ht₀, ht₁⟩, hc t (Or.inr (lt_of_not_ge ht)), smul_zero]
  ext x i
  change (load t x + (afterLoadingGate t • repeatTemplate v t) x) i = load t x i
  rw [hs]
  simp

lemma loadedRepeat_after {load v : Velocity} (hl : TimeCollars load)
    {t : ℝ} (ht : 1 ≤ t) : loadedRepeat load v t = repeatTemplate v t := by
  have he : afterLoadingGate t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  ext x i
  simp [loadedRepeat, he, hl t (Or.inr (by linarith))]

lemma loadedRepeat_support {K L : Set Space} {load v : Velocity}
    (hl : SpatiallySupported L load) (hv : SpatiallySupported K v) :
    SpatiallySupported (L ∪ K) (loadedRepeat load v) := by
  intro t x hx
  have hn := not_or.mp hx
  dsimp [loadedRepeat]
  rw [hl t x hn.1, repeatTemplate_supported hv t x hn.2, smul_zero, add_zero]

lemma loadedRepeat_repeats {load v : Velocity} (hl : TimeCollars load) :
    RepeatsAfter 1 (loadedRepeat load v) := by
  intro t ht
  rw [loadedRepeat_after hl (by linarith), loadedRepeat_after hl ht]
  exact repeatTemplate_zero_period v t

lemma div_add {u v : Velocity} (hu : JointSmooth u) (hv : JointSmooth v) (t : ℝ) (x : Space) :
    div (fun t x => u t x + v t x) t x = div u t x + div v t x := by
  simp only [div, spaceD,
    fderiv_fun_add ((hu.slice t).differentiable (by simp) x)
      ((hv.slice t).differentiable (by simp) x), add_apply, Pi.add_apply, Finset.sum_add_distrib]

lemma div_time_smul {u : Velocity} (hu : JointSmooth u) (a : ℝ → ℝ) (t : ℝ) (x : Space) :
    div (fun t x => a t • u t x) t x = a t * div u t x := by
  simp only [div, spaceD, fderiv_fun_const_smul ((hu.slice t).differentiable (by simp) x),
    smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma loadedRepeat_divergence {load v : Velocity} (hl : JointSmooth load)
    (hv : JointSmooth v) (hc : TimeCollars v)
    (hld : ∀ t x, div load t x = 0) (hvd : ∀ t x, div v t x = 0) (t : ℝ) (x : Space) :
    div (loadedRepeat load v) t x = 0 := by
  have hr := repeatTemplate_jointSmooth hv hc
  have hg : JointSmooth (fun t (_ : Space) => afterLoadingGate t) := by
    dsimp [JointSmooth, afterLoadingGate]
    fun_prop
  change div (fun t x => load t x + afterLoadingGate t • repeatTemplate v t x) t x = 0
  have hgr : JointSmooth (fun t x => afterLoadingGate t • repeatTemplate v t x) := hg.smul hr
  rw [div_add hl hgr, div_time_smul hr, hld t x, repeatTemplate_divergence hc hvd]
  ring

theorem loaded_template_realization (z : Space) {η : ℝ} (hη : 0 < η)
    {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hd : ∀ t x, div v t x = 0) :
    let U := loadedRepeat (loadingVelocity z η) v
    JointSmooth U ∧ SpatiallySupported (loadingSupport z η ∪ K) U ∧
    BoundedMixed U ∧ (∀ x, U 0 x = 0) ∧
    Function.Periodic (repeatTemplate v) 1 ∧
    (∀ t, 1 ≤ t → U t = repeatTemplate v t) ∧
    (∃ X, IsMaterialFlow U X) ∧
    ∀ ν : ℝ, ZeroDataSolution ν
      (affineForce (inertialCoefficient U) (viscousCoefficient U) ν) U (fun _ _ => 0) := by
  let load := loadingVelocity z η
  have hl : JointSmooth load := loadingVelocity_jointSmooth z η
  have hlc : TimeCollars load := fun _ ht => loadingVelocity_zero ht
  have hU := loadedRepeat_jointSmooth hl hv hc
  have hUs := loadedRepeat_support (loadingVelocity_supported z hη) hs
  have hUp := loadedRepeat_repeats (v := v) hlc
  have hUc := (loadingSupport_compact z η).union hK
  have hzero : ∀ x, loadedRepeat load v 0 x = 0 := by
    intro x
    rw [loadedRepeat_before hc le_rfl (by norm_num), hlc 0 (Or.inl (by norm_num))]
    rfl
  exact ⟨hU, hUs, boundedMixed_of_compact_repeating hUc hU hUs hUp, hzero,
    repeatTemplate_zero_period v, fun _ ht => loadedRepeat_after hlc ht,
    exists_materialFlow_of_compact_repeating hUc hU hUs hUp,
    fun ν => residual_zero_pressure_solution ν _ hU.smooth hzero
      (fun t _ x => loadedRepeat_divergence hl hv hc (loadingVelocity_divergence z η) hd t x)⟩

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

theorem prescribed_residual_realization {K : Set Space} (hK : IsCompact K)
    {U : Velocity} (hU : JointSmooth U) (hs : SpatiallySupported K U)
    (hp : RepeatsAfter 1 U) (hzero : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    Smooth U ∧ Smooth (inertialCoefficient U) ∧ Smooth (viscousCoefficient U) ∧
    CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ BoundedMixed (inertialCoefficient U) ∧ BoundedMixed (viscousCoefficient U) ∧
    PeriodicAfterOne U ∧ ComparisonClass U (fun _ _ => 0) ∧
    (∃ X, IsMaterialFlow U X ∧ ∀ Y, IsMaterialFlow U Y →
      ∀ t, 0 ≤ t → ∀ x, X t x = Y t x) ∧
    ∀ ν : ℝ, 0 < ν → let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧ UniqueInComparison ν f U := by
  obtain ⟨hf₀, hf₁, hsupport, hbound, hb₀, hb₁, hperiod, hres⟩ :=
    prescribed_residual_regularity hK hU hs hp hzero hdiv
  have hclass := comparisonClass_of_compact_boundedMixed hK hU hs hbound
  obtain ⟨X, hX⟩ := exists_materialFlow_of_boundedMixed hU hbound
  obtain ⟨K', hK'⟩ := spatial_lipschitz_of_boundedMixed hU hbound
  refine ⟨hU.smooth, hf₀, hf₁, hsupport, hbound, hb₀, hb₁, hperiod, hclass,
    ⟨X, hX, fun Y hY t ht x => materialFlow_unique hK' hX hY ht x⟩, ?_⟩
  intro ν hν
  obtain ⟨hsol, hsm, hb, hp'⟩ := hres ν
  exact ⟨hsol, hsm, hb, hp', Analysis.unique_in_comparison hν.le hsol hclass⟩

theorem loaded_template_analytic_realization (z : Space) {η : ℝ} (hη : 0 < η)
    {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hd : ∀ t x, div v t x = 0) :
    let U := loadedRepeat (loadingVelocity z η) v
    Smooth U ∧ CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ ComparisonClass U (fun _ _ => 0) ∧
    Function.Periodic (repeatTemplate v) 1 ∧
    (∀ t, 1 ≤ t → U t = repeatTemplate v t) ∧
    (∃ X, IsMaterialFlow U X) ∧
    ∀ ν : ℝ, 0 < ν → let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧ UniqueInComparison ν f U := by
  obtain ⟨hU, hUs, _, hzero, hrep, heq, hflow, _⟩ :=
    loaded_template_realization z hη hK hv hc hs hd
  have hlc : TimeCollars (loadingVelocity z η) := fun _ ht => loadingVelocity_zero ht
  have hdiv := fun t (_ : 0 ≤ t) x =>
    loadedRepeat_divergence (loadingVelocity_jointSmooth z η) hv hc
      (loadingVelocity_divergence z η) hd t x
  have hr := prescribed_residual_realization ((loadingSupport_compact z η).union hK)
    hU hUs (loadedRepeat_repeats (v := v) hlc) hzero hdiv
  exact ⟨hr.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
    hrep, heq, hflow, hr.2.2.2.2.2.2.2.2.2.2⟩

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

@[ext] structure BoxLayout (ι : Type*) where
  center : ι → Space
  width : ι → Space

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

def Positive (A : BoxLayout ι) : Prop := ∀ i k, 0 < A.width i k

def Separated (A : BoxLayout ι) (η : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ k, A.width i k + A.width j k + 4 * η < |A.center i k - A.center j k|

def Guarded (A : BoxLayout ι) (safe : Set ι) : Prop :=
  ∀ i ∈ safe, 2 < A.center i 0 - A.width i 0

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

structure BoxMotion (A B : BoxLayout ι) (safe : Set ι) (η : ℝ) where
  center : ℝ → ι → Space
  width : ℝ → ι → Space
  smooth_center : ContDiff ℝ (⊤ : ℕ∞) center
  smooth_width : ContDiff ℝ (⊤ : ℕ∞) width
  start_center : ∀ t, t ≤ 0 → center t = A.center
  start_width : ∀ t, t ≤ 0 → width t = A.width
  end_center : ∀ t, 1 ≤ t → center t = B.center
  end_width : ∀ t, 1 ≤ t → width t = B.width
  positive : ∀ t i k, 0 < width t i k
  volume : ∀ t i, ∏ k, width t i k = ∏ k, A.width i k
  separation : ∀ t, (BoxLayout.mk (center t) (width t)).Separated η
  guard : ∀ t, (BoxLayout.mk (center t) (width t)).Guarded safe

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma positive_start (m : BoxMotion A B safe η) : A.Positive := by
  have hh := m.positive 0
  rwa [m.start_width 0 le_rfl] at hh

lemma positive_end (m : BoxMotion A B safe η) : B.Positive := by
  have hh := m.positive 1
  rwa [m.end_width 1 le_rfl] at hh

lemma volume_end (m : BoxMotion A B safe η) (i : ι) :
    ∏ k, B.width i k = ∏ k, A.width i k := by
  simpa only [m.end_width 1 le_rfl] using m.volume 1 i

def stationary (hp : A.Positive) (hs : A.Separated η) (hg : A.Guarded safe) :
    BoxMotion A A safe η where
  center := fun _ => A.center
  width := fun _ => A.width
  smooth_center := contDiff_const
  smooth_width := contDiff_const
  start_center := fun _ _ => rfl
  start_width := fun _ _ => rfl
  end_center := fun _ _ => rfl
  end_width := fun _ _ => rfl
  positive := fun _ => hp
  volume := by intros; rfl
  separation := fun _ => hs
  guard := fun _ => hg

private def joinedCenter (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    (t : ℝ) : ι → Space := m.center (2 * t) + n.center (2 * t - 1) - B.center

private def joinedWidth (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    (t : ℝ) (i : ι) (k : Fin 3) : ℝ :=
  m.width (2 * t) i k * n.width (2 * t - 1) i k / B.width i k

private lemma joined_left (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    {t : ℝ} (ht : t ≤ 1 / 2) :
    joinedCenter m n t = m.center (2 * t) ∧ joinedWidth m n t = m.width (2 * t) := by
  have h := n.start_center (2 * t - 1) (by linarith)
  have hw := n.start_width (2 * t - 1) (by linarith)
  constructor
  · simp [joinedCenter, h]
  · ext i k
    simp [joinedWidth, hw, ne_of_gt (m.positive_end i k)]

private lemma joined_right (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    {t : ℝ} (ht : 1 / 2 ≤ t) :
    joinedCenter m n t = n.center (2 * t - 1) ∧ joinedWidth m n t = n.width (2 * t - 1) := by
  have h := m.end_center (2 * t) (by linarith)
  have hw := m.end_width (2 * t) (by linarith)
  constructor
  · simp [joinedCenter, h, add_sub_cancel_left]
  · ext i k
    simp [joinedWidth, hw, mul_div_cancel_left₀ _ (ne_of_gt (m.positive_end i k))]

def trans (m : BoxMotion A B safe η) (n : BoxMotion B C safe η) :
    BoxMotion A C safe η where
  center := joinedCenter m n
  width := joinedWidth m n
  smooth_center := by
    exact ((m.smooth_center.comp (contDiff_const.mul contDiff_id)).add
      (n.smooth_center.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))).sub contDiff_const
  smooth_width := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro k
    exact (((contDiff_pi.mp (contDiff_pi.mp m.smooth_width i) k).comp
      (contDiff_const.mul contDiff_id)).mul
      ((contDiff_pi.mp (contDiff_pi.mp n.smooth_width i) k).comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const))).div_const _
  start_center := by
    intro t ht
    rw [(joined_left m n (by linarith : t ≤ 1 / 2)).1, m.start_center _ (by linarith)]
  start_width := by
    intro t ht
    rw [(joined_left m n (by linarith : t ≤ 1 / 2)).2, m.start_width _ (by linarith)]
  end_center := by
    intro t ht
    rw [(joined_right m n (by linarith : 1 / 2 ≤ t)).1, n.end_center _ (by linarith)]
  end_width := by
    intro t ht
    rw [(joined_right m n (by linarith : 1 / 2 ≤ t)).2, n.end_width _ (by linarith)]
  positive := by
    intro t i k
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).2]; exact m.positive _ _ _
    · rw [(joined_right m n ht).2]; exact n.positive _ _ _
  volume := by
    intro t i
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).2]; exact m.volume _ _
    · rw [(joined_right m n ht).2, n.volume, m.volume_end]
  separation := by
    intro t
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).1, (joined_left m n ht).2]; exact m.separation _
    · rw [(joined_right m n ht).1, (joined_right m n ht).2]; exact n.separation _
  guard := by
    intro t
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).1, (joined_left m n ht).2]; exact m.guard _
    · rw [(joined_right m n ht).1, (joined_right m n ht).2]; exact n.guard _

def reverse (m : BoxMotion A B safe η) : BoxMotion B A safe η where
  center := fun t => m.center (1 - t)
  width := fun t => m.width (1 - t)
  smooth_center := m.smooth_center.comp (contDiff_const.sub contDiff_id)
  smooth_width := m.smooth_width.comp (contDiff_const.sub contDiff_id)
  start_center := fun _ ht => m.end_center _ (by linarith)
  start_width := fun _ ht => m.end_width _ (by linarith)
  end_center := fun _ ht => m.start_center _ (by linarith)
  end_width := fun _ ht => m.start_width _ (by linarith)
  positive := fun _ => m.positive _
  volume := fun _ i => (m.volume _ i).trans (m.volume_end i).symm
  separation := fun _ => m.separation _
  guard := fun _ => m.guard _

end BalancedTransport.Geometry.BoxMotion
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

def segmentLayout (a b w : ι → Space) (r : ℝ) : BoxLayout ι :=
  ⟨fun i k => (1 - r) * a i k + r * b i k, w⟩

omit [Fintype ι] in
lemma segmentLayout_start (a b w : ι → Space) : segmentLayout a b w 0 = ⟨a, w⟩ := by
  ext i k <;> simp [segmentLayout]

omit [Fintype ι] in
lemma segmentLayout_end (a b w : ι → Space) : segmentLayout a b w 1 = ⟨b, w⟩ := by
  ext i k <;> simp [segmentLayout]

def segmentMotion {a b w : ι → Space} {safe : Set ι} {η : ℝ}
    (hp : ∀ i k, 0 < w i k)
    (hs : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Separated η)
    (hg : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Guarded safe) :
    BoxMotion ⟨a, w⟩ ⟨b, w⟩ safe η where
  center := fun t => (segmentLayout a b w (Real.smoothTransition t)).center
  width := fun _ => w
  smooth_center := by
    unfold segmentLayout
    fun_prop
  smooth_width := contDiff_const
  start_center := by
    intro t ht
    simp [segmentLayout, Real.smoothTransition.zero_of_nonpos ht]
  start_width := by intros; rfl
  end_center := by
    intro t ht
    simp [segmentLayout, Real.smoothTransition.one_of_one_le ht]
  end_width := by intros; rfl
  positive := fun _ => hp
  volume := by intros; rfl
  separation := fun _ => hs _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  guard := fun _ => hg _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

omit [Fintype ι] in
lemma segment_guard {a b w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (hb : (BoxLayout.mk b w).Guarded safe)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : (segmentLayout a b w r).Guarded safe := by
  intro i hi
  have hh₀ := ha i hi
  have hh₁ := hb i hi
  change 2 < (1 - r) * a i 0 + r * b i 0 - w i 0
  by_cases he : r = 1
  · simpa [he] using hh₁
  · have h₀ : 0 < 1 - r := sub_pos.mpr (lt_of_le_of_ne hr.2 he)
    nlinarith [mul_pos (sub_pos.mpr hh₀) h₀,
      mul_nonneg (sub_nonneg.mpr (le_of_lt hh₁)) hr.1]

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def CenterSeparated (a : ι → Space) (D : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ k, D < |a i k - a j k|

omit [Fintype ι] in
lemma CenterSeparated.update {a : ι → Space} {D : ℝ} (ha : CenterSeparated a D)
    (i : ι) (b : Space) (hb : ∀ j, j ≠ i → ∃ k, D < |b k - a j k|) :
    CenterSeparated (Function.update a i b) D := by
  intro j k hjk
  by_cases hji : j = i
  · subst j
    simpa [Function.update_of_ne (Ne.symm hjk)] using hb k (Ne.symm hjk)
  · by_cases hki : k = i
    · subst k
      obtain ⟨l, hl⟩ := hb j hji
      exact ⟨l, by simpa [Function.update_of_ne hji, abs_sub_comm] using hl⟩
    · simpa [Function.update_of_ne hji, Function.update_of_ne hki] using ha j k hjk

omit [Fintype ι] [DecidableEq ι] in
lemma separated_of_centerSeparated {a w : ι → Space} {D η : ℝ}
    (ha : CenterSeparated a D) (hw : ∀ i j k, w i k + w j k + 4 * η ≤ D) :
    (BoxLayout.mk a w).Separated η := by
  intro i j hij
  obtain ⟨k, hk⟩ := ha i j hij
  exact ⟨k, lt_of_le_of_lt (hw i j k) hk⟩

omit [Fintype ι] in
lemma segment_center_eq {a : ι → Space} (i : ι) (b _w : Space) (r : ℝ) :
    (fun j k => (1 - r) * a j k + r * (Function.update a i b) j k) =
      Function.update a i (fun k => (1 - r) * a i k + r * b k) := by
  ext j k
  by_cases hji : j = i
  · subst j; simp
  · simp only [Function.update_of_ne hji]
    ring

def singleSegmentMotion {a w : ι → Space} {D η : ℝ} {safe : Set ι}
    (i : ι) (b : Space) (hp : ∀ j k, 0 < w j k)
    (hw : ∀ j l k, w j k + w l k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hb : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * a i k + r * b k - a j k|)
    (hga : (BoxLayout.mk a w).Guarded safe)
    (hgb : (BoxLayout.mk (Function.update a i b) w).Guarded safe) :
    BoxMotion ⟨a, w⟩ ⟨Function.update a i b, w⟩ safe η :=
  segmentMotion hp (by
    intro r hr
    apply separated_of_centerSeparated _ hw
    change CenterSeparated (fun j k => (1 - r) * a j k + r * (Function.update a i b) j k) D
    rw [segment_center_eq i b (0 : Space) r]
    exact ha.update i _ (hb r hr))
    (fun _ hr => segment_guard hga hgb hr)

omit [Fintype ι] in
lemma guarded_update {a w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (i : ι) (b : Space)
    (hb : i ∈ safe → 2 < b 0 - w i 0) :
    (BoxLayout.mk (Function.update a i b) w).Guarded safe := by
  intro j hj
  by_cases hji : j = i
  · subst j; simpa using hb hj
  · simpa [Function.update_of_ne hji] using ha j hj

lemma raising_gap {p q : Space} {H r D : ℝ} (hq : q 1 ≤ p 1) (hH : p 1 ≤ H)
    (hr : r ∈ Icc (0 : ℝ) 1) (hgap : ∃ k, D < |p k - q k|) :
    ∃ k, D < |(1 - r) * p k + r * (Function.update p 1 H) k - q k| := by
  obtain ⟨k, hk⟩ := hgap
  by_cases hk₁ : k = 1
  · subst k
    refine ⟨1, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hq)] at hk
    have hh : 0 ≤ (1 - r) * p 1 + r * H - q 1 := by
      nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hH)]
    simp only [Function.update_self, abs_of_nonneg hh]
    nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hH)]
  · refine ⟨k, ?_⟩
    rw [Function.update_of_ne hk₁]
    convert hk using 1; congr 1; ring

lemma high_plane_gap {p q z : Space} {H r D : ℝ} (hp : p 1 = H) (hq : q 1 = H)
    (hz : D < H - z 1) :
    ∃ k, D < |(1 - r) * p k + r * q k - z k| := by
  refine ⟨1, hz.trans_le ?_⟩
  rw [hp, hq]
  calc
    H - z 1 = (1 - r) * H + r * H - z 1 := by ring
    _ ≤ |(1 - r) * H + r * H - z 1| := le_abs_self _

lemma fixed_first_gap {p q z : Space} {r D : ℝ} (hpq : p 0 = q 0)
    (hz : D < |q 0 - z 0|) :
    ∃ k, D < |(1 - r) * p k + r * q k - z k| := by
  refine ⟨0, ?_⟩
  rw [hpq]
  convert hz using 1; congr 1; ring

def remainingCenters (a p : ι → Space) (S : Finset ι) (i : ι) : Space :=
  if i ∈ S then a i else p i

omit [Fintype ι] in
lemma remainingCenters_separated {a p : ι → Space} {D : ℝ}
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|) (S : Finset ι) :
    CenterSeparated (remainingCenters a p S) D := by
  intro i j hij
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simpa [remainingCenters, hi, hj] using ha i j hij
  · exact ⟨0, by simpa [remainingCenters, hi, hj] using hcross i j⟩
  · exact ⟨0, by simpa [remainingCenters, hi, hj, abs_sub_comm] using hcross j i⟩
  · exact ⟨0, by simpa [remainingCenters, hi, hj] using hp i j hij⟩

omit [Fintype ι] in
lemma remainingCenters_guarded {a p w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (hp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) : (BoxLayout.mk (remainingCenters a p S) w).Guarded safe := by
  intro i hi
  by_cases h : i ∈ S
  · simpa [remainingCenters, h] using ha i hi
  · simpa [remainingCenters, h] using hp i hi

omit [Fintype ι] in
lemma remainingCenters_erase {a p : ι → Space} {S : Finset ι} {i : ι} (_hi : i ∈ S) :
    remainingCenters a p (S.erase i) = Function.update (remainingCenters a p S) i (p i) := by
  ext j k
  by_cases hji : j = i
  · subst j; simp [remainingCenters]
  · simp [remainingCenters, hji]

def evacuateHighest {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) (i : ι) (hi : i ∈ S) (hmax : ∀ j ∈ S, a j 1 ≤ a i 1) :
    BoxMotion ⟨remainingCenters a p S, w⟩ ⟨remainingCenters a p (S.erase i), w⟩ safe η := by
  let u := remainingCenters a p S
  let v₁ := Function.update (a i) 1 H
  let v₂ := Function.update (p i) 1 H
  have hui : u i = a i := by simp [u, remainingCenters, hi]
  have hu := remainingCenters_separated ha hcross hp S
  have hgu := remainingCenters_guarded hga hgp S
  have hv₁ : (BoxLayout.mk (Function.update u i v₁) w).Guarded safe :=
    guarded_update hgu i v₁ (by intro his; simpa [v₁] using hga i his)
  have hv₂ : (BoxLayout.mk (Function.update u i v₂) w).Guarded safe :=
    guarded_update hgu i v₂ (by intro his; simpa [v₂] using hgp i his)
  have hp₃ : (BoxLayout.mk (Function.update u i (p i)) w).Guarded safe :=
    guarded_update hgu i (p i) (fun his => hgp i his)
  have hfirst : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * u i k + r * v₁ k - u j k| := by
    intro r hr j hji
    rw [hui]
    by_cases hj : j ∈ S
    · have huj : u j = a j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact raising_gap (hmax j hj) (by linarith [hhigha i]) hr (ha i j (Ne.symm hji))
    · have huj : u j = p j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact fixed_first_gap (by simp [v₁]) (by simpa [v₁] using hcross i j)
  have hsecond : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₁) i k +
        r * v₂ k - (Function.update u i v₁) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply high_plane_gap (H := H) (by simp [v₁]) (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj] using hhigha j
    · simpa [u, remainingCenters, hj] using hhighp j
  have hthird : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₂) i k +
        r * p i k - (Function.update u i v₂) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply fixed_first_gap (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj, abs_sub_comm] using hcross j i
    · simpa [u, remainingCenters, hj] using hp i j (Ne.symm hji)
  have hsep₁ := hu.update i v₁ (fun j hji => by simpa using hfirst 1 ⟨by norm_num, le_rfl⟩ j hji)
  have hsep₂ : CenterSeparated (Function.update u i v₂) D := by
    have hh := hsep₁.update i v₂ (fun j hji => by simpa using hsecond 1 ⟨by norm_num, le_rfl⟩ j hji)
    simpa [Function.update_idem] using hh
  let m₁ := singleSegmentMotion i v₁ hwidth hsize hu hfirst hgu hv₁
  let m₂ := singleSegmentMotion i v₂ hwidth hsize hsep₁ hsecond hv₁
    (by simpa [Function.update_idem] using hv₂)
  let m₃ := singleSegmentMotion i (p i) hwidth hsize hsep₂ hthird hv₂
    (by simpa [Function.update_idem] using hp₃)
  have m₂' : BoxMotion ⟨Function.update u i v₁, w⟩ ⟨Function.update u i v₂, w⟩ safe η :=
    by simpa [Function.update_idem] using m₂
  have m₃' : BoxMotion ⟨Function.update u i v₂, w⟩ ⟨Function.update u i (p i), w⟩ safe η :=
    by simpa [Function.update_idem] using m₃
  simpa [remainingCenters_erase hi] using (m₁.trans m₂').trans m₃'

def evacuateToParking {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe) :
    BoxMotion ⟨a, w⟩ ⟨p, w⟩ safe η := by
  have h : ∀ S : Finset ι, Nonempty
      (BoxMotion ⟨remainingCenters a p S, w⟩ ⟨p, w⟩ safe η) := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi, hmax⟩ := S.exists_max_image (fun i => a i 1) hS
      obtain ⟨m⟩ := ih (S.erase i) (Finset.erase_ssubset hi)
      exact ⟨(evacuateHighest hwidth hsize ha hcross hp hhigha hhighp hD
        hga hgp S i hi hmax).trans m⟩
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      have hempty : remainingCenters a p ∅ = p := by ext i k; simp [remainingCenters]
      rw [hempty]
      exact ⟨BoxMotion.stationary (A := ⟨p, w⟩) hwidth
        (separated_of_centerSeparated (fun i j hij => ⟨0, hp i j hij⟩) hsize) hgp⟩
  have hh := h Finset.univ
  have he : remainingCenters a p Finset.univ = a := by ext i k; simp [remainingCenters]
  rw [he] at hh
  exact Classical.choice hh

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

def expandCenters {a w : ι → Space} {safe : Set ι} {η Λ : ℝ}
    (hp : ∀ i k, 0 < w i k) (hs : (BoxLayout.mk a w).Separated η)
    (hg : (BoxLayout.mk a w).Guarded safe) (hΛ : 1 ≤ Λ) :
    BoxMotion ⟨a, w⟩ ⟨fun i k => Λ * a i k, w⟩ safe η :=
  segmentMotion hp (by
    intro r hr i j hij
    obtain ⟨k, hk⟩ := hs i j hij
    refine ⟨k, hk.trans_le ?_⟩
    have hh : 1 ≤ 1 - r + r * Λ := by nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hΛ)]
    have he : (1 - r) * a i k + r * (Λ * a i k) -
        ((1 - r) * a j k + r * (Λ * a j k)) = (1 - r + r * Λ) * (a i k - a j k) := by ring
    change |a i k - a j k| ≤ |(1 - r) * a i k + r * (Λ * a i k) -
        ((1 - r) * a j k + r * (Λ * a j k))|
    rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - r + r * Λ)]
    nlinarith [abs_nonneg (a i k - a j k)]) (by
    intro r hr
    apply segment_guard hg _ hr
    intro i hi
    have hh := hg i hi
    have hpos : 0 < a i 0 := by linarith [hp i 0]
    change 2 < Λ * a i 0 - w i 0
    nlinarith [mul_nonneg (sub_nonneg.mpr hΛ) hpos.le])

def geometricWidth (h k : ι → Space) (r : ℝ) (i : ι) (j : Fin 3) : ℝ :=
  Real.exp ((1 - r) * Real.log (h i j) + r * Real.log (k i j))

omit [Fintype ι] in
lemma geometricWidth_zero {h k : ι → Space} (hp : ∀ i j, 0 < h i j) :
    geometricWidth h k 0 = h := by
  ext i j
  simp [geometricWidth, Real.exp_log (hp i j)]

omit [Fintype ι] in
lemma geometricWidth_one {h k : ι → Space} (hp : ∀ i j, 0 < k i j) :
    geometricWidth h k 1 = k := by
  ext i j
  simp [geometricWidth, Real.exp_log (hp i j)]

omit [Fintype ι] in
lemma geometricWidth_pos (h k : ι → Space) (r : ℝ) (i : ι) (j : Fin 3) :
    0 < geometricWidth h k r i j := Real.exp_pos _

omit [Fintype ι] in
lemma geometricWidth_le {h k : ι → Space} {R r : ℝ}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hhR : ∀ i j, h i j ≤ R) (hkR : ∀ i j, k i j ≤ R)
    (hr : r ∈ Icc (0 : ℝ) 1) (i : ι) (j : Fin 3) :
    geometricWidth h k r i j ≤ R := by
  have hR : 0 < R := (hh i j).trans_le (hhR i j)
  have h₀ := Real.log_le_log (hh i j) (hhR i j)
  have h₁ := Real.log_le_log (hk i j) (hkR i j)
  rw [geometricWidth, ← Real.exp_log hR]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr hr.2),
    mul_nonneg (sub_nonneg.mpr h₁) hr.1]

omit [Fintype ι] in
lemma geometricWidth_prod {h k : ι → Space}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (he : ∀ i, ∏ j, h i j = ∏ j, k i j) (r : ℝ) (i : ι) :
    ∏ j, geometricWidth h k r i j = ∏ j, h i j := by
  have hl : ∑ j, Real.log (h i j) = ∑ j, Real.log (k i j) := by
    rw [← Real.log_prod (fun j _ => (hh i j).ne'),
      ← Real.log_prod (fun j _ => (hk i j).ne'), he]
  simp only [geometricWidth]
  rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hl]
  have hh' : (1 - r) * ∑ j, Real.log (h i j) + r * ∑ j, Real.log (h i j) =
      ∑ j, Real.log (h i j) := by ring
  rw [hh', ← Real.log_prod (fun j _ => (hh i j).ne'),
    Real.exp_log (Finset.prod_pos (fun j _ => hh i j))]

def reshapeMotion {a h k : ι → Space} {safe : Set ι} {η R D : ℝ}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hR : ∀ i j, h i j ≤ R) (kR : ∀ i j, k i j ≤ R)
    (he : ∀ i, ∏ j, h i j = ∏ j, k i j)
    (hD : 2 * R + 4 * η ≤ D) (hs : CenterSeparated a D)
    (hg : ∀ i ∈ safe, 2 + R < a i 0) :
    BoxMotion ⟨a, h⟩ ⟨a, k⟩ safe η where
  center := fun _ => a
  width := fun t => geometricWidth h k (Real.smoothTransition t)
  smooth_center := contDiff_const
  smooth_width := by unfold geometricWidth; fun_prop
  start_center := by intros; rfl
  start_width := by
    intro t ht
    rw [Real.smoothTransition.zero_of_nonpos ht, geometricWidth_zero hh]
  end_center := by intros; rfl
  end_width := by
    intro t ht
    rw [Real.smoothTransition.one_of_one_le ht, geometricWidth_one hk]
  positive := fun _ => geometricWidth_pos _ _ _
  volume := fun _ => geometricWidth_prod hh hk he _
  separation := by
    classical
    intro t
    apply separated_of_centerSeparated hs
    intro i j l
    have hi := geometricWidth_le hh hk hR kR
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩ i l
    have hj := geometricWidth_le hh hk hR kR
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩ j l
    linarith
  guard := by
    intro t i hi
    have hw := geometricWidth_le hh hk hR kR
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩ i 0
    have hhg := hg i hi
    change 2 < a i 0 - geometricWidth h k (Real.smoothTransition t) i 0
    linarith

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

def RationalConstant (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma rat (q : ℚ) : RationalConstant (q : ℝ) := ⟨q,rfl⟩

lemma nat (n : ℕ) : RationalConstant (n : ℝ) := ⟨n, by simp⟩

lemma zero : RationalConstant 0 := by simpa using rat 0

lemma one : RationalConstant 1 := by simpa using rat 1

lemma add {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b, by simp⟩

lemma sub {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a-b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a-b, by simp⟩

lemma mul {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a*b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a*b, by simp⟩

lemma elementary {d : ℕ} [NeZero d] {a : ℝ} (ha : RationalConstant a) :
    Elementary (fun _ : Fin d → ℝ => a) := by
  obtain ⟨a,rfl⟩ := ha; exact Elementary.literal a

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

def RationalCenters {ι : Type*} (a : ι → Space) : Prop := ∀ i k, RationalConstant (a i k)

def RationalLayout {ι : Type*} (A : BoxLayout ι) : Prop := RationalCenters A.center ∧ RationalCenters A.width

def ElementaryCurve (f : ℝ → ℝ) : Prop := Elementary (fun x : Fin 1 → ℝ => f (x 0))

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry Set

lemma const {c : ℝ} (hc : RationalConstant c) : ElementaryCurve (fun _ => c) := hc.elementary

lemma id : ElementaryCurve (fun t => t) := Elementary.coordinate 0

lemma add {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t + g t) := Elementary.add hf hg

lemma sub {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t - g t) := Elementary.sub hf hg

lemma mul {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t * g t) := Elementary.mul hf hg

lemma div_const {f : ℝ → ℝ} (hf : ElementaryCurve f) {c : ℝ} (hc : RationalConstant c) :
    ElementaryCurve (fun t => f t / c) := by
  obtain ⟨c,rfl⟩ := hc; exact hf.div_rat c

lemma exp {f : ℝ → ℝ} (hf : ElementaryCurve f) : ElementaryCurve (fun t => Real.exp (f t)) := Elementary.exp hf

lemma comp {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f (g t)) := Elementary.comp hf (fun x _ => g (x 0)) (fun _ => hg)

lemma transition : ElementaryCurve Real.smoothTransition := id.smoothTransition

lemma log {c : ℝ} (hc : RationalConstant c) (hp : 0 < c) : ElementaryCurve (fun _ => Real.log c) := by
  obtain ⟨c,rfl⟩ := hc
  exact Elementary.log_rat (by exact_mod_cast hp)

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

def ElementaryMotion {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}
    (m : BoxMotion A B safe η) : Prop :=
  (∀ i k, ElementaryCurve (fun t => m.center t i k)) ∧
  (∀ i k, ElementaryCurve (fun t => m.width t i k))

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryMotion
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma stationary (hA : RationalLayout A) (hp : A.Positive) (hs : A.Separated η)
    (hg : A.Guarded safe) : ElementaryMotion (BoxMotion.stationary hp hs hg) :=
  ⟨fun i k => ElementaryCurve.const (hA.1 i k), fun i k => ElementaryCurve.const (hA.2 i k)⟩

lemma trans {m : BoxMotion A B safe η} {n : BoxMotion B C safe η}
    (hm : ElementaryMotion m) (hn : ElementaryMotion n) (hB : RationalLayout B) :
    ElementaryMotion (m.trans n) := by
  have h₂ : ElementaryCurve (fun t => 2*t) :=
    (ElementaryCurve.const (RationalConstant.nat 2)).mul ElementaryCurve.id
  have h₂' : ElementaryCurve (fun t => 2*t-1) := h₂.sub (ElementaryCurve.const RationalConstant.one)
  constructor <;> intro i k
  · exact ((hm.1 i k).comp h₂).add ((hn.1 i k).comp h₂') |>.sub (ElementaryCurve.const (hB.1 i k))
  · exact (((hm.2 i k).comp h₂).mul ((hn.2 i k).comp h₂')).div_const (hB.2 i k)

lemma reverse {m : BoxMotion A B safe η} (hm : ElementaryMotion m) : ElementaryMotion m.reverse := by
  have h : ElementaryCurve (fun t => 1-t) :=
    (ElementaryCurve.const RationalConstant.one).sub ElementaryCurve.id
  exact ⟨fun i k => (hm.1 i k).comp h, fun i k => (hm.2 i k).comp h⟩

lemma segment {a b w : ι → Space} (ha : RationalCenters a) (hb : RationalCenters b)
    (hw : RationalCenters w) (hp : ∀ i k, 0 < w i k)
    (hs : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Separated η)
    (hg : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Guarded safe) :
    ElementaryMotion (segmentMotion hp hs hg) := by
  refine ⟨?_, fun i k => ElementaryCurve.const (hw i k)⟩
  intro i k
  exact (((ElementaryCurve.const RationalConstant.one).sub ElementaryCurve.transition).mul
    (ElementaryCurve.const (ha i k))).add
    (ElementaryCurve.transition.mul (ElementaryCurve.const (hb i k)))

lemma expansion {a w : ι → Space} {Λ : ℝ} (ha : RationalCenters a)
    (hw : RationalCenters w) (hΛr : RationalConstant Λ)
    (hp : ∀ i k, 0 < w i k) (hs : (BoxLayout.mk a w).Separated η)
    (hg : (BoxLayout.mk a w).Guarded safe) (hΛ : 1 ≤ Λ) :
    ElementaryMotion (expandCenters hp hs hg hΛ) :=
  segment ha (fun i k => hΛr.mul (ha i k)) hw _ _ _

lemma reshape {a h k : ι → Space} {R D : ℝ}
    (ha : RationalCenters a) (hr : RationalCenters h) (kr : RationalCenters k)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hR : ∀ i j, h i j ≤ R) (kR : ∀ i j, k i j ≤ R)
    (he : ∀ i, ∏ j, h i j = ∏ j, k i j)
    (hD : 2 * R + 4 * η ≤ D) (hs : CenterSeparated a D)
    (hg : ∀ i ∈ safe, 2 + R < a i 0) :
    ElementaryMotion (reshapeMotion hh hk hR kR he hD hs hg) := by
  refine ⟨fun i j => ElementaryCurve.const (ha i j), ?_⟩
  intro i j
  exact ((((ElementaryCurve.const RationalConstant.one).sub ElementaryCurve.transition).mul
    (ElementaryCurve.log (hr i j) (hh i j))).add
    (ElementaryCurve.transition.mul (ElementaryCurve.log (kr i j) (hk i j)))).exp

end BalancedTransport.Effectivity.ElementaryMotion
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma RationalCenters.update [DecidableEq ι] {a : ι → Space} (ha : RationalCenters a)
    (i : ι) {b : Space} (hb : ∀ k, RationalConstant (b k)) : RationalCenters (Function.update a i b) := by
  intro j k
  by_cases h : j = i
  · subst j; simpa using hb k
  · simpa [Function.update_of_ne h] using ha j k

lemma rational_space_update {a : Space} (ha : ∀ k, RationalConstant (a k))
    (j : Fin 3) {b : ℝ} (hb : RationalConstant b) : ∀ k, RationalConstant ((Function.update a j b) k) := by
  intro k
  by_cases he : k = j
  · subst k; simpa using hb
  · simpa [Function.update_of_ne he] using ha k

omit [Fintype ι] in
lemma rational_remaining [DecidableEq ι] {a p : ι → Space} (ha : RationalCenters a)
    (hp : RationalCenters p) (S : Finset ι) : RationalCenters (remainingCenters a p S) := by
  intro i k
  by_cases hi : i ∈ S
  · simpa [remainingCenters, hi] using ha i k
  · simpa [remainingCenters, hi] using hp i k

lemma elementary_singleSegment [DecidableEq ι] {a w : ι → Space} {D η : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (wr : RationalCenters w)
    (i : ι) (b : Space) (br : ∀ k, RationalConstant (b k))
    (hp : ∀ j k, 0 < w j k) (hw : ∀ j l k, w j k + w l k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hb : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i → ∃ k, D < |(1-r)*a i k+r*b k-a j k|)
    (hga : (BoxLayout.mk a w).Guarded safe)
    (hgb : (BoxLayout.mk (Function.update a i b) w).Guarded safe) :
    ElementaryMotion (singleSegmentMotion i b hp hw ha hb hga hgb) :=
  ElementaryMotion.segment ar (ar.update i br) wr _ _ _

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
open BalancedTransport.Geometry

lemma congr {d : ℕ} [NeZero d] {f g : (Fin d → ℝ) → ℝ} (hf : Elementary f) (he : ∀x, f x = g x) : Elementary g := by
  rwa [← funext he]

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry

lemma deriv {f : ℝ → ℝ} (hf : ElementaryCurve f) : ElementaryCurve (_root_.deriv f) := by
  have hd := (Elementary.coordinateDerivative hf 0)
  have h (x : Fin 1 → ℝ) :
      fderiv ℝ (fun z : Fin 1 → ℝ => f (z 0)) x (Pi.single 0 1) = _root_.deriv f (x 0) := by
    have he : (fun t : ℝ => f ((fun _ : Fin 1 => t) 0)) = f := rfl
    have hg : HasDerivAt (fun t : ℝ => fun _ : Fin 1 => t) (Pi.single 0 1) (x 0) := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      change HasDerivAt (fun s : ℝ => s) (1 : ℝ) (x 0)
      exact hasDerivAt_id _
    have hfx : (fun _ : Fin 1 => x 0) = x := by ext i; fin_cases i; rfl
    have hh := ((Elementary.differentiable hf) (fun _ => x 0)).hasFDerivAt
    simpa only [hfx, Function.comp_def] using (hh.comp_hasDerivAt (x 0) hg).deriv.symm
  change Elementary (fun x : Fin 1 → ℝ => _root_.deriv f (x 0))
  exact hd.congr h

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

def fieldArgs {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) : Fin (4+d) → ℝ :=
  Fin.append (Fin.cons t x) p

def fieldParam {d : ℕ} (z : Fin (4+d) → ℝ) : Fin d → ℝ := fun k => z (Fin.natAdd 4 k)

def fieldTime {d : ℕ} (z : Fin (4+d) → ℝ) : ℝ := z (Fin.castAdd d 0)

def fieldSpace {d : ℕ} (z : Fin (4+d) → ℝ) : Space := fun k => z (Fin.castAdd d k.succ)

@[simp] lemma fieldParam_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldParam (fieldArgs p t x) = p := by ext k; simp [fieldParam,fieldArgs]

@[simp] lemma fieldTime_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldTime (fieldArgs p t x) = t := by simp [fieldTime,fieldArgs]

@[simp] lemma fieldSpace_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldSpace (fieldArgs p t x) = x := by ext k; simp [fieldSpace,fieldArgs]

@[simp] lemma fieldArgs_parts {d : ℕ} (z : Fin (4+d) → ℝ) :
    fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z) = z := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [fieldArgs,fieldTime]
    · simp [fieldArgs,fieldTime,fieldSpace]
  · intro j
    simp [fieldArgs,fieldParam,fieldTime]

def ElementaryScalar {d : ℕ} (f : (Fin d → ℝ) → Field ℝ) : Prop :=
  Elementary (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z))

def ElementaryField {d : ℕ} (f : (Fin d → ℝ) → Velocity) : Prop :=
  ∀ i, ElementaryScalar (fun p t x => f p t x i)

lemma fieldArgs_time_hasDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasDerivAt (fun s => fieldArgs p s x) (Pi.single (Fin.castAdd d 0) 1) t := by
  apply hasDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [fieldArgs, Fin.append_left, Fin.cons_zero, Pi.single_eq_same]
      exact hasDerivAt_id _
    · have hn : Fin.castAdd d i.succ ≠ Fin.castAdd d (0 : Fin 4) := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
      simpa only [fieldArgs, Fin.append_left, Fin.cons_succ, Pi.single_apply, ite_eq_right hn] using hasDerivAt_const t (x i)
  · intro j
    have hn : Fin.natAdd 4 j ≠ Fin.castAdd d (0 : Fin 4) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at this; omega
    simpa only [fieldArgs, Fin.append_right, Pi.single_apply, ite_eq_right hn] using hasDerivAt_const t (p j)

lemma fieldArgs_space_hasFDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasFDerivAt (fun y => fieldArgs p t y)
      (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k)) x := by
  apply hasFDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [fieldArgs] using hasFDerivAt_const t x
    · simpa [fieldArgs] using hasFDerivAt_apply i x
  · intro j
    simpa [fieldArgs] using hasFDerivAt_const (p j) x

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma fullTimeD (h : ElementaryScalar f) : ElementaryScalar (fun p => Geometry.fullTimeD (f p)) := by
  have hd := h.coordinateDerivative (Fin.castAdd d 0)
  apply hd.congr
  intro z
  have hh := (h.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp_hasDerivAt (fieldTime z) (fieldArgs_time_hasDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,Geometry.fullTimeD] using he.deriv.symm

lemma spaceD (h : ElementaryScalar f) (i : Fin 3) : ElementaryScalar (fun p => BalancedTransport.spaceD i (f p)) := by
  have hd := h.coordinateDerivative (Fin.castAdd d i.succ)
  apply hd.congr
  intro z
  have hh := (h.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp (fieldSpace z) (fieldArgs_space_hasFDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  have hl : (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k) : Space →L[ℝ] (Fin (4+d) → ℝ)) (Pi.single i 1) = Pi.single (Fin.castAdd d i.succ) 1 := by
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro j
      refine Fin.cases ?_ (fun l => ?_) j
      · have hn : Fin.castAdd d (0 : Fin 4) ≠ Fin.castAdd d i.succ := by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
        simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_zero,
          zero_apply, Pi.single_apply, ite_eq_right hn]
      · simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_succ,
          ContinuousLinearMap.proj_apply, Pi.single_apply, Fin.castAdd_inj, Fin.succ_inj]
    · intro j
      have hn : Fin.natAdd 4 j ≠ Fin.castAdd d i.succ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ] at this; omega
      simp only [ContinuousLinearMap.pi_apply, Fin.addCases_right,
        zero_apply, Pi.single_apply, ite_eq_right hn]
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args, BalancedTransport.spaceD,
    ContinuousLinearMap.comp_apply, hl] using congrArg (fun l => l (Pi.single i 1)) he.fderiv.symm

end BalancedTransport.Effectivity.ElementaryScalar
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma literal (q : ℚ) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ _ => (q : ℝ)) := Elementary.literal q

lemma rational {q : ℝ} (hq : RationalConstant q) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ _ => q) := hq.elementary

lemma add (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x + g p t x) := Elementary.add hf hg

lemma mul (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x * g p t x) := Elementary.mul hf hg

lemma sub (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x - g p t x) := Elementary.sub hf hg

lemma neg (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => -f p t x) := Elementary.neg hf

lemma div_rat (q : ℚ) (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => f p t x / (q : ℝ)) := Elementary.div_rat q hf

lemma div_const {q : ℝ} (hq : RationalConstant q) (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => f p t x / q) := by
  obtain ⟨q,rfl⟩ := hq; exact hf.div_rat q

lemma inv (hf : ElementaryScalar f) (n : ℕ) (hn : ∀ p t x, ((n+1:ℕ):ℝ)⁻¹ ≤ f p t x) :
    ElementaryScalar (fun p t x => (f p t x)⁻¹) := Elementary.inv hf n (fun _ => hn _ _ _)

lemma exp (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => Real.exp (f p t x)) := Elementary.exp hf

lemma transition (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => Real.smoothTransition (f p t x)) := Elementary.smoothTransition hf

lemma time : ElementaryScalar (fun _ : Fin d → ℝ => fun t _ => t) := Elementary.coordinate (Fin.castAdd d 0)

lemma space (i : Fin 3) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ x => x i) := Elementary.coordinate (Fin.castAdd d i.succ)

lemma parameter (i : Fin d) : ElementaryScalar (fun p : Fin d → ℝ => fun _ _ => p i) := Elementary.coordinate (Fin.natAdd 4 i)

lemma curve {h : ℝ → ℝ} (hh : ElementaryCurve h) (hf : ElementaryScalar f) :
    ElementaryScalar (fun p t x => h (f p t x)) :=
  Elementary.comp hh (fun z _ => f (fieldParam z) (fieldTime z) (fieldSpace z)) (fun _ => hf)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Field ℝ)
    (hf : ∀ i ∈ s, ElementaryScalar (f i)) : ElementaryScalar (fun p t x => ∑ i ∈ s, f i p t x) :=
  Elementary.sum s _ hf

lemma prod {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Field ℝ)
    (hf : ∀ i ∈ s, ElementaryScalar (f i)) : ElementaryScalar (fun p t x => ∏ i ∈ s, f i p t x) :=
  Elementary.prod s _ hf

lemma congr (hf : ElementaryScalar f) (he : ∀p t x, f p t x = g p t x) : ElementaryScalar g :=
  Elementary.congr hf (fun _ => he _ _ _)

lemma time_differentiable (hf : ElementaryScalar f) (p : Fin d → ℝ) (x : Space) :
    Differentiable ℝ (fun t => f p t x) := by
  intro t
  have hh := (hf.differentiable (fieldArgs p t x)).comp t
    (fieldArgs_time_hasDerivAt p t x).differentiableAt
  simpa only [Function.comp_def,fieldParam_args,fieldTime_args,fieldSpace_args] using hh

lemma space_differentiable (hf : ElementaryScalar f) (p : Fin d → ℝ) (t : ℝ) :
    Differentiable ℝ (f p t) := by
  intro x
  have hh := (hf.differentiable (fieldArgs p t x)).comp x
    (fieldArgs_space_hasFDerivAt p t x).differentiableAt
  simpa only [Function.comp_def,fieldParam_args,fieldTime_args,fieldSpace_args] using hh

end BalancedTransport.Effectivity.ElementaryScalar
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryField
open BalancedTransport.Geometry
variable {d : ℕ} {v w : (Fin d → ℝ) → Velocity}

lemma fullTimeD (hv : ElementaryField v) : ElementaryField (fun p => Geometry.fullTimeD (v p)) := by
  intro i
  apply (ElementaryScalar.fullTimeD (hv i)).congr
  intro p t x
  simp only [Geometry.fullTimeD, deriv_pi (fun k => (hv k).time_differentiable p x t)]

lemma spaceD (hv : ElementaryField v) (i : Fin 3) : ElementaryField (fun p => BalancedTransport.spaceD i (v p)) := by
  intro k
  apply (ElementaryScalar.spaceD (hv k) i).congr
  intro p t x
  simp only [BalancedTransport.spaceD, fderiv_pi (fun j => (hv j).space_differentiable p t x),
    ContinuousLinearMap.pi_apply]

lemma curl (hv : ElementaryField v) : ElementaryField (fun p t => Geometry.curl (v p t)) := by
  intro k
  fin_cases k
  · exact ((hv 2).spaceD 1).sub ((hv 1).spaceD 2)
  · exact ((hv 0).spaceD 2).sub ((hv 2).spaceD 0)
  · exact ((hv 1).spaceD 0).sub ((hv 0).spaceD 1)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Velocity)
    (hf : ∀ i ∈ s, ElementaryField (f i)) : ElementaryField (fun p t x => ∑ i ∈ s, f i p t x) := by
  intro k
  simpa only [Finset.sum_apply] using ElementaryScalar.sum s (fun i p t x => f i p t x k) (fun i hi => hf i hi k)

lemma fullMixedD (hv : ElementaryField v) (a : MultiIndex) :
    ElementaryField (fun p => Geometry.fullMixedD a (v p)) := by
  induction a with
  | nil => exact hv
  | cons i a ih => cases i with
    | none => exact ih.fullTimeD
    | some i => exact ih.spaceD i

end BalancedTransport.Effectivity.ElementaryField
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma elementary_boxCutoff {d : ℕ} {a b : (Fin d → ℝ) → Velocity}
    (ha : ElementaryField a) (hb : ElementaryField b) {η : ℝ} (hη : RationalConstant η) :
    ElementaryScalar (fun p t x => boxCutoff (a p t x) (b p t x) η x) := by
  apply ElementaryScalar.prod Finset.univ
  intro i _
  exact ((((ElementaryScalar.space i).sub (ha i)).add
    ((ElementaryScalar.literal 2).mul (ElementaryScalar.rational hη))).div_const hη).transition.mul
    ((((hb i).add ((ElementaryScalar.literal 2).mul (ElementaryScalar.rational hη))).sub
      (ElementaryScalar.space i)).div_const hη).transition

lemma elementary_affinePotential {d : ℕ} {c v l : (Fin d → ℝ) → Velocity}
    (hc : ElementaryField c) (hv : ElementaryField v) (hl : ElementaryField l) :
    ElementaryField (fun p t x => affinePotential (c p t x) (v p t x) (l p t x) x) := by
  have hh (i j : Fin 3) := ((ElementaryScalar.literal (1/2)).mul
      (((hv i).mul ((ElementaryScalar.space j).sub (hc j))).sub
        ((hv j).mul ((ElementaryScalar.space i).sub (hc i))))).add
    (((ElementaryScalar.literal (1/3)).mul ((hl i).sub (hl j))).mul
      ((ElementaryScalar.space i).sub (hc i)) |>.mul ((ElementaryScalar.space j).sub (hc j)))
  intro k
  fin_cases k
  · simpa [affinePotential] using hh 1 2
  · simpa [affinePotential] using hh 2 0
  · simpa [affinePotential] using hh 0 1

lemma elementary_movingBoxVelocity {d : ℕ} (a b : Space) (ar : ∀i, RationalConstant (a i))
    (br : ∀i, RationalConstant (b i)) {c w : (Fin d → ℝ) → ℝ → Space}
    (hc : ElementaryField (fun p t _ => c p t)) (hw : ElementaryField (fun p t _ => w p t))
    (hn : ∀ i, ∃ n : ℕ, ∀ p t, ((n+1:ℕ):ℝ)⁻¹ ≤ w p t i)
    {η : ℝ} (ηr : RationalConstant η) : ElementaryField (fun p => movingBoxVelocity a b (c p) (w p) η) := by
  have ha : ElementaryField (fun p t _ => lowerEndpoint a (c p) (w p) t) :=
    fun i => (hc i).add ((hw i).mul (ElementaryScalar.rational (ar i)))
  have hb : ElementaryField (fun p t _ => lowerEndpoint b (c p) (w p) t) :=
    fun i => (hc i).add ((hw i).mul (ElementaryScalar.rational (br i)))
  have hl : ElementaryField (fun p t _ => logarithmicRate (w p) t) := by
    intro i
    obtain ⟨n,hn⟩ := hn i
    simpa only [logarithmicRate, fullTimeD, div_eq_mul_inv] using
      (ElementaryScalar.fullTimeD (hw i)).mul ((hw i).inv n (fun p t _ => hn p t))
  have hP := elementary_affinePotential hc hc.fullTimeD hl
  have hχ := elementary_boxCutoff ha hb ηr
  exact ElementaryField.curl (fun i => hχ.mul (hP i))

lemma elementary_loadingVelocity {η : ℝ} (hr : RationalConstant η) :
    ElementaryField (fun p : Fin 3 → ℝ => loadingVelocity p η) := by
  have labelRat : ∀ i, RationalConstant (fixedLabel i) := by
    intro i
    fin_cases i
    · exact RationalConstant.nat 4
    · exact RationalConstant.zero
    · exact RationalConstant.zero
  apply elementary_movingBoxVelocity fixedLabel fixedLabel labelRat labelRat
  · intro i
    simpa only [loadingCenter, loadingSwitch, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      ((((ElementaryScalar.literal 2).mul ElementaryScalar.time).sub
        (ElementaryScalar.literal (1/2))).transition.mul
        ((ElementaryScalar.parameter i).sub (ElementaryScalar.rational (labelRat i))))
  · intro i
    simpa using (ElementaryScalar.literal (d:=3) 1)
  · intro i
    exact ⟨0, by intro p t; norm_num⟩
  · exact hr

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

lemma finite_upper_bound {α : Type*} [Finite α] (f : α → ℝ) :
    ∃ R : ℝ, ∀ i, f i < R := by
  obtain ⟨R, hR⟩ := (Set.finite_range f).bddAbove
  exact ⟨R + 1, fun i => (hR (mem_range_self i)).trans_lt (lt_add_one _)⟩

lemma finite_positive_lower_bound {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ f i := by
  classical
  have hh : ∀ s : Finset α, ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨r, hr, h⟩ := ih
      refine ⟨min r (f a), lt_min hr (hf a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h i hi)
  simpa using hh Finset.univ

omit [Fintype ι] in
lemma BoxLayout.Separated.mono {A : BoxLayout ι} {η δ : ℝ}
    (h : A.Separated δ) (hle : η ≤ δ) : A.Separated η := by
  intro i j hij
  obtain ⟨k, hk⟩ := h i j hij
  exact ⟨k, by linarith⟩

lemma BoxLayout.Separated.positive_margin {A : BoxLayout ι}
    (h : A.Separated 0) : ∃ η : ℝ, 0 < η ∧ A.Separated η := by
  classical
  let J := {p : ι × ι // p.1 ≠ p.2}
  have hs (p : J) : ∃ k, 0 < |A.center p.1.1 k - A.center p.1.2 k| -
      (A.width p.1.1 k + A.width p.1.2 k) := by
    obtain ⟨k, hk⟩ := h _ _ p.2
    exact ⟨k, by linarith⟩
  choose κ hκ using hs
  obtain ⟨δ, hδ, hm⟩ := finite_positive_lower_bound
    (fun p : J => |A.center p.1.1 (κ p) - A.center p.1.2 (κ p)| -
      (A.width p.1.1 (κ p) + A.width p.1.2 (κ p))) hκ
  refine ⟨δ / 8, by positivity, ?_⟩
  intro i j hij
  let p : J := ⟨(i, j), hij⟩
  refine ⟨κ p, ?_⟩
  have hh := hm p
  dsimp [p] at hh ⊢
  linarith

omit [Fintype ι] in
lemma BoxLayout.center_injective {A : BoxLayout ι}
    (hp : A.Positive) (hs : A.Separated 0) : Function.Injective A.center := by
  intro i j hij
  by_contra hne
  obtain ⟨k, hk⟩ := hs i j hne
  rw [hij, sub_self, abs_zero] at hk
  linarith [hp i k, hp j k]

omit [Fintype ι] in
lemma centerSeparated_of_norm {a : ι → Space} {D : ℝ}
    (hD : 0 ≤ D) (ha : ∀ i j, i ≠ j → D < ‖a i - a j‖) : CenterSeparated a D := by
  intro i j hij
  by_contra! h
  have hh : ‖a i - a j‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr (by
    intro k
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h k)
  exact (ha i j hij).not_ge hh

lemma exists_expansion {a b : ι → Space} (ha : Function.Injective a)
    (hb : Function.Injective b) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ R + 2 ≤ Λ ∧
      CenterSeparated (fun i k => Λ * a i k) D ∧
      CenterSeparated (fun i k => Λ * b i k) D := by
  obtain ⟨La, hLa⟩ := finite_upper_bound (fun p : ι × ι => D / ‖a p.1 - a p.2‖)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound (fun p : ι × ι => D / ‖b p.1 - b p.2‖)
  let Λ := max 1 (max (R + 2) (max La Lb))
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛR : R + 2 ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hΛa : La ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hΛb : Lb ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hh (c : ι → Space) (hc : Function.Injective c)
      (hLc : ∀ i j, D / ‖c i - c j‖ < Λ) :
      CenterSeparated (fun i k => Λ * c i k) D := by
    apply centerSeparated_of_norm hD
    intro i j hij
    have hpos : 0 < ‖c i - c j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hc.ne hij))
    have he : (fun k => Λ * c i k) - (fun k => Λ * c j k) = Λ • (c i - c j) := by
      ext k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Λ)]
    exact (div_lt_iff₀ hpos).mp (hLc i j)
  exact ⟨Λ, hΛ, hΛR, hh a ha (fun i j => (hLa (i,j)).trans_le hΛa),
    hh b hb (fun i j => (hLb (i,j)).trans_le hΛb)⟩

lemma exists_parking (a b : ι → Space) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ p : ι → Space,
      (∀ i j, D < |a i 0 - p j 0|) ∧
      (∀ i j, D < |b i 0 - p j 0|) ∧
      (∀ i j, i ≠ j → D < |p i 0 - p j 0|) ∧
      (∀ i, 2 + R < p i 0) := by
  classical
  obtain ⟨La, hLa⟩ := finite_upper_bound (fun i => a i 0)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound (fun i => b i 0)
  let K := max (3 + R) (max La Lb) + D + 1
  let e := Fintype.equivFin ι
  let p : ι → Space := fun i => ![K + (D + 1) * (e i).val, 0, 0]
  have hKs : 2 + R < K := by dsimp [K]; have := le_max_left (3 + R) (max La Lb); linarith
  have hKa : ∀ i, D < K - a i 0 := by
    intro i
    have := (le_max_left La Lb).trans (le_max_right (3 + R) (max La Lb))
    have := hLa i
    dsimp [K]
    linarith
  have hKb : ∀ i, D < K - b i 0 := by
    intro i
    have := (le_max_right La Lb).trans (le_max_right (3 + R) (max La Lb))
    have := hLb i
    dsimp [K]
    linarith
  have hpn : ∀ i, K ≤ p i 0 := by
    intro i
    dsimp [p]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  refine ⟨p, ?_, ?_, ?_, fun i => hKs.trans_le (hpn i)⟩
  · intro i j
    have := hKa i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - a i 0) (le_abs_self _)
  · intro i j
    have := hKb i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - b i 0) (le_abs_self _)
  · intro i j hij
    have hv : (e i).val ≠ (e j).val := by intro h; exact hij (e.injective (Fin.ext h))
    have hh : (1 : ℝ) ≤ |(e i).val - ((e j).val : ℝ)| := by
      rcases lt_or_gt_of_ne hv with hl | hl
      · have hcast : ((e i).val : ℝ) + 1 ≤ (e j).val := by exact_mod_cast hl
        rw [abs_of_nonpos (by linarith : ((e i).val : ℝ) - (e j).val ≤ 0)]
        linarith
      · have hcast : ((e j).val : ℝ) + 1 ≤ (e i).val := by exact_mod_cast hl
        rw [abs_of_nonneg (by linarith : 0 ≤ ((e i).val : ℝ) - (e j).val)]
        linarith
    have he : p i 0 - p j 0 = (D + 1) * (((e i).val : ℝ) - (e j).val) := by dsimp [p]; ring
    rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ D + 1)]
    nlinarith

theorem guarded_solid_box_motion (A B : BoxLayout ι) (safe : Set ι)
    (hA : A.Positive) (hB : B.Positive)
    (hsA : A.Separated 0) (hsB : B.Separated 0)
    (hvol : ∀ i, ∏ k, A.width i k = ∏ k, B.width i k)
    (hgA : A.Guarded safe) (hgB : B.Guarded safe) :
    ∃ η : ℝ, 0 < η ∧ Nonempty (BoxMotion A B safe η) := by
  classical
  obtain ⟨ηA, hηA, hmA⟩ := hsA.positive_margin
  obtain ⟨ηB, hηB, hmB⟩ := hsB.positive_margin
  let η := min ηA ηB
  have hη : 0 < η := lt_min hηA hηB
  have hmA' := hmA.mono (min_le_left ηA ηB)
  have hmB' := hmB.mono (min_le_right ηA ηB)
  obtain ⟨RA, hRA⟩ := finite_upper_bound (fun p : ι × Fin 3 => A.width p.1 p.2)
  obtain ⟨RB, hRB⟩ := finite_upper_bound (fun p : ι × Fin 3 => B.width p.1 p.2)
  let R := max 1 (max RA RB)
  have hR : 1 ≤ R := le_max_left _ _
  have hAR : ∀ i k, A.width i k ≤ R := fun i k => (hRA (i,k)).le.trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hBR : ∀ i k, B.width i k ≤ R := fun i k => (hRB (i,k)).le.trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let D := 2 * R + 4 * η
  have hD : 0 ≤ D := by dsimp [D]; linarith
  obtain ⟨Λ, hΛ, hΛR, hΛA, hΛB⟩ := exists_expansion
    (BoxLayout.center_injective hA hsA) (BoxLayout.center_injective hB hsB) (R := R) hD
  let a : ι → Space := fun i k => Λ * A.center i k
  let b : ι → Space := fun i k => Λ * B.center i k
  obtain ⟨p, hpa, hpb, hpp, hpg⟩ := exists_parking a b (R := R) hD
  have hag : ∀ i ∈ safe, 2 + R < a i 0 := by
    intro i hi
    have hh : 2 < A.center i 0 := by have := hgA i hi; linarith [hA i 0]
    have hΛp : 0 < Λ := by linarith
    have hh' := mul_lt_mul_of_pos_left hh hΛp
    dsimp [a]
    nlinarith
  have hbg : ∀ i ∈ safe, 2 + R < b i 0 := by
    intro i hi
    have hh : 2 < B.center i 0 := by have := hgB i hi; linarith [hB i 0]
    have hΛp : 0 < Λ := by linarith
    have hh' := mul_lt_mul_of_pos_left hh hΛp
    dsimp [b]
    nlinarith
  have hga : (BoxLayout.mk a B.width).Guarded safe := by
    intro i hi
    change 2 < a i 0 - B.width i 0
    linarith [hag i hi, hBR i 0]
  have hgb : (BoxLayout.mk b B.width).Guarded safe := by
    intro i hi
    change 2 < b i 0 - B.width i 0
    linarith [hbg i hi, hBR i 0]
  have hgp : (BoxLayout.mk p B.width).Guarded safe := by
    intro i _
    change 2 < p i 0 - B.width i 0
    linarith [hpg i, hBR i 0]
  have hsize : ∀ i j k, B.width i k + B.width j k + 4 * η ≤ D := by
    intro i j k
    dsimp [D]
    linarith [hBR i k, hBR j k]
  obtain ⟨HA, hHA⟩ := finite_upper_bound (fun i => a i 1)
  obtain ⟨HB, hHB⟩ := finite_upper_bound (fun i => b i 1)
  obtain ⟨HP, hHP⟩ := finite_upper_bound (fun i => p i 1)
  let H := max HA (max HB HP) + D + 1
  have hhA : ∀ i, D < H - a i 1 := by
    intro i
    have := le_max_left HA (max HB HP)
    have := hHA i
    dsimp [H]; linarith
  have hhB : ∀ i, D < H - b i 1 := by
    intro i
    have := (le_max_left HB HP).trans (le_max_right HA (max HB HP))
    have := hHB i
    dsimp [H]; linarith
  have hhP : ∀ i, D < H - p i 1 := by
    intro i
    have := (le_max_right HB HP).trans (le_max_right HA (max HB HP))
    have := hHP i
    dsimp [H]; linarith
  let m₁ := expandCenters hA hmA' hgA hΛ
  let m₂ := reshapeMotion hA hB hAR hBR hvol (le_refl D) hΛA hag
  let m₃ := evacuateToParking hB hsize hΛA hpa hpp hhA hhP hD hga hgp
  let m₄ := evacuateToParking hB hsize hΛB hpb hpp hhB hhP hD hgb hgp
  let m₅ := expandCenters hB hmB' hgB hΛ
  exact ⟨η, hη, ⟨(((m₁.trans m₂).trans m₃).trans m₄.reverse).trans m₅.reverse⟩⟩

end BalancedTransport.Geometry
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem elementary_evacuateHighest {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (pr : RationalCenters p) (wr : RationalCenters w)
    (Hr : RationalConstant H)
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) (i : ι) (hi : i ∈ S) (hmax : ∀ j ∈ S, a j 1 ≤ a i 1) :
    ∃ m : BoxMotion ⟨remainingCenters a p S, w⟩ ⟨remainingCenters a p (S.erase i), w⟩ safe η,
      ElementaryMotion m := by
  let u := remainingCenters a p S
  let v₁ := Function.update (a i) 1 H
  let v₂ := Function.update (p i) 1 H
  have hui : u i = a i := by simp [u, remainingCenters, hi]
  have hu := remainingCenters_separated ha hcross hp S
  have hgu := remainingCenters_guarded hga hgp S
  have hv₁ : (BoxLayout.mk (Function.update u i v₁) w).Guarded safe :=
    guarded_update hgu i v₁ (by intro his; simpa [v₁] using hga i his)
  have hv₂ : (BoxLayout.mk (Function.update u i v₂) w).Guarded safe :=
    guarded_update hgu i v₂ (by intro his; simpa [v₂] using hgp i his)
  have hp₃ : (BoxLayout.mk (Function.update u i (p i)) w).Guarded safe :=
    guarded_update hgu i (p i) (fun his => hgp i his)
  have hfirst : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * u i k + r * v₁ k - u j k| := by
    intro r hr j hji
    rw [hui]
    by_cases hj : j ∈ S
    · have huj : u j = a j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact raising_gap (hmax j hj) (by linarith [hhigha i]) hr (ha i j (Ne.symm hji))
    · have huj : u j = p j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact fixed_first_gap (by simp [v₁]) (by simpa [v₁] using hcross i j)
  have hsecond : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₁) i k +
        r * v₂ k - (Function.update u i v₁) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply high_plane_gap (H := H) (by simp [v₁]) (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj] using hhigha j
    · simpa [u, remainingCenters, hj] using hhighp j
  have hthird : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₂) i k +
        r * p i k - (Function.update u i v₂) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply fixed_first_gap (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj, abs_sub_comm] using hcross j i
    · simpa [u, remainingCenters, hj] using hp i j (Ne.symm hji)
  have hsep₁ := hu.update i v₁ (fun j hji => by simpa using hfirst 1 ⟨by norm_num, le_rfl⟩ j hji)
  have hsep₂ : CenterSeparated (Function.update u i v₂) D := by
    have hh := hsep₁.update i v₂ (fun j hji => by simpa using hsecond 1 ⟨by norm_num, le_rfl⟩ j hji)
    simpa [Function.update_idem] using hh
  let m₁ := singleSegmentMotion i v₁ hwidth hsize hu hfirst hgu hv₁
  let m₂ := singleSegmentMotion i v₂ hwidth hsize hsep₁ hsecond hv₁
    (by simpa [Function.update_idem] using hv₂)
  let m₃ := singleSegmentMotion i (p i) hwidth hsize hsep₂ hthird hv₂
    (by simpa [Function.update_idem] using hp₃)
  have ur : RationalCenters u := rational_remaining ar pr S
  have v₁r : ∀ k, RationalConstant (v₁ k) := rational_space_update (ar i) 1 Hr
  have v₂r : ∀ k, RationalConstant (v₂ k) := rational_space_update (pr i) 1 Hr
  have e₁ : ElementaryMotion m₁ := elementary_singleSegment ur wr i v₁ v₁r _ _ _ _ _ _
  have e₂ : ElementaryMotion m₂ := elementary_singleSegment (ur.update i v₁r) wr i v₂ v₂r _ _ _ _ _ _
  have e₃ : ElementaryMotion m₃ := elementary_singleSegment (ur.update i v₂r) wr i (p i) (pr i) _ _ _ _ _ _
  have h₂ := Exists.intro m₂ e₂
  change ∃ m : BoxMotion ⟨Function.update u i v₁, w⟩
    ⟨Function.update (Function.update u i v₁) i v₂, w⟩ safe η, ElementaryMotion m at h₂
  rw [Function.update_idem] at h₂
  have h₃ := Exists.intro m₃ e₃
  change ∃ m : BoxMotion ⟨Function.update u i v₂, w⟩
    ⟨Function.update (Function.update u i v₂) i (p i), w⟩ safe η, ElementaryMotion m at h₃
  rw [Function.update_idem] at h₃
  obtain ⟨m₂',e₂'⟩ := h₂
  obtain ⟨m₃',e₃'⟩ := h₃
  have h : ElementaryMotion ((m₁.trans m₂').trans m₃') :=
    (e₁.trans e₂' ⟨ur.update i v₁r,wr⟩).trans e₃' ⟨ur.update i v₂r,wr⟩
  rw [remainingCenters_erase hi]
  exact ⟨_,h⟩

theorem elementary_evacuateToParking {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (pr : RationalCenters p) (wr : RationalCenters w)
    (Hr : RationalConstant H)
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe) :
    ∃ m : BoxMotion ⟨a, w⟩ ⟨p, w⟩ safe η, ElementaryMotion m := by
  have h : ∀ S : Finset ι, ∃ m : BoxMotion ⟨remainingCenters a p S, w⟩ ⟨p, w⟩ safe η,
      ElementaryMotion m := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi, hmax⟩ := S.exists_max_image (fun i => a i 1) hS
      obtain ⟨m,em⟩ := ih (S.erase i) (Finset.erase_ssubset hi)
      obtain ⟨v,ev⟩ := elementary_evacuateHighest ar pr wr Hr hwidth hsize ha hcross hp hhigha hhighp hD
        hga hgp S i hi hmax
      exact ⟨v.trans m, ev.trans em ⟨rational_remaining ar pr _,wr⟩⟩
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      have hempty : remainingCenters a p ∅ = p := by ext i k; simp [remainingCenters]
      rw [hempty]
      exact ⟨BoxMotion.stationary (A := ⟨p, w⟩) hwidth
        (separated_of_centerSeparated (fun i j hij => ⟨0, hp i j hij⟩) hsize) hgp,
        ElementaryMotion.stationary ⟨pr,wr⟩ _ _ _⟩
  have hh := h Finset.univ
  have he : remainingCenters a p Finset.univ = a := by ext i k; simp [remainingCenters]
  rw [he] at hh
  exact hh

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

lemma RationalConstant.max {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) :
    RationalConstant (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

lemma finite_upper_bound_nat {α : Type*} [Finite α] (f : α → ℝ) :
    ∃ R : ℕ, ∀ i, f i < (R : ℝ) := by
  obtain ⟨R,hR⟩ := finite_upper_bound f
  obtain ⟨N,hN⟩ := exists_nat_gt R
  exact ⟨N, fun i => (hR i).trans hN⟩

omit [Fintype ι] in
lemma scale_separation_mono {a : ι → Space} {D L N : ℝ} (hL : 0 ≤ L) (hLN : L ≤ N)
    (h : CenterSeparated (fun i k => L * a i k) D) :
    CenterSeparated (fun i k => N * a i k) D := by
  intro i j hij
  obtain ⟨k,hk⟩ := h i j hij
  refine ⟨k,hk.trans_le ?_⟩
  simp only [← mul_sub, abs_mul, abs_of_nonneg hL, abs_of_nonneg (hL.trans hLN)]
  exact mul_le_mul_of_nonneg_right hLN (abs_nonneg _)

lemma exists_nat_expansion {a b : ι → Space} (ha : Function.Injective a)
    (hb : Function.Injective b) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ L : ℕ, 1 ≤ (L : ℝ) ∧ R + 2 ≤ (L : ℝ) ∧
      CenterSeparated (fun i k => (L : ℝ) * a i k) D ∧
      CenterSeparated (fun i k => (L : ℝ) * b i k) D := by
  obtain ⟨L,hL,hLR,hLa,hLb⟩ := exists_expansion ha hb (R := R) hD
  obtain ⟨N,hN⟩ := exists_nat_gt L
  exact ⟨N,hL.trans hN.le,hLR.trans hN.le,
    scale_separation_mono (by linarith) hN.le hLa,
    scale_separation_mono (by linarith) hN.le hLb⟩

lemma exists_rational_parking (a b : ι → Space) {D R : ℝ} (hD : 0 ≤ D) :
    RationalConstant D → RationalConstant R →
    ∃ p : ι → Space, RationalCenters p ∧
      (∀ i j, D < |a i 0 - p j 0|) ∧
      (∀ i j, D < |b i 0 - p j 0|) ∧
      (∀ i j, i ≠ j → D < |p i 0 - p j 0|) ∧
      (∀ i, 2 + R < p i 0) := by
  classical
  intro Dr Rr
  obtain ⟨La, hLa⟩ := finite_upper_bound_nat (fun i => a i 0)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound_nat (fun i => b i 0)
  let K := max (3 + R) (max (La : ℝ) (Lb : ℝ)) + D + 1
  let e := Fintype.equivFin ι
  let p : ι → Space := fun i => ![K + (D + 1) * (e i).val, 0, 0]
  have hKs : 2 + R < K := by dsimp [K]; have := le_max_left (3 + R) (max (La : ℝ) (Lb : ℝ)); linarith
  have hKa : ∀ i, D < K - a i 0 := by
    intro i
    have := (le_max_left (La : ℝ) (Lb : ℝ)).trans (le_max_right (3 + R) (max (La : ℝ) (Lb : ℝ)))
    have := hLa i
    dsimp [K]
    linarith
  have hKb : ∀ i, D < K - b i 0 := by
    intro i
    have := (le_max_right (La : ℝ) (Lb : ℝ)).trans (le_max_right (3 + R) (max (La : ℝ) (Lb : ℝ)))
    have := hLb i
    dsimp [K]
    linarith
  have hpn : ∀ i, K ≤ p i 0 := by
    intro i
    dsimp [p]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have Kr : RationalConstant K :=
    ((RationalConstant.nat 3).add Rr |>.max
      ((RationalConstant.nat La).max (RationalConstant.nat Lb))).add Dr |>.add RationalConstant.one
  have pr : RationalCenters p := by
    intro i k
    fin_cases k
    · exact Kr.add ((Dr.add RationalConstant.one).mul (RationalConstant.nat _))
    · exact RationalConstant.zero
    · exact RationalConstant.zero
  refine ⟨p, pr, ?_, ?_, ?_, fun i => hKs.trans_le (hpn i)⟩
  · intro i j
    have := hKa i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - a i 0) (le_abs_self _)
  · intro i j
    have := hKb i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - b i 0) (le_abs_self _)
  · intro i j hij
    have hv : (e i).val ≠ (e j).val := by intro h; exact hij (e.injective (Fin.ext h))
    have hh : (1 : ℝ) ≤ |(e i).val - ((e j).val : ℝ)| := by
      rcases lt_or_gt_of_ne hv with hl | hl
      · have hcast : ((e i).val : ℝ) + 1 ≤ (e j).val := by exact_mod_cast hl
        rw [abs_of_nonpos (by linarith : ((e i).val : ℝ) - (e j).val ≤ 0)]
        linarith
      · have hcast : ((e j).val : ℝ) + 1 ≤ (e i).val := by exact_mod_cast hl
        rw [abs_of_nonneg (by linarith : 0 ≤ ((e i).val : ℝ) - (e j).val)]
        linarith
    have he : p i 0 - p j 0 = (D + 1) * (((e i).val : ℝ) - (e j).val) := by dsimp [p]; ring
    rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ D + 1)]
    nlinarith

theorem elementary_guarded_solid_box_motion (A B : BoxLayout ι) (safe : Set ι)
    (Ar : RationalLayout A) (Br : RationalLayout B)
    (hA : A.Positive) (hB : B.Positive)
    (hsA : A.Separated 0) (hsB : B.Separated 0)
    (hvol : ∀ i, ∏ k, A.width i k = ∏ k, B.width i k)
    (hgA : A.Guarded safe) (hgB : B.Guarded safe) :
    ∃ η : ℚ, 0 < η ∧ ∃ m : BoxMotion A B safe (η : ℝ), ElementaryMotion m := by
  classical
  obtain ⟨ηA, hηA, hmA⟩ := hsA.positive_margin
  obtain ⟨ηB, hηB, hmB⟩ := hsB.positive_margin
  obtain ⟨q,hq,hqm⟩ := exists_rat_btwn (lt_min hηA hηB)
  let η : ℝ := q
  have hη : 0 < η := hq
  have ηr : RationalConstant η := RationalConstant.rat q
  have hmA' := hmA.mono (hqm.le.trans (min_le_left ηA ηB))
  have hmB' := hmB.mono (hqm.le.trans (min_le_right ηA ηB))
  obtain ⟨RA, hRA⟩ := finite_upper_bound_nat (fun p : ι × Fin 3 => A.width p.1 p.2)
  obtain ⟨RB, hRB⟩ := finite_upper_bound_nat (fun p : ι × Fin 3 => B.width p.1 p.2)
  let R : ℝ := max 1 (max (RA : ℝ) (RB : ℝ))
  have Rr : RationalConstant R := RationalConstant.one.max
    ((RationalConstant.nat RA).max (RationalConstant.nat RB))
  have hR : 1 ≤ R := le_max_left _ _
  have hAR : ∀ i k, A.width i k ≤ R := fun i k => (hRA (i,k)).le.trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hBR : ∀ i k, B.width i k ≤ R := fun i k => (hRB (i,k)).le.trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let D := 2 * R + 4 * η
  have hD : 0 ≤ D := by dsimp [D]; linarith
  obtain ⟨L, hΛ, hΛR, hΛA, hΛB⟩ := exists_nat_expansion
    (BoxLayout.center_injective hA hsA) (BoxLayout.center_injective hB hsB) (R := R) hD
  let Λ : ℝ := L
  have Λr : RationalConstant Λ := RationalConstant.nat L
  let a : ι → Space := fun i k => Λ * A.center i k
  let b : ι → Space := fun i k => Λ * B.center i k
  have ar : RationalCenters a := fun i k => Λr.mul (Ar.1 i k)
  have br : RationalCenters b := fun i k => Λr.mul (Br.1 i k)
  have Dr : RationalConstant D := ((RationalConstant.nat 2).mul Rr).add
    ((RationalConstant.nat 4).mul ηr)
  obtain ⟨p, pr, hpa, hpb, hpp, hpg⟩ := exists_rational_parking a b (R := R) hD Dr Rr
  have hag : ∀ i ∈ safe, 2 + R < a i 0 := by
    intro i hi
    have hh : 2 < A.center i 0 := by have := hgA i hi; linarith [hA i 0]
    have hΛp : 0 < Λ := by linarith
    have hh' := mul_lt_mul_of_pos_left hh hΛp
    dsimp [a]
    nlinarith
  have hbg : ∀ i ∈ safe, 2 + R < b i 0 := by
    intro i hi
    have hh : 2 < B.center i 0 := by have := hgB i hi; linarith [hB i 0]
    have hΛp : 0 < Λ := by linarith
    have hh' := mul_lt_mul_of_pos_left hh hΛp
    dsimp [b]
    nlinarith
  have hga : (BoxLayout.mk a B.width).Guarded safe := by
    intro i hi
    change 2 < a i 0 - B.width i 0
    linarith [hag i hi, hBR i 0]
  have hgb : (BoxLayout.mk b B.width).Guarded safe := by
    intro i hi
    change 2 < b i 0 - B.width i 0
    linarith [hbg i hi, hBR i 0]
  have hgp : (BoxLayout.mk p B.width).Guarded safe := by
    intro i _
    change 2 < p i 0 - B.width i 0
    linarith [hpg i, hBR i 0]
  have hsize : ∀ i j k, B.width i k + B.width j k + 4 * η ≤ D := by
    intro i j k
    dsimp [D]
    linarith [hBR i k, hBR j k]
  obtain ⟨HA, hHA⟩ := finite_upper_bound_nat (fun i => a i 1)
  obtain ⟨HB, hHB⟩ := finite_upper_bound_nat (fun i => b i 1)
  obtain ⟨HP, hHP⟩ := finite_upper_bound_nat (fun i => p i 1)
  let H : ℝ := max (HA : ℝ) (max (HB : ℝ) (HP : ℝ)) + D + 1
  have Hr : RationalConstant H := ((RationalConstant.nat HA).max
    ((RationalConstant.nat HB).max (RationalConstant.nat HP))).add Dr |>.add RationalConstant.one
  have hhA : ∀ i, D < H - a i 1 := by
    intro i
    have := le_max_left (HA : ℝ) (max (HB : ℝ) (HP : ℝ))
    have := hHA i
    dsimp [H]; linarith
  have hhB : ∀ i, D < H - b i 1 := by
    intro i
    have := (le_max_left (HB : ℝ) (HP : ℝ)).trans (le_max_right (HA : ℝ) (max (HB : ℝ) (HP : ℝ)))
    have := hHB i
    dsimp [H]; linarith
  have hhP : ∀ i, D < H - p i 1 := by
    intro i
    have := (le_max_right (HB : ℝ) (HP : ℝ)).trans (le_max_right (HA : ℝ) (max (HB : ℝ) (HP : ℝ)))
    have := hHP i
    dsimp [H]; linarith
  let m₁ := expandCenters hA hmA' hgA hΛ
  let m₂ := reshapeMotion hA hB hAR hBR hvol (le_refl D) hΛA hag
  obtain ⟨m₃,e₃⟩ := elementary_evacuateToParking ar pr Br.2 Hr hB hsize hΛA hpa hpp hhA hhP hD hga hgp
  obtain ⟨m₄,e₄⟩ := elementary_evacuateToParking br pr Br.2 Hr hB hsize hΛB hpb hpp hhB hhP hD hgb hgp
  let m₅ := expandCenters hB hmB' hgB hΛ
  have e₁ : ElementaryMotion m₁ := ElementaryMotion.expansion Ar.1 Ar.2 Λr _ _ _ _
  have e₂ : ElementaryMotion m₂ := ElementaryMotion.reshape ar Ar.2 Br.2 _ _ _ _ _ _ _ _
  have e₅ : ElementaryMotion m₅ := ElementaryMotion.expansion Br.1 Br.2 Λr _ _ _ _
  exact ⟨q, by exact_mod_cast hq, _,
    (((e₁.trans e₂ ⟨ar,Ar.2⟩).trans e₃ ⟨ar,Br.2⟩).trans e₄.reverse ⟨pr,Br.2⟩).trans
      e₅.reverse ⟨br,Br.2⟩⟩

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

theorem inverse_base_pos : 0 < (base Q Γ : ℝ)⁻¹ :=
  inv_pos.mpr (Nat.cast_pos.mpr base_pos)

theorem inverse_base_le_one : (base Q Γ : ℝ)⁻¹ ≤ 1 := by
  have h : (1 : ℝ) ≤ base Q Γ := by exact_mod_cast base_pos (Q := Q) (Γ := Γ)
  exact inv_le_one_of_one_le₀ h

theorem digit_unit_bound (a : Letter Q Γ) :
    (base Q Γ : ℝ)⁻¹ * ((digit a : ℝ) + 1) ≤ 1 := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_one (Nat.cast_pos.mpr base_pos)).mpr (digit_upper a).le

def Configuration.stacks (c : Configuration Q Γ) : Fin 3 → Stream' (Letter Q Γ) :=
  ![c.left, c.right, c.history]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]
variable [DecidableEq Q]

def Configuration.code (M : Machine Q Γ) (c : Configuration Q Γ) : Space :=
  Coding.codedPoint digit (Coding.origin (placement M c.control)) c.stacks

def Instruction.fullMap (M : Machine Q Γ) (inst : Instruction Q Γ) : Space → Space :=
  Coding.boxMap (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ))
    (Coding.origin (placement M inst.sourceControl))
    (Coding.origin (placement M inst.targetControl)) inst.sourcePrefixes inst.targetPrefixes

theorem Instruction.fullMap_code (M : Machine Q Γ) (inst : Instruction Q Γ)
    (t : Tails Q Γ) :
    inst.fullMap M ((inst.source t).code M) = (inst.target t).code M := by
  let tails : Fin 3 → Stream' (Letter Q Γ) := ![t.left, t.right, t.history]
  have hs : (inst.source t).stacks = fun i => inst.sourcePrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  have ht : (inst.target t).stacks = fun i => inst.targetPrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  unfold fullMap Configuration.code
  rw [hs, ht]
  exact Coding.boxMap_codedPoint (Nat.ne_of_gt base_pos) _ _ _ _ _ _

theorem Instruction.source_code_mem (M : Machine Q Γ) (inst : Instruction Q Γ)
    (t : Tails Q Γ) :
    (inst.source t).code M ∈
      inst.sourceBox (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) := by
  let tails : Fin 3 → Stream' (Letter Q Γ) := ![t.left, t.right, t.history]
  have hs : (inst.source t).stacks = fun i => inst.sourcePrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  change Coding.codedPoint digit _ (inst.source t).stacks ∈ _
  rw [hs]
  exact Coding.codedPoint_mem_box _ _ _ _

theorem compiled_boxes_disjoint [DecidableEq Γ] (M : Machine Q Γ) :
    ((table M : Set (Row Q Γ)).Pairwise fun a b =>
      Disjoint ((a.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))
      ((b.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))) ∧
    ((table M : Set (Row Q Γ)).Pairwise fun a b =>
      Disjoint ((a.instruction M).targetBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))
      ((b.instruction M).targetBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))) := by
  constructor
  · intro a ha b hb hab
    exact source_boxes_disjoint M inverse_base_pos _ (fun a => (digit_pos a).le)
      digit_unit_bound digit_gap (placement M) (placement_injective M)
      ((mem_table M a).mp ha) ((mem_table M b).mp hb) hab
  · intro a _ b _ hab
    exact target_boxes_disjoint M inverse_base_pos _ (fun a => (digit_pos a).le)
      digit_unit_bound digit_gap (placement M) (placement_injective M) hab

omit [DecidableEq Q] in

theorem prefix_halfWidth (w : List (Letter Q Γ)) :
    0 < (base Q Γ : ℝ)⁻¹ ^ w.length / 2 ∧
    (base Q Γ : ℝ)⁻¹ ^ w.length / 2 ≤ 1 / 2 := by
  have hp := pow_pos (inverse_base_pos (Q := Q) (Γ := Γ)) w.length
  have hle := pow_le_one₀ (inverse_base_pos (Q := Q) (Γ := Γ)).le
    (inverse_base_le_one (Q := Q) (Γ := Γ)) (n := w.length)
  constructor <;> linarith

theorem nonhalt_box_guard (M : Machine Q Γ) (s : Control Q) (hs : s ≠ .ready M.halt)
    (u : Fin 3 → List (Letter Q Γ)) {x : Space}
    (hx : x ∈ Coding.box (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ))
      (Coding.origin (placement M s)) u) : 4 ≤ x 0 := by
  have hl := (Coding.interval_subset_unit inverse_base_pos _ (fun a => (digit_pos a).le)
    digit_unit_bound (u 0) (hx 0)).1
  have hp : (1 : ℝ) ≤ placement M s := by exact_mod_cast placement_positive M s hs
  simp only [Coding.origin, Matrix.cons_val_zero] at hl
  linarith

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] in

theorem Row.sourceControl_ne_halt (M : Machine Q Γ) (a : Row Q Γ) (ha : a.valid M) :
    (a.instruction M).sourceControl ≠ .ready M.halt := by
  cases a <;> simp_all [Row.valid, Row.instruction]

theorem source_box_guard (M : Machine Q Γ) (a : Row Q Γ) (ha : a.valid M) {x : Space}
    (hx : x ∈ (a.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
      (fun c => (digit c : ℝ)) (placement M)) : 4 ≤ x 0 :=
  nonhalt_box_guard M _ (a.sourceControl_ne_halt M ha) _ hx

theorem code_mem_observer_iff (M : Machine Q Γ) (c : Configuration Q Γ) :
    c.code M ∈ observer ↔ c.control = .ready M.halt := by
  have hi : ∀ i : Fin 3, Coding.stream digit (c.stacks i) ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i
    exact Coding.stream_mem_interior base_pos digit digit_pos digit_upper _
  constructor
  · intro h
    by_contra hc
    have hp : (1 : ℝ) ≤ placement M c.control := by
      exact_mod_cast placement_positive M c.control hc
    have hi₀ := hi 0
    have hh : c.code M 0 < 2 := (h 0 (Set.mem_univ _)).2
    simp only [Configuration.code, Coding.codedPoint, Coding.origin, Matrix.cons_val_zero] at hh
    linarith [hi₀.1]
  · intro hc i _
    have ho : Coding.origin (placement M c.control) i = 0 := by
      rw [hc, placement_halt]
      fin_cases i <;> simp [Coding.origin]
    change -1 < Coding.origin (placement M c.control) i + Coding.stream digit (c.stacks i) ∧
      Coding.origin (placement M c.control) i + Coding.stream digit (c.stacks i) < 2
    rw [ho, zero_add]
    constructor <;> linarith [(hi i).1, (hi i).2]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

structure Checkpoint (Q Γ : Type*) where
  state : Q
  left : Stream' Γ
  current : Γ
  right : List Γ
  history : Stream' (Letter Q Γ)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control

def expand (M : Machine Q Γ) (c : Checkpoint Q Γ) : Configuration Q Γ :=
  ⟨ready c.state, Stream'.map work c.left,
    work c.current :: (c.right.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
    c.history⟩

def next (M : Machine Q Γ) (c : Checkpoint Q Γ) : Checkpoint Q Γ :=
  let v := M.transition c.state c.current
  match v.move with
  | .stay => ⟨v.state, c.left, v.write, c.right, record (.stay c.state c.current) :: c.history⟩
  | .left => ⟨v.state, c.left.tail, c.left.head, v.write :: c.right,
      record (.left c.state c.current c.left.head) :: c.history⟩
  | .right =>
      match c.right with
      | [] => ⟨v.state, v.write :: c.left, M.blank, [],
          record (.extend c.state c.current) :: c.history⟩
      | List.cons a w => ⟨v.state, v.write :: c.left, a, w,
          record (.right c.state c.current a) :: c.history⟩

def WorkStep (M : Machine Q Γ) (c d : Checkpoint Q Γ) : Prop :=
  c.state ≠ M.halt ∧ d = c.next M

theorem next_exec (M : Machine Q Γ) (c : Checkpoint Q Γ) (hc : c.state ≠ M.halt) :
    Exec M (2 * (c.right.length + 1) + 2) (c.expand M) ((c.next M).expand M) := by
  cases hm : (M.transition c.state c.current).move with
  | stay =>
      simpa [next, hm, expand] using
        checkpoint_stay M c.state hc c.current hm c.right (Stream'.map work c.left) c.history
  | left =>
      have h := checkpoint_left M c.state hc c.current c.left.head hm c.right
        (Stream'.map work c.left.tail) c.history
      have hl : (work c.left.head :: Stream'.map work c.left.tail : Stream' (Letter Q Γ)) =
          Stream'.map work c.left := by
        funext n
        cases n <;> rfl
      simpa only [next, hm, expand, List.map_cons, Stream'.appendStream', hl] using h
  | right =>
      cases hw : c.right with
      | nil =>
          simpa [next, hm, expand, hw, Stream'.map_cons] using
            checkpoint_extend M c.state hc c.current hm (Stream'.map work c.left) c.history
      | cons a w =>
          simpa [next, hm, expand, hw, Stream'.map_cons, Stream'.appendStream', Nat.add_assoc] using
            checkpoint_right M c.state hc c.current a hm w (Stream'.map work c.left) c.history

theorem work_execution (M : Machine Q Γ) {c d : Checkpoint Q Γ}
    (h : Relation.ReflTransGen (WorkStep M) c d) :
    ∃ n, Exec M n (c.expand M) (d.expand M) := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | @tail d e hd hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨hnh, rfl⟩ := hstep
      exact ⟨_, hn.trans (next_exec M d hnh)⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

theorem no_step_from_halt (M : Machine Q Γ) {c d : Configuration Q Γ}
    (hc : c.control = .ready M.halt) : ¬Step M c d := by
  rintro ⟨r, hr, t, rfl, _⟩
  exact r.sourceControl_ne_halt M hr hc

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ] {M : Machine Q Γ}

theorem cancel_to_terminal {n m : ℕ} {c d e : Configuration Q Γ}
    (h : Exec M n c d) (g : Exec M m c e) (hd : ∀ f, ¬Step M d f) :
    ∃ k, n = m + k ∧ Exec M k e d := by
  induction g generalizing n with
  | refl => exact ⟨n, by omega, h⟩
  | @cons m c b e hcb hbe ih =>
      cases h with
      | refl => exact False.elim (hd b hcb)
      | @cons n c a d hca had =>
          have he := step_deterministic M hca hcb
          subst a
          obtain ⟨k, hk, he⟩ := ih had
          exact ⟨k, by omega, he⟩

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ]

theorem halt_reflection (M : Machine Q Γ) {n : ℕ} {c : Checkpoint Q Γ}
    {d : Configuration Q Γ} (h : Exec M n (c.expand M) d)
    (hd : d.control = .ready M.halt) :
    ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  induction n using Nat.strong_induction_on generalizing c d with
  | h n ih =>
      by_cases hc : c.state = M.halt
      · exact ⟨c, .refl, hc⟩
      · obtain ⟨k, hk, hkd⟩ := h.cancel_to_terminal (next_exec M c hc)
          (fun f => no_step_from_halt M hd)
        have hkn : k < n := by omega
        obtain ⟨e, he, hehalt⟩ := ih k hkn hkd hd
        exact ⟨e, (Relation.ReflTransGen.single (show WorkStep M c (c.next M) from
          ⟨hc, rfl⟩)).trans he, hehalt⟩

theorem halting_iff (M : Machine Q Γ) (c : Checkpoint Q Γ) :
    (∃ n d, Exec M n (c.expand M) d ∧ d.control = .ready M.halt) ↔
      ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  constructor
  · rintro ⟨n, d, h, hd⟩
    exact halt_reflection M h hd
  · rintro ⟨e, h, he⟩
    obtain ⟨n, hn⟩ := work_execution M h
    exact ⟨n, e.expand M, hn, by simpa [expand] using he⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def rationalWord {B : ℕ} (digit : S → Fin B) : List S → ℚ
  | [] => 0
  | a :: w => (B : ℚ)⁻¹ * ((digit a : ℚ) + rationalWord digit w)

theorem rationalWord_cast {B : ℕ} (digit : S → Fin B) (w : List S) :
    (rationalWord digit w : ℝ) = word (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w := by
  induction w with
  | nil => simp [rationalWord]
  | cons a w ih => simp [rationalWord, word, ih]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem stream_const {B : ℕ} (hB : 1 < B) (digit : S → Fin B) (a : S) :
    stream digit (Stream'.const a) = (digit a : ℝ) / ((B : ℝ) - 1) := by
  have hs : (a :: Stream'.const a : Stream' S) = Stream'.const a := by
    funext n
    cases n <;> rfl
  have he := stream_cons digit a (Stream'.const a)
  rw [hs, mul_comm, ← div_eq_mul_inv] at he
  have hB' : (1 : ℝ) < B := by exact_mod_cast hB
  have hn : (B : ℝ) ≠ 0 := by linarith
  have hsub : (B : ℝ) - 1 ≠ 0 := by linarith
  apply (eq_div_iff hsub).mpr
  have he' := (eq_div_iff hn).mp he
  nlinarith only [he']

def rationalTailCode {B : ℕ} (digit : S → Fin B) (w : List S) (a : S) : ℚ :=
  rationalWord digit w + (B : ℚ)⁻¹ ^ w.length * ((digit a : ℚ) / ((B : ℚ) - 1))

theorem rationalTailCode_cast {B : ℕ} (hB : 1 < B) (digit : S → Fin B)
    (w : List S) (a : S) :
    (rationalTailCode digit w a : ℝ) = stream digit (w ++ₛ Stream'.const a) := by
  rw [stream_append, stream_const hB]
  simp [rationalTailCode, prefixPoint, rationalWord_cast]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter

def initial (M : Machine Q Γ) (q₀ : Q) (w : List Γ) : Checkpoint Q Γ :=
  ⟨q₀, Stream'.const M.blank, w.headD M.blank, w.tail, Stream'.const (work M.blank)⟩

theorem initial_work_block (M : Machine Q Γ) (q₀ : Q) (w : List Γ) :
    (initial M q₀ w).current :: (initial M q₀ w).right =
      if w = [] then [M.blank] else w := by
  cases w <;> simp [initial]

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

omit [DecidableEq Q] in

theorem base_gt_one : 1 < base Q Γ := by
  have hh : 0 < Fintype.card (Letter Q Γ) := Fintype.card_pos_iff.mpr ⟨.boundary⟩
  dsimp [base]
  omega

def rationalInitial (M : Machine Q Γ) (q₀ : Q) (w : List Γ) : Fin 3 → ℚ :=
  let b := Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) [] (work M.blank : Letter Q Γ)
  let v : List (Letter Q Γ) := work (w.headD M.blank) :: (w.tail.map work ++ [boundary])
  ![4 * (placement M (.ready q₀) : ℚ) + b,
    Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) v (work M.blank), b]

theorem rationalInitial_cast (M : Machine Q Γ) (q₀ : Q) (w : List Γ) :
    rationalSpace (rationalInitial M q₀ w) = ((initial M q₀ w).expand M).code M := by
  have hb := Coding.rationalTailCode_cast (base_gt_one (Q := Q) (Γ := Γ))
    digit [] (work M.blank : Letter Q Γ)
  have hr := Coding.rationalTailCode_cast (base_gt_one (Q := Q) (Γ := Γ))
    digit (work (w.headD M.blank) :: (w.tail.map work ++ [boundary]))
    (work M.blank : Letter Q Γ)
  have hr' : (Coding.rationalTailCode (digit (Q := Q) (Γ := Γ))
      (work (w.headD M.blank) :: (w.tail.map work ++ [boundary])) (work M.blank) : ℝ) =
      Coding.stream (digit (Q := Q) (Γ := Γ)) (work (w.headD M.blank) ::
        (w.tail.map work ++ₛ (boundary :: Stream'.const (work M.blank)))) := by
    simpa only [Stream'.appendStream', Stream'.append_append_stream] using hr
  simp only [Stream'.nil_append_stream] at hb
  funext i
  fin_cases i
  · simp [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial, Stream'.map_const, hb]
  · simpa [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial] using hr'
  · simpa [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial] using hb

end BalancedTransport.Recorder.Checkpoint
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

theorem coded_halting_iff {Q Γ : Type*} [Fintype Q] [Fintype Γ]
    [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ) (c : Checkpoint Q Γ) :
    (∃ n d, Exec M n (c.expand M) d ∧ d.code M ∈ observer) ↔
      ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  constructor
  · rintro ⟨n, d, h, hd⟩
    exact (halting_iff M c).mp ⟨n, d, h, (code_mem_observer_iff M d).mp hd⟩
  · intro h
    obtain ⟨n, d, hh, hd⟩ := (halting_iff M c).mpr h
    exact ⟨n, d, hh, (code_mem_observer_iff M d).mpr hd⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine

def normalized (M : FiniteMachine) :
    Recorder.Machine (Option (Fin (M.states + 1))) (Fin (M.symbols + 1)) where
  halt := none
  blank := M.blank
  transition q a := match q with
    | none => ⟨none, a, .stay⟩
    | some q => match M.transition q a with
      | none => ⟨none, a, .stay⟩
      | some v => ⟨some v.state, v.write, v.move⟩

abbrev WorkConfiguration (M : FiniteMachine) :=
  Recorder.Checkpoint (Option (Fin (M.states + 1))) (Fin (M.symbols + 1))

def initialWork (M : FiniteMachine) (w : Input M) : WorkConfiguration M :=
  Recorder.Checkpoint.initial M.normalized (some M.initial) w

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.TapeConfiguration

def advance {M : FiniteMachine} (c : TapeConfiguration M)
    (v : Recorder.Transition (Fin (M.states + 1)) (Fin (M.symbols + 1))) :
    TapeConfiguration M :=
  ⟨v.state, c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1),
    Function.update c.tape c.head v.write⟩

end BalancedTransport.TapeConfiguration
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
open Stream'

structure Represents (M : FiniteMachine) (w : M.WorkConfiguration)
    (c : TapeConfiguration M) : Prop where
  current : w.current = c.tape c.head
  left : ∀ n : ℕ, w.left n = c.tape (c.head - ((n : ℤ) + 1))
  right : ∀ n : ℕ, w.right[n]?.getD M.blank = c.tape (c.head + ((n : ℤ) + 1))

theorem initialWork_represents (M : FiniteMachine) (w : Input M) :
    Represents M (M.initialWork w) (initialConfiguration M w) := by
  constructor
  · cases w <;> simp [initialWork, Checkpoint.initial, normalized, initialConfiguration]
  · intro n
    change M.blank = (if 0 ≤ (0 : ℤ) - ((n : ℤ) + 1)
      then w[((0 : ℤ) - ((n : ℤ) + 1)).toNat]?.getD M.blank else M.blank)
    rw [ite_eq_right (by omega)]
  · intro n
    simp only [initialWork, Checkpoint.initial, normalized, initialConfiguration, zero_add,
      show (0 : ℤ) ≤ (n : ℤ) + 1 by omega, ↓reduceIte]
    have hn : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [hn]
    cases w <;> simp

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.FiniteMachine.Represents
open Recorder
open Stream'
variable {M : FiniteMachine} {w : M.WorkConfiguration} {c : TapeConfiguration M}

theorem advance (h : Represents M w c)
    (v : Transition (Fin (M.states + 1)) (Fin (M.symbols + 1)))
    (hv : M.normalized.transition w.state w.current = ⟨some v.state, v.write, v.move⟩) :
    Represents M (w.next M.normalized) (c.advance v) := by
  cases hm : v.move with
  | stay =>
      simp only [Checkpoint.next, hv, hm]
      constructor
      · simp [TapeConfiguration.advance, hm]
      · intro n
        change w.left n = Function.update c.tape c.head v.write
          (c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1) -
            ((n : ℤ) + 1))
        simp only [hm, add_zero]
        rw [Function.update_of_ne (by omega) _ _]
        exact h.left n
      · intro n
        simp only [TapeConfiguration.advance, hm, add_zero]
        rw [Function.update_of_ne (by omega) _ _]
        exact h.right n
  | left =>
      simp only [Checkpoint.next, hv, hm]
      constructor
      · simp only [TapeConfiguration.advance, hm, Stream'.head, Stream'.get]
        rw [Function.update_of_ne (by omega) _ _]
        simpa [sub_eq_add_neg] using h.left 0
      · intro n
        simp only [TapeConfiguration.advance, hm, Stream'.tail, Stream'.get]
        rw [Function.update_of_ne (by omega) _ _]
        convert h.left (n + 1) using 1
        congr 1
        omega
      · intro n
        simp only [TapeConfiguration.advance, hm]
        cases n with
        | zero => simp
        | succ n =>
            rw [Function.update_of_ne (by omega) _ _]
            simp only [List.getElem?_cons_succ]
            convert h.right n using 1
            congr 1
            omega
  | right =>
      cases hr : w.right with
      | nil =>
          simp only [Checkpoint.next, hv, hm, hr]
          constructor
          · simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            change M.blank = c.tape (c.head + 1)
            simpa only [hr, List.getElem?_nil, Option.getD_none, Nat.cast_zero, zero_add]
              using h.right 0
          · intro n
            simp only [TapeConfiguration.advance, hm]
            cases n with
            | zero => simp [Stream'.cons]
            | succ n =>
                rw [Function.update_of_ne (by omega) _ _]
                simp only [Stream'.cons]
                convert h.left n using 1
                congr 1
                omega
          · intro n
            simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            have he : c.head + 1 + ((n : ℤ) + 1) =
                c.head + (((n + 1 : ℕ) : ℤ) + 1) := by omega
            rw [he]
            simpa only [hr, List.getElem?_nil, Option.getD_none] using h.right (n + 1)
      | cons a r =>
          simp only [Checkpoint.next, hv, hm, hr]
          constructor
          · simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            simpa only [hr, List.getElem?_cons_zero, Option.getD_some, Nat.cast_zero, zero_add]
              using h.right 0
          · intro n
            simp only [TapeConfiguration.advance, hm]
            cases n with
            | zero => simp [Stream'.cons]
            | succ n =>
                rw [Function.update_of_ne (by omega) _ _]
                simp only [Stream'.cons]
                convert h.left n using 1
                congr 1
                omega
          · intro n
            simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            have he : c.head + 1 + ((n : ℤ) + 1) =
                c.head + (((n + 1 : ℕ) : ℤ) + 1) := by omega
            rw [he]
            simpa only [hr, List.getElem?_cons_succ] using h.right (n + 1)

theorem stop (h : Represents M w c)
    (hv : M.normalized.transition w.state w.current = ⟨none, w.current, .stay⟩) :
    Represents M (w.next M.normalized) c := by
  simp only [Checkpoint.next, hv]
  exact ⟨h.current, h.left, h.right⟩

end BalancedTransport.FiniteMachine.Represents
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

theorem next_state {Q Γ : Type*} (M : Machine Q Γ) (w : Checkpoint Q Γ) :
    (w.next M).state = (M.transition w.state w.current).state := by
  cases hm : (M.transition w.state w.current).move <;>
    simp only [next, hm]
  cases w.right <;> rfl

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
variable {M : FiniteMachine}

theorem lift_step {c d : TapeConfiguration M} {w : M.WorkConfiguration}
    (h : machineStep M c = some d) (hs : w.state = some c.state)
    (ht : Represents M w c) :
    Checkpoint.WorkStep M.normalized w (w.next M.normalized) ∧
    (w.next M.normalized).state = some d.state ∧
    Represents M (w.next M.normalized) d := by
  cases hv : M.transition c.state (c.tape c.head) with
  | none => simp [machineStep, hv] at h
  | some v =>
      have hd : c.advance v = d := by
        cases hm : v.move <;>
          simpa only [machineStep, hv, Option.map_some, Option.some.injEq,
            TapeConfiguration.advance, hm] using h
      subst d
      have hv' : M.normalized.transition w.state w.current =
          ⟨some v.state, v.write, v.move⟩ := by
        simp [normalized, hs, ht.current, hv]
      refine ⟨⟨?_, rfl⟩, ?_, ht.advance v hv'⟩
      · simp [normalized, hs]
      · rw [Checkpoint.next_state, hv']
        rfl

theorem lift_execution {c d : TapeConfiguration M}
    (h : Relation.ReflTransGen (fun c d => machineStep M c = some d) c d)
    {w : M.WorkConfiguration} (hs : w.state = some c.state) (ht : Represents M w c) :
    ∃ w', Relation.ReflTransGen (Checkpoint.WorkStep M.normalized) w w' ∧
      w'.state = some d.state ∧ Represents M w' d := by
  induction h with
  | refl => exact ⟨w, .refl, hs, ht⟩
  | @tail c' d hc' hd ih =>
      obtain ⟨w', hw', hs', ht'⟩ := ih
      obtain ⟨hstep, hs'', ht''⟩ := lift_step hd hs' ht'
      exact ⟨w'.next M.normalized, hw'.tail hstep, hs'', ht''⟩

theorem lift_halt {c : TapeConfiguration M} {w : M.WorkConfiguration}
    (h : machineStep M c = none) (hs : w.state = some c.state)
    (ht : Represents M w c) :
    Checkpoint.WorkStep M.normalized w (w.next M.normalized) ∧
    (w.next M.normalized).state = none := by
  have hv : M.transition c.state (c.tape c.head) = none := by
    simpa only [machineStep, Option.map_eq_none_iff] using h
  have hv' : M.normalized.transition w.state w.current =
      ⟨none, w.current, .stay⟩ := by
    simp [normalized, hs, ht.current, hv]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · simp [normalized, hs]
  · rw [Checkpoint.next_state, hv']

def Corresponds (M : FiniteMachine) (w : M.WorkConfiguration)
    (c : TapeConfiguration M) : Prop :=
  Represents M w c ∧
    (w.state = some c.state ∨ (w.state = none ∧ machineStep M c = none))

theorem reflect_step {c : TapeConfiguration M} {w w' : M.WorkConfiguration}
    (hc : Corresponds M w c) (h : Checkpoint.WorkStep M.normalized w w') :
    ∃ d, Relation.ReflTransGen (fun c d => machineStep M c = some d) c d ∧
      Corresponds M w' d := by
  obtain ⟨ht, hs | ⟨hs, _⟩⟩ := hc
  · obtain ⟨hnh, rfl⟩ := h
    cases hv : M.transition c.state (c.tape c.head) with
    | none =>
        have hv' : M.normalized.transition w.state w.current =
            ⟨none, w.current, .stay⟩ := by
          simp [normalized, hs, ht.current, hv]
        refine ⟨c, .refl, ht.stop hv', Or.inr ⟨?_, ?_⟩⟩
        · rw [Checkpoint.next_state, hv']
        · simp [machineStep, hv]
    | some v =>
        have hd : machineStep M c = some (c.advance v) := by
          cases hm : v.move <;> simp [machineStep, hv, TapeConfiguration.advance, hm]
        obtain ⟨_, hs', ht'⟩ := lift_step hd hs ht
        exact ⟨c.advance v, .single hd, ht', Or.inl hs'⟩
  · exact False.elim (h.1 hs)

theorem reflect_execution {c : TapeConfiguration M} {w w' : M.WorkConfiguration}
    (hc : Corresponds M w c)
    (h : Relation.ReflTransGen (Checkpoint.WorkStep M.normalized) w w') :
    ∃ d, Relation.ReflTransGen (fun c d => machineStep M c = some d) c d ∧
      Corresponds M w' d := by
  induction h with
  | refl => exact ⟨c, .refl, hc⟩
  | @tail w' w'' hw' hstep ih =>
      obtain ⟨d, hd, hcd⟩ := ih
      obtain ⟨e, he, hce⟩ := reflect_step hcd hstep
      exact ⟨e, hd.trans he, hce⟩

theorem normalized_halting_iff (M : FiniteMachine) (input : Input M) :
    (∃ w', Relation.ReflTransGen (Checkpoint.WorkStep M.normalized)
      (M.initialWork input) w' ∧ w'.state = M.normalized.halt) ↔ Halts M input := by
  constructor
  · rintro ⟨w', hw', hhalt⟩
    have hc : Corresponds M (M.initialWork input) (initialConfiguration M input) :=
      ⟨initialWork_represents M input, Or.inl rfl⟩
    obtain ⟨d, hd, _, hs | ⟨_, hterm⟩⟩ := reflect_execution hc hw'
    · simp only [normalized] at hhalt
      rw [hhalt] at hs
      cases hs
    · exact ⟨d, hd, hterm⟩
  · rintro ⟨d, hd, hterm⟩
    obtain ⟨w', hw', hs', ht'⟩ := lift_execution hd (w := M.initialWork input)
      rfl (initialWork_represents M input)
    obtain ⟨hst, hh⟩ := lift_halt hterm hs' ht'
    exact ⟨w'.next M.normalized, hw'.tail hst, hh⟩

theorem discrete_compiled_halting_iff (M : FiniteMachine) (input : Input M) :
    (∃ n d, Exec M.normalized n ((M.initialWork input).expand M.normalized) d ∧
      d.code M.normalized ∈ observer) ↔ Halts M input :=
  (Checkpoint.coded_halting_iff M.normalized (M.initialWork input)).trans
    (normalized_halting_iff M input)

end BalancedTransport.FiniteMachine
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*} {M : Machine Q Γ}

theorem split {n m : ℕ} {c d : Configuration Q Γ} (h : Exec M (n + m) c d) :
    ∃ e, Exec M n c e ∧ Exec M m e d := by
  induction n generalizing c with
  | zero => exact ⟨c, .refl _, by simpa using h⟩
  | succ n ih =>
    have hh : Exec M ((n + m) + 1) c d := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    cases hh with
    | @cons _ _ b _ hcb hbd =>
      obtain ⟨e, hce, hed⟩ := ih hbd
      exact ⟨e, .cons hcb hce, hed⟩

lemma take {m n : ℕ} {c d : Configuration Q Γ} (h : Exec M n c d) (hm : m ≤ n) :
    ∃ e, Exec M m c e := by
  have hh : Exec M (m + (n - m)) c d := by rwa [Nat.add_sub_of_le hm]
  obtain ⟨e, he, _⟩ := hh.split
  exact ⟨e, he⟩

lemma one_iff {c d : Configuration Q Γ} : Exec M 1 c d ↔ Step M c d := by
  constructor
  · intro h
    cases h with
    | cons h h' => cases h'; exact h
  · exact single

lemma snoc {n : ℕ} {c d : Configuration Q Γ} (h : Exec M (n + 1) c d) :
    ∃ e, Exec M n c e ∧ Step M e d := by
  obtain ⟨e, he, hed⟩ := h.split
  exact ⟨e, he, one_iff.mp hed⟩

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*} {M : Machine Q Γ}

theorem arbitrarily_long_execution (M : Machine Q Γ) (c : Checkpoint Q Γ)
    (hh : ¬∃ d, Relation.ReflTransGen (WorkStep M) c d ∧ d.state = M.halt)
    (n : ℕ) : ∃ d, Exec M n (c.expand M) d := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    have hc : c.state ≠ M.halt := fun he => hh ⟨c, .refl, he⟩
    let m := 2 * (c.right.length + 1) + 2
    have hm : 0 < m := by dsimp [m]; omega
    have he : Exec M m (c.expand M) ((c.next M).expand M) := next_exec M c hc
    by_cases hnm : n ≤ m
    · exact he.take hnm
    · have hh' : ¬∃ d, Relation.ReflTransGen (WorkStep M) (c.next M) d ∧ d.state = M.halt := by
        rintro ⟨d, hd, hs⟩
        exact hh ⟨d, (Relation.ReflTransGen.single (show WorkStep M c (c.next M) from
          ⟨hc, rfl⟩)).trans hd, hs⟩
      obtain ⟨d, hd⟩ := ih (n - m) (by omega) (c.next M) hh'
      exact ⟨d, by simpa [Nat.add_sub_of_le (le_of_not_ge hnm)] using he.trans hd⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} {M : Machine Q Γ}
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

lemma Configuration.code_guard {M : Machine Q Γ} {c : Configuration Q Γ}
    (hc : c.control ≠ .ready M.halt) : 4 ≤ c.code M 0 := by
  have hp : (1 : ℝ) ≤ placement M c.control := by
    exact_mod_cast placement_positive M c.control hc
  have hb := (Coding.stream_mem_interior base_pos digit digit_pos digit_upper (c.stacks 0)).1
  change 4 ≤ 4 * (placement M c.control : ℝ) + Coding.stream digit (c.stacks 0)
  linarith

def GuardedTemplate (M : Machine Q Γ) (v : Velocity) : Prop :=
  ∀ r : Row Q Γ, r.valid M → ∀ x,
    x ∈ (r.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
      (fun a => (digit a : ℝ)) (placement M) →
    ∃ γ : ℝ → Space,
      γ 0 = x ∧ γ 1 = (r.instruction M).fullMap M x ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (v t (γ t)) (Set.Icc 0 1) t) ∧
      ((r.instruction M).targetControl ≠ .ready M.halt →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ observer)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set
open scoped NNReal

lemma IsMaterialFlow.shift_unit {U : Velocity} {X : MaterialFlow}
    (hX : IsMaterialFlow U X) (a : Space) {b : ℝ} (hb : 0 ≤ b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => X (s + b) a) (U (t + b) (X (t + b) a)) (Icc 0 1) t := by
  have hd := (hX.2 a (t + b) (add_nonneg ht.1 hb)).scomp t
    ((hasDerivAt_id t).add_const b).hasDerivWithinAt
    (show MapsTo (fun s : ℝ => s + b) (Icc 0 1) (Ici 0) from
      fun s hs => add_nonneg hs.1 hb)
  simpa only [Function.comp_def, one_smul, id_eq] using hd

lemma loadedRepeat_on_later_unit {load v : Velocity}
    (hl : TimeCollars load) (hv : TimeCollars v) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    loadedRepeat load v (t + ((n : ℝ) + 1)) = v t := by
  rw [loadedRepeat_after hl (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) n])]
  have hp := (repeatTemplate_zero_period v).nat_mul (n + 1) t
  simp only [Nat.cast_add, Nat.cast_one, mul_one] at hp
  rw [hp, repeatTemplate_on_unit hv ht]

lemma materialFlow_loading {z : Space} {η : ℝ} (hη : 0 < η)
    {v : Velocity} (hv : TimeCollars v) {X : MaterialFlow}
    (hX : IsMaterialFlow (loadedRepeat (loadingVelocity z η) v) X)
    {L : ℝ≥0}
    (hL : ∀ t, 0 ≤ t → LipschitzWith L (loadingVelocity z η t))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    X t fixedLabel = loadingPath z t := by
  have hd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => X s fixedLabel)
        (loadingVelocity z η s (X s fixedLabel)) (Icc 0 1) s := by
    intro s hs
    have hh := (hX.2 fixedLabel s hs.1).mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from Icc_subset_Ici_self)
    rwa [loadedRepeat_before hv hs.1 hs.2] at hh
  exact curves_agree_on_overlap hL (HasDerivWithinAt.continuousOn hd)
    (HasDerivWithinAt.continuousOn (fun s _ => (loadingPath_hasDerivAt z hη s).hasDerivWithinAt))
    hd (fun s _ => (loadingPath_hasDerivAt z hη s).hasDerivWithinAt)
    ((hX.1 fixedLabel).trans (loadingPath_start z).symm) ht.1 ht.2 ht.2

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q]
variable {M : Machine Q Γ} {v load : Velocity} {X : MaterialFlow} {L : ℝ≥0}

lemma guarded_period_step (hg : GuardedTemplate M v) (hv : TimeCollars v)
    (hl : TimeCollars load)
    (hLip : ∀ t, 0 ≤ t → LipschitzWith L (v t))
    (hX : IsMaterialFlow (loadedRepeat load v) X)
    {c d : Configuration Q Γ} (hcd : Step M c d) (n : ℕ) (a : Space)
    (hstart : X ((n : ℝ) + 1) a = c.code M) :
    X ((n : ℝ) + 2) a = d.code M ∧
      (d.control ≠ .ready M.halt → ∀ t ∈ Icc (0 : ℝ) 1,
        X (t + ((n : ℝ) + 1)) a ∉ observer) := by
  obtain ⟨r, hr, tails, rfl, rfl⟩ := hcd
  obtain ⟨γ, hγ₀, hγ₁, hdγ, hguard⟩ := hg r hr _
    ((r.instruction M).source_code_mem M tails)
  have hdX : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => X (s + ((n : ℝ) + 1)) a)
        (v s (X (s + ((n : ℝ) + 1)) a)) (Icc 0 1) s := by
    intro s hs
    have hh := Geometry.IsMaterialFlow.shift_unit hX a
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity) hs
    rwa [loadedRepeat_on_later_unit hl hv n hs] at hh
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, X (t + ((n : ℝ) + 1)) a = γ t := by
    intro t ht
    exact curves_agree_on_overlap hLip (HasDerivWithinAt.continuousOn hdX)
      (HasDerivWithinAt.continuousOn hdγ) hdX hdγ
      (by simpa only [zero_add] using hstart.trans hγ₀.symm) ht.1 ht.2 ht.2
  constructor
  · have he := (heq 1 ⟨by norm_num, le_rfl⟩).trans
      (hγ₁.trans ((r.instruction M).fullMap_code M tails))
    simpa only [show (1 : ℝ) + ((n : ℝ) + 1) = (n : ℝ) + 2 by ring] using he
  · intro hnh t ht
    rw [heq t ht]
    exact hguard hnh t ht

lemma guarded_execution_endpoint (hg : GuardedTemplate M v) (hv : TimeCollars v)
    (hl : TimeCollars load)
    (hLip : ∀ t, 0 ≤ t → LipschitzWith L (v t))
    (hX : IsMaterialFlow (loadedRepeat load v) X)
    {c d : Configuration Q Γ} {n : ℕ} (h : Exec M n c d) (a : Space)
    (hinit : X 1 a = c.code M) : X ((n : ℝ) + 1) a = d.code M := by
  induction n generalizing d with
  | zero => cases h; simpa using hinit
  | succ n ih =>
      obtain ⟨e, he, hed⟩ := h.snoc
      have hn := guarded_period_step hg hv hl hLip hX hed n a (ih he)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hn.1

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set

lemma TimeCollars.repeats {v : Velocity} (hv : TimeCollars v) : RepeatsAfter 1 v := by
  intro t ht
  rw [hv t (Or.inr (by linarith)), hv (t + 1) (Or.inr (by linarith))]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

theorem loaded_template_halting_iff (M : Machine Q Γ) (c : Checkpoint Q Γ)
    {η : ℝ} (hη : 0 < η) {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hg : GuardedTemplate M v) {X : MaterialFlow}
    (hX : IsMaterialFlow (loadedRepeat (loadingVelocity ((c.expand M).code M) η) v) X) :
    (∃ t : ℝ, 0 ≤ t ∧ X t fixedLabel ∈ observer) ↔
      ∃ d, Relation.ReflTransGen (Checkpoint.WorkStep M) c d ∧ d.state = M.halt := by
  let z := (c.expand M).code M
  have hlc : TimeCollars (loadingVelocity z η) := fun _ ht => loadingVelocity_zero ht
  obtain ⟨L, hLip⟩ := spatial_lipschitz_of_boundedMixed hv
    (boundedMixed_of_compact_repeating hK hv hs hc.repeats)
  obtain ⟨L₀, hLip₀⟩ := spatial_lipschitz_of_boundedMixed (loadingVelocity_jointSmooth z η)
    (loadingVelocity_boundedMixed z hη)
  have hload : ∀ t ∈ Icc (0 : ℝ) 1, X t fixedLabel = loadingPath z t :=
    fun _ ht => materialFlow_loading hη hc hX hLip₀ ht
  have hinit : X 1 fixedLabel = z :=
    (hload 1 ⟨by norm_num, le_rfl⟩).trans (loadingPath_end z)
  have hend {n : ℕ} {d : Configuration Q Γ} (hd : Exec M n (c.expand M) d) :
      X ((n : ℝ) + 1) fixedLabel = d.code M :=
    guarded_execution_endpoint hg hc hlc hLip hX hd fixedLabel hinit
  constructor
  · rintro ⟨t, ht, hobs⟩
    by_contra hn
    have hstate : c.state ≠ M.halt := fun he => hn ⟨c, .refl, he⟩
    by_cases ht₁ : t ≤ 1
    · rw [hload t ⟨ht, ht₁⟩] at hobs
      exact loadingPath_avoids_observer
        (Configuration.code_guard (show (c.expand M).control ≠ .ready M.halt by
          exact fun he => hstate (Control.ready.inj he))) t hobs
    · let n : ℕ := ⌊t - 1⌋₊
      have hnf : (n : ℝ) ≤ t - 1 := Nat.floor_le (by linarith)
      have hnt : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - 1)
      let s := t - ((n : ℝ) + 1)
      have hs' : s ∈ Icc (0 : ℝ) 1 := by dsimp [s]; constructor <;> linarith
      obtain ⟨e, he⟩ := c.arbitrarily_long_execution M hn (n + 1)
      obtain ⟨d, hd, hde⟩ := he.snoc
      have hne : e.control ≠ .ready M.halt := fun hh =>
        hn (Checkpoint.halt_reflection M he hh)
      have hguard := (guarded_period_step hg hc hlc hLip hX hde n fixedLabel (hend hd)).2
        hne s hs'
      have heq : s + ((n : ℝ) + 1) = t := sub_add_cancel _ _
      exact hguard (by rwa [heq])
  · intro hhalt
    obtain ⟨n, d, hd, hh⟩ := (Checkpoint.halting_iff M c).mpr hhalt
    exact ⟨(n : ℝ) + 1, by positivity, by rw [hend hd]; exact (code_mem_observer_iff M d).mpr hh⟩

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open BalancedTransport.Geometry

theorem compiled_continuous_halting_iff (M : FiniteMachine) (w : Input M)
    {η : ℝ} (hη : 0 < η) {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hg : Recorder.GuardedTemplate M.normalized v) {X : MaterialFlow}
    (hX : IsMaterialFlow
      (loadedRepeat (loadingVelocity (((M.initialWork w).expand M.normalized).code M.normalized) η) v) X) :
    (∃ t : ℝ, 0 ≤ t ∧ X t fixedLabel ∈ observer) ↔ Halts M w :=
  (Recorder.loaded_template_halting_iff M.normalized (M.initialWork w) hη hK hv hc hs hg hX).trans
    (normalized_halting_iff M w)

end BalancedTransport.FiniteMachine
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

def solid (A : BoxLayout ι) (i : ι) : Set Space :=
  Icc (A.center i - A.width i) (A.center i + A.width i)

omit [Fintype ι] in
lemma mem_solid {A : BoxLayout ι} {i : ι} {x : Space} : x ∈ A.solid i ↔
    ∀ k, A.center i k - A.width i k ≤ x k ∧ x k ≤ A.center i k + A.width i k := by
  simp only [solid, mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
  exact forall_and.symm

def affineMap (A B : BoxLayout ι) (i : ι) (x : Space) : Space :=
  fun k => B.center i k + B.width i k / A.width i k * (x k - A.center i k)

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

def fieldCenter (m : BoxMotion A B safe η) (i : ι) (t : ℝ) : Space :=
  m.center (2 * t - 1 / 2) i

def fieldScale (m : BoxMotion A B safe η) (i : ι) (t : ℝ) : Space :=
  fun k => m.width (2 * t - 1 / 2) i k / A.width i k

def velocity (m : BoxMotion A B safe η) : Velocity :=
  familyVelocity (fun i => -A.width i) A.width m.fieldCenter m.fieldScale η

def path (m : BoxMotion A B safe η) (i : ι) (x : Space) : ℝ → Space :=
  affinePath (m.fieldCenter i) (m.fieldScale i) (x - A.center i)

lemma fieldCenter_smooth (m : BoxMotion A B safe η) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (m.fieldCenter i) :=
  (contDiff_pi.mp m.smooth_center i).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma fieldScale_smooth (m : BoxMotion A B safe η) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (m.fieldScale i) := by
  apply contDiff_pi.mpr
  intro k
  exact (((contDiff_pi.mp (contDiff_pi.mp m.smooth_width i) k).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))).div_const _

lemma fieldScale_pos (m : BoxMotion A B safe η) (i : ι) (t : ℝ) (k : Fin 3) :
    0 < m.fieldScale i t k := div_pos (m.positive _ _ _) (m.positive_start _ _)

lemma fieldScale_det (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    ∏ k, m.fieldScale i t k = 1 := by
  simp only [fieldScale, Finset.prod_div_distrib, m.volume]
  exact div_self (ne_of_gt (Finset.prod_pos (fun k _ => m.positive_start i k)))

lemma velocity_jointSmooth (m : BoxMotion A B safe η) : JointSmooth m.velocity :=
  familyVelocity_jointSmooth m.fieldCenter_smooth m.fieldScale_smooth
    (fun i t k => (m.fieldScale_pos i t k).ne') _ _ _

lemma velocity_divergence (m : BoxMotion A B safe η) (t : ℝ) (x : Space) :
    div m.velocity t x = 0 :=
  familyVelocity_divergence m.fieldCenter_smooth m.fieldScale_smooth
    (fun i t k => (m.fieldScale_pos i t k).ne') _ _ _ _ _

lemma lowerEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i - m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  field_simp [(m.positive_start i k).ne']
  ring

lemma upperEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i + m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  rw [div_mul_cancel₀ _ (m.positive_start i k).ne']

lemma enlarged_disjoint (m : BoxMotion A B safe η) (t : ℝ) :
    Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t)
        (lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (-A.width j) (m.fieldCenter j) (m.fieldScale j) t)
        (lowerEndpoint (A.width j) (m.fieldCenter j) (m.fieldScale j) t) (2 * η)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rw [m.lowerEndpoint_eq, m.upperEndpoint_eq, mem_closedEnlargement] at hi hj
  obtain ⟨k, hk⟩ := m.separation (2 * t - 1 / 2) i j hij
  have hbound : |m.center (2 * t - 1 / 2) i k - m.center (2 * t - 1 / 2) j k| ≤
      m.width (2 * t - 1 / 2) i k + m.width (2 * t - 1 / 2) j k + 4 * η := by
    apply abs_le.mpr
    have hi' := hi k
    have hj' := hj k
    dsimp at hi' hj'
    constructor <;> linarith
  exact hk.not_ge hbound

lemma path_start (m : BoxMotion A B safe η) (i : ι) (x : Space) : m.path i x 0 = x := by
  ext k
  have hc := m.start_center (-(1 / 2)) (by norm_num)
  have hw := m.start_width (-(1 / 2)) (by norm_num)
  simp only [path, affinePath, fieldCenter, fieldScale, mul_zero, zero_sub, Pi.sub_apply]
  rw [hc, hw, div_self (m.positive_start i k).ne', one_mul]
  ring

lemma path_end (m : BoxMotion A B safe η) (i : ι) (x : Space) :
    m.path i x 1 = A.affineMap B i x := by
  ext k
  change m.center (2 * 1 - 1 / 2) i k +
    m.width (2 * 1 - 1 / 2) i k / A.width i k * (x k - A.center i k) = _
  rw [m.end_center _ (by norm_num), m.end_width _ (by norm_num)]
  rfl

omit [Fintype ι] in
lemma reference_mem {i : ι} {x : Space} (hx : x ∈ A.solid i) :
    x - A.center i ∈ Icc (-A.width i) (A.width i) := by
  rw [BoxLayout.mem_solid] at hx
  constructor <;> intro k <;> dsimp <;> linarith [(hx k).1, (hx k).2]

lemma path_hasDerivAt (m : BoxMotion A B safe η) (hη : 0 < η)
    {i : ι} {x : Space} (hx : x ∈ A.solid i) (t : ℝ) :
    HasDerivAt (m.path i x) (m.velocity t (m.path i x t)) t := by
  have hz := reference_mem hx
  have hplateau := affinePath_mem_plateau (c := m.fieldCenter i) hη hz (m.fieldScale_pos i t)
  unfold path
  rw [velocity, familyVelocity_eq_on_plateau hη i hplateau (m.enlarged_disjoint t)]
  exact affinePath_hasDerivAt hη (m.fieldCenter_smooth i) (m.fieldScale_smooth i)
    (m.fieldScale_pos i) (m.fieldScale_det i) hz t

lemma path_guarded (m : BoxMotion A B safe η) {i : ι} (hi : i ∈ safe)
    {x : Space} (hx : x ∈ A.solid i) (t : ℝ) : m.path i x t ∉ observer := by
  intro hobs
  have hob : m.path i x t 0 < 2 := (Set.mem_pi.mp hobs 0 (Set.mem_univ _)).2
  have hg := m.guard (2 * t - 1 / 2) i hi
  have hz := (reference_mem hx).1 0
  have hp := m.fieldScale_pos i t 0
  have hmul := mul_le_mul_of_nonneg_left hz hp.le
  change m.fieldScale i t 0 * (-A.width i 0) ≤
    m.fieldScale i t 0 * (x - A.center i) 0 at hmul
  have hlow : m.center (2 * t - 1 / 2) i 0 - m.width (2 * t - 1 / 2) i 0 ≤ m.path i x t 0 := by
    have he := congrFun (m.lowerEndpoint_eq i t) 0
    change m.fieldCenter i t 0 + m.fieldScale i t 0 * (-A.width i 0) =
      m.center (2 * t - 1 / 2) i 0 - m.width (2 * t - 1 / 2) i 0 at he
    change _ ≤ m.fieldCenter i t 0 + m.fieldScale i t 0 * (x - A.center i) 0
    rw [← he]
    linarith
  exact (lt_of_lt_of_le hg hlow).not_gt hob

lemma fieldCenter_before (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : t ≤ 1 / 4) :
    m.fieldCenter i t = A.center i := by
  unfold fieldCenter
  rw [m.start_center _ (by linarith)]

lemma fieldScale_before (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : t ≤ 1 / 4) :
    m.fieldScale i t = 1 := by
  ext k
  change m.width (2 * t - 1 / 2) i k / A.width i k = 1
  rw [m.start_width _ (by linarith), div_self (m.positive_start i k).ne']

lemma fieldCenter_after (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : 3 / 4 ≤ t) :
    m.fieldCenter i t = B.center i := by
  unfold fieldCenter
  rw [m.end_center _ (by linarith)]

lemma fieldScale_after (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : 3 / 4 ≤ t) :
    m.fieldScale i t = fun k => B.width i k / A.width i k := by
  unfold fieldScale
  rw [m.end_width _ (by linarith)]

lemma velocity_collars (m : BoxMotion A B safe η) : TimeCollars m.velocity := by
  intro t ht
  apply familyVelocity_zero
  · intro i
    rcases ht with ht | ht
    · have he : m.fieldCenter i =ᶠ[𝓝 t] fun _ => A.center i := by
        filter_upwards [Iio_mem_nhds ht] with s hs using m.fieldCenter_before i hs.le
      rw [he.deriv_eq, deriv_const]
    · have he : m.fieldCenter i =ᶠ[𝓝 t] fun _ => B.center i := by
        filter_upwards [Ioi_mem_nhds ht] with s hs using m.fieldCenter_after i hs.le
      rw [he.deriv_eq, deriv_const]
  · intro i k
    rcases ht with ht | ht
    · have he : (fun s => m.fieldScale i s k) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        rw [m.fieldScale_before i hs.le]
        rfl
      rw [he.deriv_eq, deriv_const]
    · have he : (fun s => m.fieldScale i s k) =ᶠ[𝓝 t] fun _ => B.width i k / A.width i k := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        rw [m.fieldScale_after i hs.le]
      rw [he.deriv_eq, deriv_const]

lemma bounded_geometry (m : BoxMotion A B safe η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t i k,
      |m.center t i k| ≤ C ∧ |m.width t i k| ≤ C := by
  obtain ⟨Cc, hc⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    m.smooth_center.continuous.continuousOn
  obtain ⟨Cw, hw⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    m.smooth_width.continuous.continuousOn
  have hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i k,
      |m.center t i k| ≤ max 0 (max Cc Cw) ∧
      |m.width t i k| ≤ max 0 (max Cc Cw) := by
    intro t ht i k
    constructor
    · exact (norm_le_pi_norm (m.center t i) k).trans
        ((norm_le_pi_norm (m.center t) i).trans ((hc t ht).trans
          ((le_max_left _ _).trans (le_max_right _ _))))
    · exact (norm_le_pi_norm (m.width t i) k).trans
        ((norm_le_pi_norm (m.width t) i).trans ((hw t ht).trans
          ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨max 0 (max Cc Cw), le_max_left _ _, fun t i k => ?_⟩
  by_cases ht : t ≤ 0
  · simpa only [m.start_center t ht, m.start_width t ht,
      m.start_center 0 le_rfl, m.start_width 0 le_rfl] using hh 0 ⟨le_rfl, by norm_num⟩ i k
  · by_cases ht' : 1 ≤ t
    · simpa only [m.end_center t ht', m.end_width t ht',
        m.end_center 1 le_rfl, m.end_width 1 le_rfl] using hh 1 ⟨by norm_num, le_rfl⟩ i k
    · exact hh t ⟨le_of_not_ge ht, le_of_not_ge ht'⟩ i k

lemma velocity_compact_support (m : BoxMotion A B safe η) (hη : 0 < η) :
    ∃ K : Set Space, IsCompact K ∧ SpatiallySupported K m.velocity := by
  obtain ⟨C, hC, hb⟩ := m.bounded_geometry
  let K : Set Space := Icc (fun _ => -(2 * C + 2 * η)) (fun _ => 2 * C + 2 * η)
  refine ⟨K, isCompact_Icc, fun t x hx => image_eq_zero_of_notMem_tsupport ?_⟩
  intro ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp (tsupport_familyVelocity_subset
    (fun i => -A.width i) A.width m.fieldCenter m.fieldScale hη t ht)
  rw [m.lowerEndpoint_eq, m.upperEndpoint_eq, mem_closedEnlargement] at hi
  apply hx
  constructor <;> intro k
  · have hh := hi k
    have hbc := (abs_le.mp (hb (2 * t - 1 / 2) i k).1).1
    have hbw := (abs_le.mp (hb (2 * t - 1 / 2) i k).2).2
    dsimp at hh ⊢
    linarith [hh.1]
  · have hh := hi k
    have hbc := (abs_le.mp (hb (2 * t - 1 / 2) i k).1).2
    have hbw := (abs_le.mp (hb (2 * t - 1 / 2) i k).2).2
    dsimp at hh ⊢
    linarith [hh.2]

end BalancedTransport.Geometry.BoxMotion
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma BoxLayout.lower_mem {A : BoxLayout ι} (hp : A.Positive) (i : ι) :
    A.center i - A.width i ∈ A.solid i := by
  rw [BoxLayout.mem_solid]
  intro k
  exact ⟨le_rfl, by dsimp; linarith [hp i k]⟩

omit [Fintype ι] in
lemma BoxLayout.separated_of_disjoint {A : BoxLayout ι} (hp : A.Positive)
    (hs : Pairwise fun i j => Disjoint (A.solid i) (A.solid j)) : A.Separated 0 := by
  intro i j hij
  by_contra! h
  let x : Space := fun k => max (A.center i k - A.width i k) (A.center j k - A.width j k)
  have hh (k : Fin 3) :
      -(A.width i k + A.width j k) ≤ A.center i k - A.center j k ∧
      A.center i k - A.center j k ≤ A.width i k + A.width j k := by
    have := h k
    simp only [mul_zero, add_zero] at this
    exact abs_le.mp this
  have hi : x ∈ A.solid i := by
    rw [BoxLayout.mem_solid]
    intro k
    refine ⟨le_max_left _ _, max_le ?_ ?_⟩
    · linarith [hp i k]
    · linarith [(hh k).1]
  have hj : x ∈ A.solid j := by
    rw [BoxLayout.mem_solid]
    intro k
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · linarith [(hh k).2]
    · linarith [hp j k]
  exact Set.disjoint_left.mp (hs hij) hi hj

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Coding
open BalancedTransport.Geometry
variable {S ι : Type*}

def layout (r : ℝ) (digit : S → ℝ) (o : ι → Space) (u : ι → Fin 3 → List S) :
    BoxLayout ι where
  center i k := o i k + word r digit (u i k) + r ^ (u i k).length / 2
  width i k := r ^ (u i k).length / 2

lemma layout_positive {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (o : ι → Space) (u : ι → Fin 3 → List S) : (layout r digit o u).Positive := by
  intro i k
  exact div_pos (pow_pos hr _) (by norm_num)

lemma layout_solid [Fintype ι] (r : ℝ) (digit : S → ℝ) (o : ι → Space)
    (u : ι → Fin 3 → List S) (i : ι) :
    (layout r digit o u).solid i = box r digit (o i) (u i) := by
  ext x
  rw [BoxLayout.mem_solid]
  change (∀ k, o i k + word r digit (u i k) + r ^ (u i k).length / 2 -
      r ^ (u i k).length / 2 ≤ x k ∧
      x k ≤ o i k + word r digit (u i k) + r ^ (u i k).length / 2 +
      r ^ (u i k).length / 2) ↔
    ∀ k, word r digit (u i k) ≤ x k - o i k ∧
      x k - o i k ≤ word r digit (u i k) + r ^ (u i k).length
  constructor <;> intro h k <;> have := h k <;> constructor <;> linarith

lemma layout_affineMap {r : ℝ} (hr : r ≠ 0) (digit : S → ℝ) (o p : ι → Space)
    (u v : ι → Fin 3 → List S) (i : ι) (x : Space) :
    (layout r digit o u).affineMap (layout r digit p v) i x =
      boxMap r digit (o i) (p i) (u i) (v i) x := by
  ext k
  dsimp [BoxLayout.affineMap, layout, boxMap, replacement]
  field_simp
  ring

lemma layout_volume (r : ℝ) (digit : S → ℝ) (o p : ι → Space)
    (u v : ι → Fin 3 → List S) (i : ι)
    (h : ∑ k, (u i k).length = ∑ k, (v i k).length) :
    ∏ k, (layout r digit o u).width i k = ∏ k, (layout r digit p v).width i k := by
  simp only [layout, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, h]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
open BalancedTransport.Geometry
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

abbrev ActiveRow (M : Machine Q Γ) := {r : Row Q Γ // r ∈ table M}

def sourceLayout (M : Machine Q Γ) : BoxLayout (ActiveRow M) :=
  Coding.layout (base Q Γ : ℝ)⁻¹ (fun a : Letter Q Γ => (digit a : ℝ))
    (fun i => Coding.origin (placement M (i.val.instruction M).sourceControl))
    (fun i => (i.val.instruction M).sourcePrefixes)

def targetLayout (M : Machine Q Γ) : BoxLayout (ActiveRow M) :=
  Coding.layout (base Q Γ : ℝ)⁻¹ (fun a : Letter Q Γ => (digit a : ℝ))
    (fun i => Coding.origin (placement M (i.val.instruction M).targetControl))
    (fun i => (i.val.instruction M).targetPrefixes)

def safeRows (M : Machine Q Γ) : Set (ActiveRow M) :=
  {i | (i.val.instruction M).targetControl ≠ .ready M.halt}

omit [DecidableEq Γ] in
lemma sourceLayout_solid (M : Machine Q Γ) (i : ActiveRow M) :
    (sourceLayout M).solid i = (i.val.instruction M).sourceBox
      (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) :=
  Coding.layout_solid _ _ _ _ _

omit [DecidableEq Γ] in
lemma targetLayout_solid (M : Machine Q Γ) (i : ActiveRow M) :
    (targetLayout M).solid i = (i.val.instruction M).targetBox
      (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) :=
  Coding.layout_solid _ _ _ _ _

omit [DecidableEq Γ] in
lemma sourceLayout_positive (M : Machine Q Γ) : (sourceLayout M).Positive :=
  Coding.layout_positive inverse_base_pos _ _ _

omit [DecidableEq Γ] in
lemma targetLayout_positive (M : Machine Q Γ) : (targetLayout M).Positive :=
  Coding.layout_positive inverse_base_pos _ _ _

lemma sourceLayout_separated (M : Machine Q Γ) : (sourceLayout M).Separated 0 := by
  apply BoxLayout.separated_of_disjoint (sourceLayout_positive M)
  intro i j hij
  rw [sourceLayout_solid, sourceLayout_solid]
  exact (compiled_boxes_disjoint M).1 i.property j.property (fun h => hij (Subtype.ext h))

lemma targetLayout_separated (M : Machine Q Γ) : (targetLayout M).Separated 0 := by
  apply BoxLayout.separated_of_disjoint (targetLayout_positive M)
  intro i j hij
  rw [targetLayout_solid, targetLayout_solid]
  exact (compiled_boxes_disjoint M).2 i.property j.property (fun h => hij (Subtype.ext h))

omit [DecidableEq Γ] in
lemma layouts_equal_volume (M : Machine Q Γ) (i : ActiveRow M) :
    ∏ k, (sourceLayout M).width i k = ∏ k, (targetLayout M).width i k := by
  apply Coding.layout_volume
  simpa [Instruction.sourcePrefixes, Instruction.targetPrefixes, Fin.sum_univ_succ,
    Instruction.Balanced, Nat.add_assoc] using i.val.balanced M

omit [DecidableEq Γ] in
lemma sourceLayout_guard (M : Machine Q Γ) : (sourceLayout M).Guarded (safeRows M) := by
  intro i _
  have hh := BoxLayout.lower_mem (sourceLayout_positive M) i
  rw [sourceLayout_solid] at hh
  have hn := source_box_guard M i.val ((mem_table M _).mp i.property) hh
  change 2 < (sourceLayout M).center i 0 - (sourceLayout M).width i 0
  change 4 ≤ (sourceLayout M).center i 0 - (sourceLayout M).width i 0 at hn
  linarith

omit [DecidableEq Γ] in
lemma targetLayout_guard (M : Machine Q Γ) : (targetLayout M).Guarded (safeRows M) := by
  intro i hi
  have hh := BoxLayout.lower_mem (targetLayout_positive M) i
  rw [targetLayout_solid] at hh
  have hn := nonhalt_box_guard M _ hi _ hh
  change 2 < (targetLayout M).center i 0 - (targetLayout M).width i 0
  change 4 ≤ (targetLayout M).center i 0 - (targetLayout M).width i 0 at hn
  linarith

omit [DecidableEq Γ] in
lemma layouts_affineMap (M : Machine Q Γ) (i : ActiveRow M) (x : Space) :
    (sourceLayout M).affineMap (targetLayout M) i x = (i.val.instruction M).fullMap M x :=
  Coding.layout_affineMap inverse_base_pos.ne' _ _ _ _ _ _ _

theorem exists_guarded_template (M : Machine Q Γ) :
    ∃ (v : Velocity) (K : Set Space), IsCompact K ∧ JointSmooth v ∧ TimeCollars v ∧
      SpatiallySupported K v ∧ (∀ t x, div v t x = 0) ∧ GuardedTemplate M v := by
  obtain ⟨η, hη, ⟨m⟩⟩ := guarded_solid_box_motion (sourceLayout M) (targetLayout M)
    (safeRows M) (sourceLayout_positive M) (targetLayout_positive M)
    (sourceLayout_separated M) (targetLayout_separated M) (layouts_equal_volume M)
    (sourceLayout_guard M) (targetLayout_guard M)
  obtain ⟨K, hK, hs⟩ := m.velocity_compact_support hη
  refine ⟨m.velocity, K, hK, m.velocity_jointSmooth, m.velocity_collars, hs,
    m.velocity_divergence, ?_⟩
  intro r hr x hx
  let i : ActiveRow M := ⟨r, (mem_table M r).mpr hr⟩
  have hm : x ∈ (sourceLayout M).solid i := by rwa [sourceLayout_solid]
  refine ⟨m.path i x, m.path_start i x, ?_, ?_, ?_⟩
  · rw [m.path_end, layouts_affineMap]
  · intro t _
    exact (m.path_hasDerivAt hη hm t).hasDerivWithinAt
  · intro hsafe t _
    exact m.path_guarded hsafe hm t

end BalancedTransport.Recorder
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma neg {x : ℝ} (h : RationalConstant x) : RationalConstant (-x) := by
  obtain ⟨q,rfl⟩ := h; exact ⟨-q, by simp⟩

lemma inv {x : ℝ} (h : RationalConstant x) : RationalConstant x⁻¹ := by
  obtain ⟨q,rfl⟩ := h; exact ⟨q⁻¹, by simp⟩

lemma div {x y : ℝ} (hx : RationalConstant x) (hy : RationalConstant y) : RationalConstant (x/y) := by
  simpa only [div_eq_mul_inv] using hx.mul hy.inv

lemma pow {x : ℝ} (h : RationalConstant x) (n : ℕ) : RationalConstant (x^n) := by
  obtain ⟨q,rfl⟩ := h; exact ⟨q^n, by simp⟩

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

lemma elementary_motion_velocity {ι : Type*} [Fintype ι] {A B : BoxLayout ι} {safe : Set ι}
    {η : ℝ} (hr : RationalConstant η) (Ar : RationalLayout A) {m : BoxMotion A B safe η}
    (hm : ElementaryMotion m) (d : ℕ) : ElementaryField (fun _ : Fin d → ℝ => m.velocity) := by
  apply ElementaryField.sum Finset.univ
  intro i _
  have ht : ElementaryCurve (fun t : ℝ => 2*t-1/2) := by
    simpa using
      ((ElementaryCurve.const (RationalConstant.nat 2)).mul ElementaryCurve.id).sub
        (ElementaryCurve.const (RationalConstant.rat (1/2)))
  have hc : ElementaryField (fun _ : Fin d → ℝ => fun t _ => m.fieldCenter i t) :=
    fun k => ElementaryScalar.time.curve ((hm.1 i k).comp ht)
  have hw : ElementaryField (fun _ : Fin d → ℝ => fun t _ => m.fieldScale i t) :=
    fun k => (ElementaryScalar.time.curve ((hm.2 i k).comp ht)).div_const (Ar.2 i k)
  apply elementary_movingBoxVelocity (-A.width i) (A.width i)
    (fun k => (Ar.2 i k).neg) (Ar.2 i) hc hw
  · intro k
    obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
      (contDiff_pi.mp (m.fieldScale_smooth i) k).continuous.continuousOn
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (m.fieldScale_pos i t k)
    have hn' : (((n+1:ℕ):ℝ)⁻¹) ≤ m.fieldScale i t k := by simpa [one_div] using hn.le
    refine ⟨n, fun _ s => hn'.trans ?_⟩
    have hh : ∀ s ∈ Icc (0 : ℝ) 1, m.fieldScale i t k ≤ m.fieldScale i s k := hmin
    by_cases hs : s ≤ 1/4
    · simpa only [m.fieldScale_before i hs, m.fieldScale_before i (by norm_num : (0:ℝ) ≤ 1/4),
        Nat.cast_add, Nat.cast_one, one_div] using hh 0 (by simp)
    · by_cases hs' : 3/4 ≤ s
      · simpa only [m.fieldScale_after i hs', m.fieldScale_after i (by norm_num : (3:ℝ)/4 ≤ 1)] using hh 1 (by simp)
      · exact hh s ⟨by linarith,by linarith⟩
  · exact hr

lemma rational_word {S : Type*} {r : ℝ} {digit : S → ℝ} (hr : RationalConstant r)
    (hd : ∀s, RationalConstant (digit s)) (w : List S) : RationalConstant (Coding.word r digit w) := by
  induction w with
  | nil => exact RationalConstant.zero
  | cons a w ih => exact hr.mul ((hd a).add ih)

lemma rational_origin (n : ℕ) : ∀i, RationalConstant (Coding.origin n i) := by
  intro i
  fin_cases i
  · exact (RationalConstant.nat 4).mul (RationalConstant.nat n)
  · exact RationalConstant.zero
  · exact RationalConstant.zero

lemma rational_coding_layout {S ι : Type*} {r : ℝ} {digit : S → ℝ} {o : ι → Space}
    (hr : RationalConstant r) (hd : ∀s, RationalConstant (digit s)) (ho : RationalCenters o)
    (u : ι → Fin 3 → List S) : RationalLayout (Coding.layout r digit o u) := by
  constructor
  · intro i k
    exact ((ho i k).add (rational_word hr hd _)).add ((hr.pow _).div (RationalConstant.nat 2))
  · intro i k
    exact (hr.pow _).div (RationalConstant.nat 2)

lemma rational_sourceLayout {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]
    (M : Recorder.Machine Q Γ) : RationalLayout (Recorder.sourceLayout M) :=
  rational_coding_layout (RationalConstant.nat _).inv (fun _ => RationalConstant.nat _)
    (fun _ => rational_origin _) _

lemma rational_targetLayout {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]
    (M : Recorder.Machine Q Γ) : RationalLayout (Recorder.targetLayout M) :=
  rational_coding_layout (RationalConstant.nat _).inv (fun _ => RationalConstant.nat _)
    (fun _ => rational_origin _) _

theorem exists_elementary_guarded_template {Q Γ : Type*} [Fintype Q] [Fintype Γ]
    [DecidableEq Q] [DecidableEq Γ] (M : Recorder.Machine Q Γ) (d : ℕ) :
    ∃ (v : Velocity) (K : Set Space), IsCompact K ∧ JointSmooth v ∧ TimeCollars v ∧
      SpatiallySupported K v ∧ (∀ t x, div v t x = 0) ∧ Recorder.GuardedTemplate M v ∧
      ElementaryField (fun _ : Fin d → ℝ => v) := by
  obtain ⟨η,hη,m,hm⟩ := elementary_guarded_solid_box_motion (Recorder.sourceLayout M)
    (Recorder.targetLayout M) (Recorder.safeRows M) (rational_sourceLayout M) (rational_targetLayout M)
    (Recorder.sourceLayout_positive M) (Recorder.targetLayout_positive M)
    (Recorder.sourceLayout_separated M) (Recorder.targetLayout_separated M)
    (Recorder.layouts_equal_volume M) (Recorder.sourceLayout_guard M) (Recorder.targetLayout_guard M)
  have hp : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  obtain ⟨K,hK,hs⟩ := m.velocity_compact_support hp
  refine ⟨m.velocity,K,hK,m.velocity_jointSmooth,m.velocity_collars,hs,m.velocity_divergence,?_,
    elementary_motion_velocity (RationalConstant.rat η) (rational_sourceLayout M) hm d⟩
  intro r hr x hx
  let i : Recorder.ActiveRow M := ⟨r, (Recorder.mem_table M r).mpr hr⟩
  have hm : x ∈ (Recorder.sourceLayout M).solid i := by rwa [Recorder.sourceLayout_solid]
  refine ⟨m.path i x,m.path_start i x,?_,?_,?_⟩
  · rw [m.path_end, Recorder.layouts_affineMap]
  · intro t _
    exact (m.path_hasDerivAt hp hm t).hasDerivWithinAt
  · intro hsafe t _
    exact m.path_guarded hsafe hm t

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open _root_.OAI.BalancedTransport.Geometry

def fieldCoordinate (d : ℕ) : Option (Fin 3) → Fin (4+d)
  | none => Fin.castAdd d 0
  | some i => Fin.castAdd d i.succ

def scalarMixedD : MultiIndex → Field ℝ → Field ℝ
  | [], f => f
  | none :: a, f => fullTimeD (scalarMixedD a f)
  | some i :: a, f => spaceD i (scalarMixedD a f)

lemma ElementaryScalar.scalarMixedD {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (a : MultiIndex) :
    ElementaryScalar (fun p => scalarMixedD a (f p)) := by
  induction a with
  | nil => exact hf
  | cons i a ih => cases i with
    | none => exact ih.fullTimeD
    | some i => exact ih.spaceD i

lemma coordinateDerivative_field_time {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (z : Fin (4+d) → ℝ) :
    fderiv ℝ (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z)) z
      (Pi.single (fieldCoordinate d none) 1) =
        fullTimeD (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  have hh := (hf.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp_hasDerivAt (fieldTime z) (fieldArgs_time_hasDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,Geometry.fullTimeD,
    fieldCoordinate] using he.deriv.symm

lemma fieldArgs_space_single {d : ℕ} (i : Fin 3) :
    (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
      Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
        (fun _ => 0) k) : Space →L[ℝ] (Fin (4+d) → ℝ)) (Pi.single i 1) =
      Pi.single (fieldCoordinate d (some i)) 1 := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · have hn : Fin.castAdd d (0 : Fin 4) ≠ Fin.castAdd d i.succ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
      simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_zero,
        zero_apply, Pi.single_apply, ite_eq_right hn,fieldCoordinate]
    · simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_succ,
        ContinuousLinearMap.proj_apply, Pi.single_apply, Fin.castAdd_inj, Fin.succ_inj,fieldCoordinate]
  · intro j
    have hn : Fin.natAdd 4 j ≠ Fin.castAdd d i.succ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ] at this; omega
    simp only [ContinuousLinearMap.pi_apply, Fin.addCases_right,
      zero_apply, Pi.single_apply, ite_eq_right hn,fieldCoordinate]

lemma coordinateDerivative_field_space {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (z : Fin (4+d) → ℝ) (i : Fin 3) :
    fderiv ℝ (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z)) z
      (Pi.single (fieldCoordinate d (some i)) 1) =
        spaceD i (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  have hh := (hf.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp (fieldSpace z) (fieldArgs_space_hasFDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,spaceD,
    ContinuousLinearMap.comp_apply, fieldArgs_space_single] using congrArg (fun l => l (Pi.single i 1)) he.fderiv.symm

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
open _root_.OAI.BalancedTransport.Geometry

def fieldJet (d : ℕ) : MultiIndex → NumericProgram → NumericProgram
  | [], p => p
  | i :: a, p => (fieldJet d a p).jetStep (fieldCoordinate d i)

lemma fieldJet_fold (d : ℕ) (a : MultiIndex) (p : NumericProgram) :
    fieldJet d a p = a.reverse.foldl (fun q i => q.jetStep (fieldCoordinate d i)) p := by
  induction a with
  | nil => rfl
  | cons i a ih => simp [fieldJet, ih]

lemma computable_fieldCoordinate (d : ℕ) : Computable (fieldCoordinate d) := by
  have h : Primrec (fun i : Option (Fin 3) => (Option.casesOn i 0 (fun j => j.val+1) : ℕ)) :=
    Primrec.option_casesOn Primrec.id (Primrec.const 0)
      (Primrec.succ.comp (Primrec.fin_val.comp Primrec.snd)).to₂
  have hv : Primrec (fun i : Option (Fin 3) => (fieldCoordinate d i).val) :=
    h.of_eq (fun i => by cases i <;> rfl)
  exact (Primrec.fin_val_iff.mp hv).to_comp

lemma computable_fieldJet_step (d : ℕ) :
    Computable (fun z : (MultiIndex × NumericProgram) × (NumericProgram × Option (Fin 3)) =>
      jetStep (fieldCoordinate d z.2.2) z.2.1) := by
  let A := (MultiIndex × NumericProgram) × (NumericProgram × Option (Fin 3))
  have hk : Computable (fun z : A => fieldCoordinate d z.2.2) :=
    (computable_fieldCoordinate d).comp (Computable.snd.comp Computable.snd)
  have hp : Computable (fun z : A => z.2.1) := Computable.fst.comp Computable.snd
  exact Computable.comp
    (f := fun z : Fin (4+d) × NumericProgram => jetStep z.1 z.2)
    (g := fun z : A => (fieldCoordinate d z.2.2, z.2.1))
    (computable_jetStep (d := 4+d)) (hk.pair hp)

lemma computable_fieldJet (d : ℕ) :
    Computable (fun z : MultiIndex × NumericProgram => fieldJet d z.1 z.2) := by
  have hl : Computable (fun z : MultiIndex × NumericProgram => z.1.reverse) :=
    Primrec.list_reverse.to_comp.comp Computable.fst
  have h := computable_foldl hl Computable.snd (computable_fieldJet_step d).to₂
  exact h.of_eq (fun z => (fieldJet_fold d z.1 z.2).symm)

lemma fieldJet_valid (d : ℕ) (a : MultiIndex) (p : NumericProgram) (z : Fin (4+d) → ℝ)
    (hp : p.Valid z) : (fieldJet d a p).Valid z := by
  induction a with
  | nil => exact hp
  | cons i a ih => exact jetStep_valid _ _ ih

lemma fieldJet_real {d : ℕ} {f : (Fin d → ℝ) → Field ℝ} (hf : ElementaryScalar f)
    (p : NumericProgram) (hp : ∀ z : Fin (4+d) → ℝ, p.Valid z)
    (he : ∀z, p.real z = f (fieldParam z) (fieldTime z) (fieldSpace z)) (a : MultiIndex) :
    ∀ z : Fin (4+d) → ℝ, (fieldJet d a p).real z =
      scalarMixedD a (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  induction a with
  | nil => exact he
  | cons i a ih =>
    intro z
    rw [fieldJet, jetStep_real _ _ _ (fieldJet_valid d a p z (hp z)), funext ih]
    cases i with
    | none => exact coordinateDerivative_field_time (hf.scalarMixedD a) z
    | some i => exact coordinateDerivative_field_space (hf.scalarMixedD a) z i

end BalancedTransport.Effectivity.NumericProgram
end

noncomputable section
namespace BalancedTransport.Effectivity
open _root_.OAI.BalancedTransport.Geometry

lemma scalarMixedD_component {v : Velocity} (hv : JointSmooth v) (a : MultiIndex) (i : Fin 3) :
    scalarMixedD a (fun t x => v t x i) = fun t x => fullMixedD a v t x i := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    cases j with
    | none =>
      simp only [scalarMixedD, ih, fullMixedD, fullTimeD]
      ext t x
      exact ((hasDerivAt_pi.mp
        (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t).hasDerivAt) i).deriv
    | some j =>
      simp only [scalarMixedD, ih, fullMixedD, spaceD]
      ext t x
      have he := (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x
        (((hv.fullMixedD a).slice t).differentiable (by simp) x).hasFDerivAt
      exact congrArg (fun l => l (Pi.single j 1)) he.fderiv

theorem elementary_jet_programs {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) (hs : ∀p, JointSmooth (v p)) :
    ∃ ps : Fin 3 → NumericProgram,
      ∀ i a z, (NumericProgram.fieldJet d a (ps i)).Valid (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z)) ∧
        (NumericProgram.fieldJet d a (ps i)).real z =
          fullMixedD a (v (fieldParam z)) (fieldTime z) (fieldSpace z) i := by
  choose ps hne hclosed hp he using (fun i => hv i)
  refine ⟨ps, ?_⟩
  intro i a z
  refine ⟨NumericProgram.fieldJet_valid d a (ps i) _ (hp i _), ?_⟩
  rw [NumericProgram.fieldJet_real (hv i) (ps i) (hp i) (fun z => congrFun (he i) z)]
  exact congrFun (congrFun (scalarMixedD_component (hs (fieldParam z)) a i) (fieldTime z)) (fieldSpace z)

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Filter Set
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma timeGerm_fullTimeD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    fullTimeD v =ᶠ[𝓝 t] fullTimeD w := by
  filter_upwards [h.eventually_nhds] with s hs
  funext x
  have he : (fun r => v r x) =ᶠ[𝓝 s] (fun r => w r x) := hs.mono (fun _ he => congrFun he x)
  exact he.deriv_eq

lemma timeGerm_spaceD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) (i : Fin 3) :
    spaceD i v =ᶠ[𝓝 t] spaceD i w := by
  filter_upwards [h] with s hs
  funext x
  change fderiv ℝ (v s) x _ = fderiv ℝ (w s) x _
  rw [hs]

lemma timeGerm_fullMixedD {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) (a : MultiIndex) :
    fullMixedD a v =ᶠ[𝓝 t] fullMixedD a w := by
  induction a with
  | nil => exact h
  | cons i a ih => cases i with
    | none => exact timeGerm_fullTimeD ih
    | some i => exact timeGerm_spaceD ih i

lemma timeGerm_fullInertial {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    fullInertial v =ᶠ[𝓝 t] fullInertial w := by
  have hd : ∀ᶠ s in 𝓝 t, ∀ i : Fin 3, spaceD i v s = spaceD i w s :=
    (Filter.eventually_all).mpr (fun i => timeGerm_spaceD h i)
  filter_upwards [h, timeGerm_fullTimeD h, hd] with s hs ht hd
  funext x
  change fullTimeD v s x + BalancedTransport.convection v s x = fullTimeD w s x + BalancedTransport.convection w s x
  simp only [BalancedTransport.convection, hs, ht, hd]

lemma timeGerm_viscous {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    viscousCoefficient v =ᶠ[𝓝 t] viscousCoefficient w := by
  have hd : ∀ᶠ s in 𝓝 t, ∀ i : Fin 3, spaceD i (spaceD i v) s = spaceD i (spaceD i w) s :=
    (Filter.eventually_all).mpr (fun i => timeGerm_spaceD (timeGerm_spaceD h i) i)
  filter_upwards [hd] with s hd
  funext x
  change -(∑ i, spaceD i (spaceD i v) s x) = -(∑ i, spaceD i (spaceD i w) s x)
  simp only [hd]

lemma fullTimeD_translate (v : Field F) (b : ℝ) :
    fullTimeD (fun t => v (t-b)) = fun t => fullTimeD v (t-b) := by
  funext t x
  exact deriv_comp_sub_const (fun s => v s x) b t

lemma fullMixedD_translate (v : Velocity) (a : MultiIndex) (b : ℝ) :
    fullMixedD a (fun t => v (t-b)) = fun t => fullMixedD a v (t-b) := by
  induction a with
  | nil => rfl
  | cons i a ih => cases i with
    | none => simp only [fullMixedD, ih, fullTimeD_translate]
    | some i => simp only [fullMixedD, ih]; rfl

lemma fullInertial_translate (v : Velocity) (b : ℝ) :
    fullInertial (fun t => v (t-b)) = fun t => fullInertial v (t-b) := by
  ext t x i
  simp only [fullInertial, fullTimeD_translate, convection, spaceD]

lemma viscous_translate (v : Velocity) (b : ℝ) :
    viscousCoefficient (fun t => v (t-b)) = fun t => viscousCoefficient v (t-b) := rfl

lemma loadedRepeat_before_open {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht : t < 5/4) : loadedRepeat load v t = load t := by
  by_cases hh : t ≤ 3/4
  · have he : afterLoadingGate t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    ext x i
    simp [loadedRepeat, he]
  · have he : repeatTemplate v t = 0 := by
      ext x i
      rw [repeatTemplate_eq hc (n := 0) (by simp only [Int.cast_zero, sub_zero]; constructor <;> linarith),
        Int.cast_zero, sub_zero, hc t (Or.inr (lt_of_not_ge hh))]
    ext x i
    simp [loadedRepeat, he]

lemma loadedRepeat_after_open {load v : Velocity} (hl : TimeCollars load) (hc : TimeCollars v)
    {t : ℝ} (ht : 3/4 < t) : loadedRepeat load v t = repeatTemplate v t := by
  by_cases hh : 1 ≤ t
  · exact loadedRepeat_after hl hh
  · have he : repeatTemplate v t = 0 := by
      ext x i
      rw [repeatTemplate_eq hc (n := 0) (by simp only [Int.cast_zero, sub_zero]; constructor <;> linarith),
        Int.cast_zero, sub_zero, hc t (Or.inr ht)]
    ext x i
    simp [loadedRepeat, he, hl t (Or.inr ht)]

lemma loadedRepeat_germ_before {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht : t < 1) : loadedRepeat load v =ᶠ[𝓝 t] load := by
  filter_upwards [eventually_lt_nhds (show t < 5/4 by linarith)] with s hs
  exact loadedRepeat_before_open hc hs

lemma loadedRepeat_germ_after {load v : Velocity} (hl : TimeCollars load) (hc : TimeCollars v)
    {t : ℝ} (ht : 1 ≤ t) :
    loadedRepeat load v =ᶠ[𝓝 t] (fun s => v (s-(⌊t⌋ : ℤ))) := by
  have hi : t - (⌊t⌋ : ℤ) ∈ Ioo (-1/4 : ℝ) (5/4) := by
    have := Int.floor_le t
    have := Int.lt_floor_add_one t
    constructor <;> linarith
  have hn : ∀ᶠ s : ℝ in 𝓝 t, s - (⌊t⌋ : ℤ) ∈ Ioo (-1/4 : ℝ) (5/4) :=
    (continuous_id.sub continuous_const).continuousAt.eventually (isOpen_Ioo.mem_nhds hi)
  filter_upwards [hn, eventually_gt_nhds (show (3 : ℝ)/4 < t by linarith)] with s hs hst
  rw [loadedRepeat_after_open hl hc hst]
  exact funext (repeatTemplate_eq hc hs)

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma ElementaryField.convection {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => convection (v p)) := by
  intro k
  simp only [BalancedTransport.convection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply ElementaryScalar.sum Finset.univ
  intro i _
  exact (hv i).mul ((hv.spaceD i) k)

lemma ElementaryField.fullInertial {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => fullInertial (v p)) :=
  fun i => ((hv.fullTimeD) i).add (hv.convection i)

lemma ElementaryField.viscous {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => viscousCoefficient (v p)) := by
  intro k
  simp only [viscousCoefficient, laplacian, Pi.neg_apply, Finset.sum_apply]
  apply ElementaryScalar.neg
  apply ElementaryScalar.sum Finset.univ
  intro i _
  exact ((hv.spaceD i).spaceD i) k

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma computable_fin_lam {α β : Type*} [Primcodable α] [Primcodable β]
    {n : ℕ} {f : α → Fin n → β} (hf : ∀ i, Computable (fun a => f a i)) :
    Computable f := by
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hf)).of_eq
    (fun a => by funext i; simp)

def rationalNatFloor (q : ℚ) : ℕ := q.num.toNat / q.den

lemma computable_rationalNatFloor : Computable rationalNatFloor :=
  Primrec.nat_div.to_comp.comp (primrec_int_toNat.to_comp.comp computable_rat_num)
    computable_rat_den

lemma rationalNatFloor_eq {q : ℚ} (hq : 0 ≤ q) : rationalNatFloor q = ⌊q⌋₊ := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have he : ((q.num.toNat : ℕ) : ℚ) / (q.den : ℚ) = q := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Rat.num_div_den]
  conv_rhs => rw [← he, Rat.natFloor_natCast_div_natCast]
  rfl

lemma rationalNatFloor_cast {q : ℚ} (hq : 0 ≤ q) :
    (rationalNatFloor q : ℝ) = (⌊(q : ℝ)⌋ : ℤ) := by
  rw [Rat.floor_cast, rationalNatFloor_eq hq, ← Int.natCast_floor_eq_floor hq]
  simp

def rationalPhase (q : ℚ) : ℚ := if q < 1 then q else q - rationalNatFloor q

lemma computable_rationalPhase : Computable rationalPhase := by
  apply computable_ite (computable_rat_lt.comp Computable.id (Computable.const 1)) Computable.id
  exact computable_rat_sub.comp Computable.id
    (computable_rat_natCast.comp computable_rationalNatFloor)

lemma rationalPhase_cast (q : ℚ) (hq : 0 ≤ q) :
    (rationalPhase q : ℝ) = if (q : ℝ) < 1 then (q : ℝ) else (q : ℝ) - (⌊(q : ℝ)⌋ : ℤ) := by
  by_cases h : q < 1
  · have hr : (q : ℝ) < 1 := by exact_mod_cast h
    simp [rationalPhase,h,hr]
  · have hr : ¬ (q : ℝ) < 1 := by exact_mod_cast h
    simp [rationalPhase,h,hr,rationalNatFloor_cast hq]

lemma rationalPhase_bound (q : ℚ) (hq : 0 ≤ q) : |(rationalPhase q : ℝ)| ≤ 1 := by
  rw [rationalPhase_cast q hq]
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast hq)]
    exact h.le
  · have hlo := Int.floor_le (q : ℝ)
    have hhi := Int.lt_floor_add_one (q : ℝ)
    rw [abs_of_nonneg (by linarith)]
    linarith

def fieldRationalArgs {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) :
    Fin (4+d) → ℚ := Fin.addCases (Fin.cases t x) p

lemma fieldRationalArgs_cast {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) :
    (fun i => (fieldRationalArgs p t x i : ℝ)) = fieldArgs (fun i => (p i : ℝ)) t (rationalSpace x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j <;> simp [fieldRationalArgs, fieldArgs, rationalSpace]
  · simp [fieldRationalArgs, fieldArgs]

lemma computable_fieldRationalArgs (d : ℕ) :
    Computable (fun z : (Fin d → ℚ) × RationalPoint => fieldRationalArgs z.1 z.2.1 z.2.2) := by
  apply computable_fin_lam
  intro i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [id_eq,fieldRationalArgs,Fin.addCases_left,Fin.cases_zero] using
        (Computable.fst.comp Computable.snd : Computable (fun z : (Fin d → ℚ) × RationalPoint => z.2.1))
    · simpa only [id_eq,fieldRationalArgs,Fin.addCases_left,Fin.cases_succ] using
        (Computable.fin_app.comp (Computable.snd.comp Computable.snd) (Computable.const l) :
          Computable (fun z : (Fin d → ℚ) × RationalPoint => z.2.2 l))
  · simpa only [id_eq,fieldRationalArgs,Fin.addCases_right] using
      (Computable.fin_app.comp Computable.fst (Computable.const k) :
        Computable (fun z : (Fin d → ℚ) × RationalPoint => z.1 k))

lemma fieldArgs_bound {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) (C S : ℕ)
    (hp : ∀ i, |p i| ≤ C) (ht : |t| ≤ 1) (hx : ∀ i, |x i| ≤ S) :
    ∀ j, |fieldArgs p t x j| ≤ (C+1+S : ℕ) := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · refine Fin.cases ?_ (fun i => ?_) k
    · change |t| ≤ _; push_cast; linarith [Nat.cast_nonneg C (α := ℝ), Nat.cast_nonneg S (α := ℝ)]
    · simp only [fieldArgs,Fin.append_left,Fin.cons_succ]; push_cast; linarith [hx i, Nat.cast_nonneg C (α := ℝ)]
  · simp only [fieldArgs,Fin.append_right]; push_cast; linarith [hp k, Nat.cast_nonneg S (α := ℝ)]

def ElementaryPieces {d : ℕ} (L V : (Fin d → ℝ) → Velocity)
    (κ : ℕ → Fin d → ℚ) (F : Family Velocity) : Prop :=
  ∀ M w t, 0 ≤ t →
    if t < 1 then
      F M w =ᶠ[𝓝 t] L (fun i => (κ (inputCode M w) i : ℝ))
    else F M w =ᶠ[𝓝 t]
      (fun s => V (fun i => (κ (inputCode M w) i : ℝ)) (s - (⌊t⌋ : ℤ)))

lemma ElementaryPieces.jet {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F)
    (M : FiniteMachine) (w : Input M) (a : MultiIndex) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    fullMixedD a (F M w) t x =
      if t < 1 then fullMixedD a (L (fun i => (κ (inputCode M w) i : ℝ))) t x
      else fullMixedD a (V (fun i => (κ (inputCode M w) i : ℝ))) (t - (⌊t⌋ : ℤ)) x := by
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact congrFun (timeGerm_fullMixedD hh a |>.self_of_nhds) x
  · simpa only [fullMixedD_translate] using
      (congrFun (timeGerm_fullMixedD hh a |>.self_of_nhds) x)

lemma computable_sum_nat {α ι : Type*} [Primcodable α] (s : Finset ι)
    {f : ι → α → ℕ} (hf : ∀ i ∈ s, Computable (f i)) :
    Computable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Computable.const (0 : ℕ) : Computable (fun _ : α => 0))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      Primrec.nat_add.to_comp.comp (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

def gridRadius (C : ℕ) (x : Fin 3 → ℚ) : ℕ := C + 1 + ∑ i, (x i).num.natAbs

lemma computable_gridRadius (C : ℕ) : Computable (gridRadius C) := by
  apply Primrec.nat_add.to_comp.comp (Computable.const (C+1))
  apply computable_sum_nat
  intro i _
  exact primrec_int_natAbs.to_comp.comp (computable_rat_num.comp
    (Computable.fin_app.comp Computable.id (Computable.const i)))

lemma gridRadius_bound {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) (C : ℕ)
    (hp : ∀ i, |(p i : ℝ)| ≤ C) (ht : |(t : ℝ)| ≤ 1) :
    ∀ j, |(fieldRationalArgs p t x j : ℝ)| ≤ gridRadius C x := by
  intro j
  rw [congrFun (fieldRationalArgs_cast p t x) j]
  apply fieldArgs_bound _ _ _ C _ hp ht _ j
  intro i
  exact (rat_abs_le_num (x i)).trans (by exact_mod_cast
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((x j).num.natAbs)) (Finset.mem_univ i)))

theorem elementary_jet_evaluators {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) (hs : ∀ p, JointSmooth (v p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C : ℕ)
    (hC : ∀ n i, |(κ n i : ℝ)| ≤ C) :
    ∃ E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ,
    ∃ b : MultiIndex × ℕ → ℕ,
      Computable E ∧ Computable b ∧
      (∀ m a z n, |(z.1 : ℝ)| ≤ 1 → ∀ i,
        |(E (m,a,z,n) i : ℝ) - fullMixedD a (v (fun j => (κ m j : ℝ)))
          z.1 (rationalSpace z.2) i| ≤ error n) ∧
      (∀ m a t x (S : ℕ), |t| ≤ 1 → ‖x‖ ≤ (S : ℝ) →
        ‖fullMixedD a (v (fun j => (κ m j : ℝ))) t x‖ ≤ (b (a,S) : ℝ)) := by
  obtain ⟨ps,hps⟩ := elementary_jet_programs hv hs
  let E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ := fun z i =>
    (NumericProgram.fieldJet d z.2.1 (ps i)).approximation (gridRadius C z.2.2.1.2)
      (fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2) z.2.2.2
  let b : MultiIndex × ℕ → ℕ := fun z =>
    ∑ i, ((NumericProgram.fieldJet d z.1 (ps i)).bound (C+1+z.2)).1
  have hE : Computable E := by
    apply computable_fin_lam
    intro i
    let A := ℕ × MultiIndex × RationalPoint × ℕ
    have hp : Computable (fun z : A => NumericProgram.fieldJet d z.2.1 (ps i)) :=
      (NumericProgram.computable_fieldJet d).comp
        ((Computable.fst.comp Computable.snd).pair (Computable.const (ps i)))
    have hc : Computable (fun z : A => gridRadius C z.2.2.1.2) :=
      (computable_gridRadius C).comp (Computable.snd.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hx : Computable (fun z : A => fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2) :=
      Computable.comp (f := fun z : (Fin d → ℚ) × RationalPoint => fieldRationalArgs z.1 z.2.1 z.2.2)
        (g := fun z : A => (κ z.1,z.2.2.1)) (computable_fieldRationalArgs d)
        ((hκ.comp Computable.fst).pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hn : Computable (fun z : A => z.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    exact Computable.comp
      (f := fun z : NumericProgram × ℕ × (Fin (4+d) → ℚ) × ℕ =>
        z.1.approximation z.2.1 z.2.2.1 z.2.2.2)
      (g := fun z : A => (NumericProgram.fieldJet d z.2.1 (ps i), gridRadius C z.2.2.1.2,
        fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2, z.2.2.2))
      (NumericProgram.computable_approximation (4+d)) (hp.pair (hc.pair (hx.pair hn)))
  have hb : Computable b := by
    apply computable_sum_nat
    intro i _
    have hp : Computable (fun z : MultiIndex × ℕ => NumericProgram.fieldJet d z.1 (ps i)) :=
      (NumericProgram.computable_fieldJet d).comp
        (Computable.fst.pair (Computable.const (ps i)))
    have hc : Computable (fun z : MultiIndex × ℕ => C+1+z.2) :=
      Primrec.nat_add.to_comp.comp (Computable.const (C+1)) Computable.snd
    exact Computable.fst.comp (NumericProgram.computable_bound.comp hp hc)
  refine ⟨E,b,hE,hb,?_,?_⟩
  · intro m a z n ht i
    have hh := hps i a (fieldArgs (fun j => (κ m j : ℝ)) z.1 (rationalSpace z.2))
    simp only [fieldParam_args,fieldTime_args,fieldSpace_args] at hh
    have he := (NumericProgram.fieldJet d a (ps i)).approximation_spec (gridRadius C z.2)
      (fieldRationalArgs (κ m) z.1 z.2) n (gridRadius_bound _ _ _ C (hC m) ht)
      (by rw [fieldRationalArgs_cast]; exact hh.1)
    rw [fieldRationalArgs_cast, hh.2] at he
    exact he
  · intro m a t x S ht hx
    apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg (b (a,S)))).mpr
    intro i
    rw [Real.norm_eq_abs]
    have hh := hps i a (fieldArgs (fun j => (κ m j : ℝ)) t x)
    simp only [fieldParam_args,fieldTime_args,fieldSpace_args] at hh
    have hi : ∀ i, |x i| ≤ S := fun i =>
      (le_trans (norm_le_pi_norm x i) hx)
    have he := (NumericProgram.fieldJet d a (ps i)).magnitude (C+1+S)
      (fieldArgs (fun j => (κ m j : ℝ)) t x)
      (fieldArgs_bound _ _ _ C S (hC m) ht hi) hh.1
    rw [hh.2] at he
    exact he.trans (by exact_mod_cast
      (Finset.single_le_sum (fun j _ => Nat.zero_le
        ((NumericProgram.fieldJet d a (ps j)).bound (C+1+S)).1) (Finset.mem_univ i)))

theorem effectiveFamily_of_elementary_pieces {d : ℕ}
    {L V : (Fin d → ℝ) → Velocity} (hL : ElementaryField L) (hV : ElementaryField V)
    (hsL : ∀p, JointSmooth (L p)) (hsV : ∀p, JointSmooth (V p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C R : ℕ)
    (hC : ∀n i, |(κ n i : ℝ)| ≤ C) {F : Family Velocity}
    (hF : ∀M w, JointSmooth (F M w))
    (hS : ∀M w, SpatiallySupported (Metric.closedBall (0 : Space) R) (F M w))
    (hp : ElementaryPieces L V κ F) : EffectiveFamily F := by
  obtain ⟨EL,bL,hEL,hbL,heL,hmL⟩ := elementary_jet_evaluators hL hsL hκ C hC
  obtain ⟨EV,bV,hEV,hbV,heV,hmV⟩ := elementary_jet_evaluators hV hsV hκ C hC
  let phaseInput : (ℕ × MultiIndex × RationalPoint × ℕ) →
      (ℕ × MultiIndex × RationalPoint × ℕ) :=
    fun z => (z.1,z.2.1,(rationalPhase z.2.2.1.1,z.2.2.1.2),z.2.2.2)
  have hc : Computable phaseInput := by
    dsimp only [phaseInput]
    exact Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (((computable_rationalPhase.comp (Computable.fst.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))).pair
        (Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))).pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  let E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ :=
    fun z => if z.2.2.1.1 < 1 then EL (phaseInput z) else EV (phaseInput z)
  have hE : Computable E :=
    computable_ite (computable_rat_lt.comp (Computable.fst.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd))) (Computable.const 1))
      (hEL.comp hc) (hEV.comp hc)
  let b : ℕ × MultiIndex → ℕ := fun z => bL (z.2,R) + bV (z.2,R)
  have hb : Computable b := Primrec.nat_add.to_comp.comp
    (hbL.comp (Computable.snd.pair (Computable.const R)))
    (hbV.comp (Computable.snd.pair (Computable.const R)))
  refine ⟨E,b,(fun _ => R),hE,hb,Computable.const R,?_,?_,?_⟩
  · intro M w a z n hz i
    have ht : 0 ≤ (z.1 : ℝ) := by exact_mod_cast hz
    rw [← fullMixedD_eq_mixedD (hF M w) a _ ht _, hp.jet M w a _ ht _]
    dsimp only [E,phaseInput]
    by_cases hz' : z.1 < 1
    · have hr : (z.1 : ℝ) < 1 := by exact_mod_cast hz'
      simp only [ite_eq_left hz',ite_eq_left hr]
      have he := heL (inputCode M w) a (rationalPhase z.1,z.2) n
        (rationalPhase_bound _ hz) i
      simpa only [rationalPhase,ite_eq_left hz'] using he
    · have hr : ¬(z.1 : ℝ) < 1 := by exact_mod_cast hz'
      simp only [ite_eq_right hz',ite_eq_right hr]
      have he := heV (inputCode M w) a (rationalPhase z.1,z.2) n
        (rationalPhase_bound _ hz) i
      simpa only [rationalPhase_cast _ hz,ite_eq_right hr] using he
  · intro M w a t ht x
    rw [← fullMixedD_eq_mixedD (hF M w) a _ ht _]
    by_cases hx : ‖x‖ ≤ (R : ℝ)
    · rw [hp.jet M w a t ht x]
      split_ifs with hlt
      · have he := hmL (inputCode M w) a t x R
          (by rw [abs_of_nonneg ht]; exact hlt.le) hx
        exact he.trans (by dsimp [b]; push_cast; exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      · have hlo := Int.floor_le t
        have hhi := Int.lt_floor_add_one t
        have he := hmV (inputCode M w) a (t-(⌊t⌋ : ℤ)) x R
          (by rw [abs_of_nonneg (by linarith)]; linarith) hx
        exact he.trans (by dsimp [b]; push_cast; exact le_add_of_nonneg_left (Nat.cast_nonneg _))
    · have he := (hS M w).fullMixedD Metric.isClosed_closedBall a t x
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
      rw [he, norm_zero]
      exact Nat.cast_nonneg _
  · intro M w t _ x hx
    exact hS M w t x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Recorder Coding BalancedTransport.Geometry
open scoped Classical

lemma computable_rationalWord {S : Type*} [Primcodable S] [Fintype S] [Inhabited S]
    {B : ℕ} (digit : S → Fin B) : Computable (Coding.rationalWord digit) := by
  have h : Computable (fun w : List S => w.reverse.foldl
      (fun q a => (B : ℚ)⁻¹ * ((digit a : ℚ) + q)) 0) :=
    computable_foldl Primrec.list_reverse.to_comp (Computable.const 0)
      (computable_rat_mul.comp (Computable.const ((B : ℚ)⁻¹))
        (computable_rat_add.comp
          ((Primrec.dom_finite (fun a : S => (digit a : ℚ))).to_comp.comp
            (Computable.snd.comp Computable.snd))
          (Computable.fst.comp Computable.snd))).to₂
  apply h.of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [List.reverse_cons,List.foldl_append,List.foldl_cons,
      List.foldl_nil, Coding.rationalWord] using
      (congrArg (fun q => (B : ℚ)⁻¹ * ((digit a : ℚ) + q)) ih)

lemma computable_rationalTailCode {S : Type*} [Primcodable S] [Fintype S] [Inhabited S]
    {B : ℕ} (digit : S → Fin B) (a : S) :
    Computable (fun w => Coding.rationalTailCode digit w a) :=
  computable_rat_add.comp (computable_rationalWord digit)
    (computable_rat_mul.comp
      (computable_rat_pow.comp (Computable.const ((B : ℚ)⁻¹)) Computable.list_length)
      (Computable.const ((digit a : ℚ) / ((B : ℚ) - 1))))

lemma computable_rationalInitial (N : FiniteMachine) :
    Computable (Recorder.Checkpoint.rationalInitial N.normalized (some N.initial)) := by
  let S := Recorder.Letter (Option (Fin (N.states+1))) (Fin (N.symbols+1))
  let : Primcodable S := Primcodable.ofEquiv (Fin (Fintype.card S)) (Fintype.equivFin S)
  let : Inhabited S := ⟨.boundary⟩
  have hwork : Primrec (fun a : Fin (N.symbols+1) => (Letter.work a : S)) := Primrec.dom_finite _
  have hh : Computable (fun w : Input N => w.headD N.blank) := by
    exact (Primrec.option_getD.comp Primrec.list_head? (Primrec.const N.blank)).to_comp.of_eq
      (fun w => by cases w <;> rfl)
  have hw : Computable (fun w : Input N =>
      (Letter.work (w.headD N.blank) : S) :: (w.tail.map Letter.work ++ [Letter.boundary])) :=
    Primrec.list_cons.to_comp.comp (hwork.to_comp.comp hh)
      (Primrec.list_append.to_comp.comp
        ((Primrec.list_map Primrec.list_tail (hwork.comp Primrec.snd).to₂).to_comp)
        (Computable.const [Letter.boundary]))
  apply computable_fin_lam
  intro i
  fin_cases i
  · exact Computable.const _
  · exact (computable_rationalTailCode (Recorder.digit (Q := Option (Fin (N.states+1)))
      (Γ := Fin (N.symbols+1))) (Letter.work N.blank)).comp hw
  · exact Computable.const _

lemma rationalInitial_bounded (N : FiniteMachine) :
    ∃ C : ℕ, ∀ w : Input N, ∀ i,
      |(Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) w i : ℝ)| ≤ C := by
  let k := Recorder.placement N.normalized (.ready (some N.initial))
  refine ⟨4*k+1, ?_⟩
  intro w i
  have he := congrFun (Recorder.Checkpoint.rationalInitial_cast N.normalized (some N.initial) w) i
  change (Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) w i : ℝ) = _ at he
  rw [he]
  change |Coding.origin k i + Coding.stream Recorder.digit _| ≤ _
  have hh := Coding.stream_mem_unit Recorder.digit
    (((Recorder.Checkpoint.initial N.normalized (some N.initial) w).expand N.normalized).stacks i)
  have ho : 0 ≤ Coding.origin k i ∧ Coding.origin k i ≤ 4*(k : ℝ) := by
    fin_cases i <;> dsimp [Coding.origin] <;> constructor <;>
      first | positivity | exact le_rfl
  rw [abs_of_nonneg (add_nonneg ho.1 hh.1)]
  push_cast
  linarith [hh.2, ho.2]

lemma fixedLabel_bound (i : Fin 3) : |fixedLabel i| ≤ (4 : ℝ) := by
  fin_cases i <;> norm_num [fixedLabel]

lemma loadingSupport_ball {z : Space} {C : ℕ} (hz : ∀i, |z i| ≤ C) :
    loadingSupport z 1 ⊆ Metric.closedBall (0 : Space) (C+6 : ℕ) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have hh := (mem_closedEnlargement _ _ _ x).mp hx i
  have h₀ := (abs_le.mp (fixedLabel_bound i))
  have hz' := abs_le.mp (hz i)
  have hlo : -(C : ℝ)-4 ≤ min (fixedLabel i) (z i) := le_min (by linarith) (by linarith)
  have hhi : max (fixedLabel i) (z i) ≤ (C : ℝ)+4 := max_le (by linarith) (by linarith)
  push_cast
  constructor <;> linarith [hh.1,hh.2]

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma EffectiveFamily.forwardEq {V W : Family Velocity} (hV : EffectiveFamily V)
    (h : ∀M w, ForwardEq (V M w) (W M w)) : EffectiveFamily W := by
  obtain ⟨E,b,R,hE,hb,hR,he,hB,hs⟩ := hV
  refine ⟨E,b,R,hE,hb,hR,?_,?_,?_⟩
  · intro M w a z n hz i
    rw [← (h M w).mixedD a _ (by exact_mod_cast hz)]
    exact he M w a z n hz i
  · intro M w a t ht x
    rw [← (h M w).mixedD a t ht]
    exact hB M w a t ht x
  · intro M w t ht x hx
    rw [← h M w t ht]
    exact hs M w t ht x hx

lemma ElementaryPieces.fullInertial {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F) :
    ElementaryPieces (fun p => fullInertial (L p)) (fun p => fullInertial (V p)) κ
      (fun M w => fullInertial (F M w)) := by
  intro M w t ht
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact timeGerm_fullInertial hh
  · simpa only [fullInertial_translate] using timeGerm_fullInertial hh

lemma ElementaryPieces.viscous {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F) :
    ElementaryPieces (fun p => viscousCoefficient (L p)) (fun p => viscousCoefficient (V p)) κ
      (fun M w => viscousCoefficient (F M w)) := by
  intro M w t ht
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact timeGerm_viscous hh
  · simpa only [viscous_translate] using timeGerm_viscous hh

theorem effective_loaded_family {κ : ℕ → Fin 3 → ℚ} (hκ : Computable κ)
    (C : ℕ) (hC : ∀n i, |(κ n i : ℝ)| ≤ C)
    {v : Velocity} {K : Set Space} (hK : IsCompact K)
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (he : ElementaryField (fun _ : Fin 3 → ℝ => v)) :
    let U : Family Velocity := fun M w =>
      loadedRepeat (loadingVelocity (rationalSpace (κ (inputCode M w))) 1) v
    EffectiveFamily U ∧ EffectiveFamily (fun M w => inertialCoefficient (U M w)) ∧
      EffectiveFamily (fun M w => viscousCoefficient (U M w)) := by
  dsimp only
  let U : Family Velocity := fun M w =>
    loadedRepeat (loadingVelocity (rationalSpace (κ (inputCode M w))) 1) v
  have hU (M : FiniteMachine) (w : Input M) : JointSmooth (U M w) :=
    loadedRepeat_jointSmooth (loadingVelocity_jointSmooth _ _) hv hc
  have hp : ElementaryPieces (fun p : Fin 3 → ℝ => loadingVelocity p 1)
      (fun _ : Fin 3 → ℝ => v) κ U := by
    intro M w t ht
    split_ifs with hlt
    · exact loadedRepeat_germ_before hc hlt
    · exact loadedRepeat_germ_after (fun _ ht => loadingVelocity_zero ht) hc (le_of_not_gt hlt)
  obtain ⟨r,hr⟩ := hK.isBounded.subset_closedBall (0 : Space)
  obtain ⟨n,hn⟩ := exists_nat_ge r
  let R : ℕ := max n (C+6)
  have hS (M : FiniteMachine) (w : Input M) :
      SpatiallySupported (Metric.closedBall (0 : Space) R) (U M w) := by
    intro t x hx
    apply loadedRepeat_support (loadingVelocity_supported _ (by norm_num : (0 : ℝ) < 1)) hs t x
    intro hm
    apply hx
    rcases hm with hm | hm
    · exact Metric.closedBall_subset_closedBall (by exact_mod_cast (Nat.le_max_right n (C+6)))
        (loadingSupport_ball (hC (inputCode M w)) hm)
    · exact Metric.closedBall_subset_closedBall
        (hn.trans (by exact_mod_cast (Nat.le_max_left n (C+6)))) (hr hm)
  have el : ElementaryField (fun p : Fin 3 → ℝ => loadingVelocity p 1) :=
    elementary_loadingVelocity ⟨1, by simp⟩
  have sl := fun p : Fin 3 → ℝ => loadingVelocity_jointSmooth p 1
  have eu := effectiveFamily_of_elementary_pieces el he sl (fun _ => hv) hκ C R hC hU hS hp
  have e₀ := effectiveFamily_of_elementary_pieces el.fullInertial he.fullInertial
    (fun p => (sl p).fullInertial) (fun _ => hv.fullInertial) hκ C R hC
    (fun M w => (hU M w).fullInertial) (fun M w => (hS M w).fullInertial) hp.fullInertial
  have e₁ := effectiveFamily_of_elementary_pieces el.viscous he.viscous
    (fun p => (sl p).viscousCoefficient) (fun _ => hv.viscousCoefficient) hκ C R hC
    (fun M w => (hU M w).viscousCoefficient)
    (fun M w => (hS M w).viscousCoefficient Metric.isClosed_closedBall) hp.viscous
  exact ⟨eu,EffectiveFamily.forwardEq e₀ (fun M w => fullInertial_forwardEq (hU M w)),e₁⟩

end BalancedTransport.Effectivity
end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace BalancedTransport
open BalancedTransport.Geometry

theorem balanced_three_stack_realization_oai :
    ∃ U f₀ f₁ : Family Velocity,
    ∃ X : Family MaterialFlow,
    ∃ repeated : FiniteMachine → Velocity,
      EffectiveFamily U ∧ EffectiveFamily f₀ ∧ EffectiveFamily f₁ ∧
      (∀ M, Function.Periodic (repeated M) 1) ∧
      ∀ (M : FiniteMachine) (w : Input M),
        Smooth (U M w) ∧ Smooth (f₀ M w) ∧ Smooth (f₁ M w) ∧
        f₀ M w = inertialCoefficient (U M w) ∧
        f₁ M w = viscousCoefficient (U M w) ∧
        CommonCompactSupport (U M w) (f₀ M w) (f₁ M w) ∧
        BoundedMixed (U M w) ∧
        PeriodicAfterOne (U M w) ∧
        (∀ t, 1 ≤ t → ∀ x, U M w t x = repeated M t x) ∧
        ComparisonClass (U M w) (fun _ _ => 0) ∧
        IsMaterialFlow (U M w) (X M w) ∧
        ((∃ t : ℝ, 0 ≤ t ∧ X M w t fixedLabel ∈ observer) ↔ Halts M w) ∧
        ∀ ν : ℝ, 0 < ν →
          let f := affineForce (f₀ M w) (f₁ M w) ν
          ZeroDataSolution ν f (U M w) (fun _ _ => 0) ∧
          Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧
          UniqueInComparison ν f (U M w) ∧
          (ComputableReal ν → EffectiveFieldIn ∅ f) ∧
          (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name} f) := by
  obtain ⟨N, δ, hδ, hh⟩ := Universal.exists_universal_machine
  obtain ⟨v, K, hK, hv, hc, hs, hd, hg, he⟩ :=
    Effectivity.exists_elementary_guarded_template N.normalized 3
  let κ : ℕ → Fin 3 → ℚ := fun n =>
    Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) (δ n)
  have hκ : Computable κ := (Effectivity.computable_rationalInitial N).comp hδ
  obtain ⟨C, hC⟩ := Effectivity.rationalInitial_bounded N
  let z : Family Space := fun M w => rationalSpace (κ (inputCode M w))
  let U : Family Velocity := fun M w => loadedRepeat (loadingVelocity (z M w) 1) v
  have hz (M : FiniteMachine) (w : Input M) : z M w =
      ((N.initialWork (δ (inputCode M w))).expand N.normalized).code N.normalized :=
    Recorder.Checkpoint.rationalInitial_cast N.normalized (some N.initial) (δ (inputCode M w))
  have hu (M : FiniteMachine) (w : Input M) :=
    loaded_template_realization (z M w) (by norm_num : (0 : ℝ) < 1) hK hv hc hs hd
  have hlc (M : FiniteMachine) (w : Input M) : TimeCollars (loadingVelocity (z M w) 1) :=
    fun _ ht => loadingVelocity_zero ht
  have hr (M : FiniteMachine) (w : Input M) :=
    prescribed_residual_realization ((loadingSupport_compact (z M w) 1).union hK)
      (hu M w).1 (hu M w).2.1 (loadedRepeat_repeats (hlc M w)) (hu M w).2.2.2.1
      (fun t (_ : 0 ≤ t) x => loadedRepeat_divergence
        (loadingVelocity_jointSmooth (z M w) 1) hv hc
        (loadingVelocity_divergence (z M w) 1) hd t x)
  have ef : EffectiveFamily U ∧
      EffectiveFamily (fun M w => inertialCoefficient (U M w)) ∧
      EffectiveFamily (fun M w => viscousCoefficient (U M w)) :=
    Effectivity.effective_loaded_family hκ C (fun n => hC (δ n)) hK hv hc hs he
  choose X hX using (fun M w => (hu M w).2.2.2.2.2.2.1)
  refine ⟨U, (fun M w => inertialCoefficient (U M w)),
    (fun M w => viscousCoefficient (U M w)), X, (fun _ => repeatTemplate v),
    ef.1, ef.2.1, ef.2.2, (fun _ => repeatTemplate_zero_period v), ?_⟩
  intro M w
  obtain ⟨hsm, hsm₀, hsm₁, hsupp, hb, _, _, hp, hclass, _, hres⟩ := hr M w
  refine ⟨hsm, hsm₀, hsm₁, rfl, rfl, hsupp, hb, hp, ?_, hclass, hX M w, ?_, ?_⟩
  · intro t ht x
    exact congrFun ((hu M w).2.2.2.2.2.1 t ht) x
  · have hx : IsMaterialFlow
        (loadedRepeat (loadingVelocity
          (((N.initialWork (δ (inputCode M w))).expand N.normalized).code N.normalized) 1) v)
        (X M w) := by
      rw [← hz M w]
      exact hX M w
    exact (N.compiled_continuous_halting_iff (δ (inputCode M w))
      (by norm_num : (0 : ℝ) < 1) hK hv hc hs hg hx).trans (hh M w)
  · intro ν hν
    obtain ⟨hsol, hsf, hbf, hpf, huniq⟩ := hres ν hν
    have heff := Effectivity.residual_effective_viscosity (fun M w => (hu M w).1)
      ef.2.1 ef.2.2 M w ν
    exact ⟨hsol, hsf, hbf, hpf, huniq, heff.1, heff.2⟩

end BalancedTransport
end

end OAI
end
end

theorem solution : type_of% @OAI.BalancedTransport.balanced_three_stack_realization_oai := @OAI.BalancedTransport.balanced_three_stack_realization_oai
