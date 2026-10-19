-- Prove2me | solution 1 for OAI.Erdos3.exists_positiveGrid_compression_bound_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:59:19.312973+00:00
-- url     : https://prove2.me/submissions/3470e41e-da53-44bd-80c5-c401010d10dc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B086
import Definitions.Def_OAIE3v2B123
import Definitions.Def_OAIE3v2B198
import Theorems.Thm_OAI_Erdos3_exists_cyclicShiftComparison_positive_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem orderedProductTail_zero {n : ℕ} (x : Fin (n + 1) → ℝ) :
    orderedProductTail x 0 = ∏ j : Fin n, x j.succ := by
  simp [orderedProductTail, Fin.prod_univ_succ]

theorem orderedProductTail_succ {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin n) :
    orderedProductTail x i.succ = orderedProductTail (fun j => x j.succ) i := by
  simp [orderedProductTail, Fin.prod_univ_succ]

theorem orderedProduct_telescope (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    (∏ i, x i) - c ^ n = ∑ i, c ^ i.val * (x i - c) * orderedProductTail x i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, orderedProductTail_zero]
    simp only [Fin.val_zero, pow_zero, one_mul]
    have hsum : (∑ i : Fin n, c ^ i.succ.val * (x i.succ - c) * orderedProductTail x i.succ) =
        c * (∑ i : Fin n, c ^ i.val * (x i.succ - c) * orderedProductTail (fun j => x j.succ) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [orderedProductTail_succ, Fin.val_succ, pow_succ]
      ring
    rw [hsum, ← ih (fun j => x j.succ), pow_succ]
    ring

theorem axisSuffix_update {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (i : Fin n) (a y : G) :
    axisSuffix f (Function.update t i a) i y = axisSuffix f t i y := by
  classical
  unfold axisSuffix orderedProductTail
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, ite_true, Function.update_of_ne (ne_of_gt hij)]
  · simp only [hij, ite_false]

theorem axisProduct_nonneg {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y) (t : Fin n → G) (y : G) :
    0 ≤ axisProduct f t y := Finset.prod_nonneg (fun i _ => hf i _)

theorem axisSuffix_nonneg {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y) (t : Fin n → G) (i : Fin n) (y : G) :
    0 ≤ axisSuffix f t i y := by
  unfold axisSuffix orderedProductTail
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact hf j _
  · exact zero_le_one

theorem axisProduct_le_exp {G : Type*} [Add G] {n : ℕ} {p : ℝ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y ∧ f i y ≤ Real.exp p)
    (t : Fin n → G) (y : G) : axisProduct f t y ≤ Real.exp ((n : ℝ) * p) := by
  calc
    _ ≤ ∏ _i : Fin n, Real.exp p :=
      Finset.prod_le_prod (fun index _ => (hf index _).1) (fun index _ => (hf index _).2)
    _ = _ := by simp [Real.exp_nat_mul]

theorem axisSuffix_le_exp {G : Type*} [Add G] {n : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y ∧ f i y ≤ Real.exp p)
    (t : Fin n → G) (i : Fin n) (y : G) : axisSuffix f t i y ≤ Real.exp ((n : ℝ) * p) := by
  have h1 : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  calc
    _ ≤ ∏ _j : Fin n, Real.exp p := by
      unfold axisSuffix orderedProductTail
      apply Finset.prod_le_prod
      · intro j _
        split_ifs
        · exact (hf j _).1
        · exact zero_le_one
      · intro j _
        split_ifs
        · exact (hf j _).2
        · exact h1
    _ = _ := by simp [Real.exp_nat_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3.NativeModelingNumerics

theorem mul_exp_le_exp {a b c d : ℝ} (hc : c ≤ Real.exp d) (hab : a + d ≤ b) :
    c * Real.exp a ≤ Real.exp b := by
  calc
    _ ≤ Real.exp d * Real.exp a := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (d + a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

theorem translated_shift_error_bound {p B n : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B)
    (hN : Real.exp (B + (8 * p + 8) + 10) ≤ n) :
    Real.exp B * Real.exp (-(B + (8 * p + 8) + 10)) +
      Real.exp (2 * p + 2) * (6 * Real.exp (-(8 * p + 8)) + 3 / n) ≤ Real.exp (-p) := by
  let q := 8 * p + 8
  have hn : 0 < n := (Real.exp_pos _).trans_le hN
  have hqn : Real.exp q ≤ n := (Real.exp_le_exp.mpr (by dsimp [q]; linarith)).trans hN
  have hinv : 1 / n ≤ Real.exp (-q) := by
    apply (div_le_iff₀ hn).mpr
    calc
      1 = Real.exp (-q) * Real.exp q := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left hqn (Real.exp_nonneg _)
  have hfirst : Real.exp B * Real.exp (-(B + q + 10)) ≤ Real.exp (-p - 1) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [q]
    linarith
  have hcut : 6 * Real.exp (-q) + 3 / n ≤ 9 * Real.exp (-q) := by
    have hthree : 3 / n ≤ 3 * Real.exp (-q) := by
      calc
        _ = 3 * (1 / n) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    linarith
  have hsecond : Real.exp (2 * p + 2) * (6 * Real.exp (-q) + 3 / n) ≤ Real.exp (-p - 1) := by
    calc
      _ ≤ Real.exp (2 * p + 2) * (9 * Real.exp (-q)) :=
        mul_le_mul_of_nonneg_left hcut (Real.exp_nonneg _)
      _ = 9 * Real.exp (2 * p + 2 - q) := by rw [Real.exp_sub, Real.exp_neg]; ring
      _ ≤ _ := NativeModelingNumerics.mul_exp_le_exp (d := 9)
        (by linarith [Real.add_one_le_exp (9 : ℝ)]) (by dsimp [q]; linarith)
  have hlast : 2 * Real.exp (-p - 1) ≤ Real.exp (-p) :=
    NativeModelingNumerics.mul_exp_le_exp (d := 1)
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by linarith)
  change Real.exp B * Real.exp (-(B + q + 10)) +
    Real.exp (2 * p + 2) * (6 * Real.exp (-q) + 3 / n) ≤ Real.exp (-p)
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

theorem same_side_of_cut_of_small_displacement {x y c ρ : ℝ}
    (hxy : |x - y| ≤ ρ) (hgap : ρ < |x - c|) : (c ≤ x ↔ c ≤ y) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hxy
  by_cases hcx : c ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hcx)] at hgap
    have hcy : c ≤ y := by linarith
    simp only [hcx, hcy]
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hcx))] at hgap
    have hcy : ¬c ≤ y := by linarith
    simp only [hcx, hcy]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positive_partition_sum_unit_interval {I : Type*} [Fintype I]
    (w c : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) :
    0 ≤ ∑ i, w i * c i ∧ ∑ i, w i * c i ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hc i).1), ?_⟩
  calc
    _ ≤ ∑ i, w i := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hw i) (hc i).2)
    _ = 1 := hsum

theorem positive_partition_approximation_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w c : I → X → ℝ) (T : X → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    (hc : ∀ i x, 0 ≤ c i x ∧ c i x ≤ 1) (hT : ∀ x, 0 ≤ T x ∧ T x ≤ 1)
    (hgood : ∀ x, x ∉ E → |T x - ∑ i, w i x * c i x| ≤ ε) :
    (𝔼 x, |T x - ∑ i, w i x * c i x|) ≤ ε + (E.card : ℝ) / Fintype.card X := by
  have hcap (x : X) : |T x - ∑ i, w i x * c i x| ≤ 1 := by
    have hc' := positive_partition_sum_unit_interval (fun i => w i x) (fun i => c i x)
      (fun i => hw i x) (hsum x) (fun i => hc i x)
    exact abs_le.mpr ⟨by linarith [(hT x).1], by linarith [(hT x).2]⟩
  simpa only [one_mul] using expect_abs_le_of_exceptional_set E _ hε hcap hgood

end Erdos3

end

section

namespace Erdos3

theorem cyclic_wrap_branch_eq_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    (N - h.val ≤ x.val ↔ N - h.val ≤ y.val) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hd := good_circle_observations_control_representatives h x y hρ hx hy hdist
  rw [← sub_div, abs_div, abs_of_pos hN] at hd
  have hdiff : |(x.val : ℝ) - y.val| ≤ (N : ℝ) * ρ := by
    have h := (div_le_iff₀ hN).mp hd
    nlinarith
  have hgap := (outside_cyclicWrapExceptional h x hx).2.2
  have hb := same_side_of_cut_of_small_displacement hdiff hgap
  exact_mod_cast hb

theorem cyclic_representative_difference_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ((h + x).val : ℤ) - ((h + y).val : ℤ) = (x.val : ℤ) - (y.val : ℤ) := by
  have hb := cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hdist
  rw [cyclic_representative_add h x, cyclic_representative_add h y]
  simp only [← hb]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace PositiveCyclicNiltest

universe u

theorem apply_shiftBound {degree N : ℕ} [NeZero N] {p error : ℝ}
    {a J c : ZMod N → ℝ} {E : Finset (ZMod N)}
    (hc : PositiveCyclicNiltest.{u} degree N p c)
    (hbound : CyclicNiltestShiftBound.{u} degree N p error a J E)
    {h : ZMod N} (hh : h ∉ E) :
    (𝔼 n, a n * J (n + h) * c n) ≤ error := by
  rcases hc with ⟨D, hs, T, hT, hTc, heval⟩
  simp_rw [heval]
  exact hbound h hh D hs T hT hTc

end PositiveCyclicNiltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslatedShiftTesting
namespace OAI

universe u

section

namespace Erdos3

theorem exists_cyclic_partition_offsets {I : Type*} {N : ℕ} [NeZero N]
    (A : I → ZMod N → ℝ) (h : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hdiam : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ∃ b : I → ℤ, ∀ i x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
      ((h + x).val : ℤ) = (x.val : ℤ) + b i := by
  classical
  have hlocal (i : I) : ∃ b : ℤ, ∀ x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
      ((h + x).val : ℤ) = (x.val : ℤ) + b := by
    by_cases hex : ∃ y, y ∉ cyclicWrapExceptional h ρ ∧ 0 < A i y
    · obtain ⟨y, hy, hAy⟩ := hex
      refine ⟨((h + y).val : ℤ) - (y.val : ℤ), ?_⟩
      intro x hx hAx
      have he := cyclic_representative_difference_of_good_circle h x y hρ hx hy
        (hdiam i x y hAx hAy)
      linarith
    · exact ⟨0, fun x hx hAx => False.elim (hex ⟨x, hx, hAx⟩)⟩
  choose b hb using hlocal
  exact ⟨b, hb⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_positive_translation_partition {I : Type*} [Fintype I]
    {degree N : ℕ} [NeZero N] {p ρ : ℝ} (hp : 0 ≤ p) (hρ : 0 < ρ)
    (f : ZMod N → ℝ) (hf : PositiveCyclicNiltest.{0} degree N p f)
    (A : I → ZMod N → ℝ) (hA : ∀ i, PositiveCyclicNiltest.{0} degree N p (A i))
    (hsum : ∀ x, ∑ i, A i x = 1)
    (hdiam : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) (h : ZMod N) :
    ∃ U : I → ZMod N → ℝ,
      (∀ i, PositiveCyclicNiltest.{0} degree N
        (productNiltestBudget (raisedNiltestBudget p)) (U i)) ∧
      (∀ x, 0 ≤ ∑ i, U i x ∧ ∑ i, U i x ≤ 1) ∧
      (∀ x, x ∉ cyclicWrapExceptional h ρ → f (h + x) = ∑ i, U i x) ∧
      (𝔼 x, |f (h + x) - ∑ i, U i x|) ≤ 6 * ρ + 3 / N := by
  classical
  have hfunit (x) := hf.unit_interval x
  obtain ⟨b, hb⟩ := exists_cyclic_partition_offsets A h hρ hdiam
  rcases hf with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  let g : I → ZMod N → ℝ := fun i x => (T.eval (fun _ => (x.val : ℤ) + b i)).re
  have hg (i) : PositiveCyclicNiltest.{0} degree N p (g i) := by
    refine .of_test D hs (T.translate (fun _ => Nat.zero_lt_one) (fun _ => b i)) hT hTc ?_
    intro x
    simp only [g, RationalFilteredNilmanifold.Niltest.evalCyclic,
      RationalFilteredNilmanifold.Niltest.eval_translate]
    rfl
  let U : I → ZMod N → ℝ := fun i x => A i x * g i x
  have hgood (x) (hx : x ∉ cyclicWrapExceptional h ρ) : f (h + x) = ∑ i, U i x := by
    have heach (i) : A i x * g i x = A i x * f (h + x) := by
      by_cases hzero : A i x = 0
      · simp only [hzero, zero_mul]
      · have hpos : 0 < A i x := lt_of_le_of_ne ((hA i).unit_interval x).1 (Ne.symm hzero)
        have he : g i x = f (h + x) := by
          rw [heval]
          change (T.eval (fun _ => (x.val : ℤ) + b i)).re =
            (T.eval (fun _ => ((h + x).val : ℤ))).re
          rw [hb i x hx hpos]
        rw [he]
    simp only [U, heach, ← Finset.sum_mul, hsum, one_mul]
  refine ⟨U, fun i => (hA i).mul (hg i) hp, ?_, hgood, ?_⟩
  · intro x
    exact positive_partition_sum_unit_interval (fun i => A i x) (fun i => g i x)
      (fun i => ((hA i).unit_interval x).1) (hsum x) (fun i => (hg i).unit_interval x)
  · have hm := positive_partition_approximation_mean_error (cyclicWrapExceptional h ρ)
      A g (fun x => f (h + x)) (by norm_num : (0 : ℝ) ≤ 0)
      (fun i x => ((hA i).unit_interval x).1) hsum
      (fun i x => (hg i).unit_interval x) (fun x => hfunit (h + x))
      (fun x hx => by
        change |f (h + x) - ∑ i, U i x| ≤ 0
        simp only [← hgood x hx, sub_self, abs_zero, le_refl])
    have hm' : (𝔼 x, |f (h + x) - ∑ i, U i x|) ≤
        ((cyclicWrapExceptional h ρ).card : ℝ) / N := by
      simpa only [U, zero_add, ZMod.card] using hm
    exact hm'.trans (cyclicWrapExceptional_density_le h hρ.le)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem PositiveCyclicNiltest.eq_of_degree_zero {N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} 0 N p f) (x y : ZMod N) :
    f x = f y := by
  rcases hf with ⟨D, hs, T, _, _, heval⟩
  have hz : _ = 0 := Nat.eq_zero_of_le_zero hs
  subst hz
  rw [heval x, heval y]
  exact congrArg Complex.re ((RationalFilteredNilmanifold.Niltest.eval_step_zero D T _).trans
    (RationalFilteredNilmanifold.Niltest.eval_step_zero D T _).symm)

theorem exists_positive_cyclic_translation_approximation (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p ρ : ℝ},
      0 ≤ p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ f : ZMod N → ℝ, PositiveCyclicNiltest.{0} s N p f → ∀ h : ZMod N,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : Fin n → ZMod N → ℝ,
          (∀ i, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (U i)) ∧
          (∀ x, 0 ≤ ∑ i, U i x ∧ ∑ i, U i x ≤ 1) ∧
          (∀ x, x ∉ cyclicWrapExceptional h ρ → f (h + x) = ∑ i, U i x) ∧
          (𝔼 x, |f (h + x) - ∑ i, U i x|) ≤ 6 * ρ + 3 / N := by
  obtain ⟨B, _, hinterval⟩ := exists_interval_circle_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  let R := T + (T + 2) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * T + Q)
  refine ⟨C, hC, ?_⟩
  intro s N _ p ρ hp hρ hρinv f hf h
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hcost : 2 * t + productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by
    simpa [T, X, R, Q, t, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hQ0 : 0 ≤ productNiltestBudget (raisedNiltestBudget t) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hproduct : productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  cases s with
  | zero =>
    refine ⟨1, by norm_num, ?_, fun _ => f, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (ht.trans htC)
    · intro i
      exact hf.mono le_rfl (hpt.trans htC)
    · intro x
      simpa using hf.unit_interval x
    · intro x _
      simpa using hf.eq_of_degree_zero (h + x) x
    · have he (x) : f (h + x) = f x := hf.eq_of_degree_zero _ _
      simpa [he] using (show (0 : ℝ) ≤ 6 * ρ + 3 / N by positivity)
  | succ s =>
    obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ := hinterval N hp hρ hρinv
    obtain ⟨U, hU, hrange, hgood, hmean⟩ := exists_positive_translation_partition ht hρ f
      (hf.mono le_rfl hpt) A (fun i => (hA i).mono (by omega) hBt) hsum hdiam h
    exact ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr (hBt.trans htC)), U,
      fun i => (hU i).mono le_rfl hproduct, hrange, hgood, hmean⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_weighted_sum_approximation_le {X I : Type*} [Fintype X] [Fintype I]
    (w f : X → ℝ) (U : I → X → ℝ) {M delta error : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, |w x| ≤ M) (happrox : (𝔼 x, |f x - ∑ i, U i x|) ≤ delta)
    (hpiece : ∀ i, (𝔼 x, w x * U i x) ≤ error) :
    (𝔼 x, w x * f x) ≤ (Fintype.card I : ℝ) * error + M * delta := by
  have hpoint (x) : w x * f x ≤ (∑ i, w x * U i x) + M * |f x - ∑ i, U i x| := by
    have he : w x * (f x - ∑ i, U i x) ≤ M * |f x - ∑ i, U i x| := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hw x) (abs_nonneg _)
    rw [← Finset.mul_sum]
    nlinarith
  calc
    _ ≤ (𝔼 x, ((∑ i, w x * U i x) + M * |f x - ∑ i, U i x|)) :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = (∑ i, 𝔼 x, w x * U i x) + M * (𝔼 x, |f x - ∑ i, U i x|) := by
      rw [Finset.expect_add_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]
    _ ≤ (Fintype.card I : ℝ) * error + M * delta := by
      apply add_le_add
      · calc
          _ ≤ ∑ _i : I, error := Finset.sum_le_sum (fun i _ => hpiece i)
          _ = _ := by simp
      · exact mul_le_mul_of_nonneg_left happrox hM

theorem exists_translated_shift_testing_bound (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p rho R error M : ℝ},
      0 ≤ p → 0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      (p + C) ^ C ≤ R → 0 ≤ error → 0 ≤ M →
      ∀ (v J : ZMod N → ℝ) (E : Finset (ZMod N)),
      CyclicNiltestShiftBound.{0} s N R error v J E →
      ∀ h ∉ E, (∀ x, |v x * J (x + h)| ≤ M) →
      ∀ f : ZMod N → ℝ, PositiveCyclicNiltest.{0} s N p f → ∀ b : ZMod N,
      (𝔼 x, v x * J (x + h) * f (b + x)) ≤
        Real.exp ((p + C) ^ C) * error + M * (6 * rho + 3 / N) := by
  obtain ⟨C, hC, htranslation⟩ := exists_positive_cyclic_translation_approximation a
  refine ⟨C, hC, ?_⟩
  intro s N _ p rho R error M hp hrho hrhoinv hR herror hM v J E hbound h hh hw f hf b
  obtain ⟨n, _, hn, U, hU, _, _, hmean⟩ := htranslation hp hrho hrhoinv f hf b
  have hpiece (i) : (𝔼 x, (v x * J (x + h)) * U i x) ≤ error :=
    ((hU i).mono le_rfl hR).apply_shiftBound hbound hh
  apply (expect_weighted_sum_approximation_le (fun x => v x * J (x + h))
    (fun x => f (b + x)) U hM hw hmean hpiece).trans
  simpa only [Fintype.card_fin] using add_le_add
    (mul_le_mul_of_nonneg_right hn herror) (le_refl (M * (6 * rho + 3 / N)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ConditionalCoordinateExceptions
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_split_coordinate {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G]
    (i : I) (F : (I → G) → ℝ) :
    (𝔼 t, F t) = 𝔼 z : ({j : I // j ≠ i} → G),
      𝔼 a : G, F ((Equiv.funSplitAt i G).symm (a, z)) := by
  calc
    _ = 𝔼 u : G × ({j : I // j ≠ i} → G), F ((Equiv.funSplitAt i G).symm u) := by
      apply Fintype.expect_equiv (Equiv.funSplitAt i G)
      intro t
      rw [Equiv.symm_apply_apply]
    _ = 𝔼 a : G, 𝔼 z : ({j : I // j ≠ i} → G), F ((Equiv.funSplitAt i G).symm (a, z)) := by
      exact Finset.expect_product' (Finset.univ : Finset G)
        (Finset.univ : Finset ({j : I // j ≠ i} → G))
        (fun a z => F ((Equiv.funSplitAt i G).symm (a, z)))
    _ = _ := Finset.expect_comm _ _ _

theorem expect_neg_membership {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (E : Finset G) :
    (𝔼 a : G, if -a ∈ E then (1 : ℝ) else 0) = (E.card : ℝ) / Fintype.card G := by
  classical
  let e : G ≃ G := ⟨Neg.neg, Neg.neg, neg_neg, neg_neg⟩
  calc
    _ = 𝔼 a : G, if a ∈ E then (1 : ℝ) else 0 := by
      apply Fintype.expect_equiv e
      intro a
      rfl
    _ = _ := by simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem]

theorem conditional_neg_coordinate_bad_mean {I G : Type*}
    [Fintype I] [DecidableEq I] [AddGroup G] [Fintype G] [DecidableEq G]
    (i : I) (E : (I → G) → Finset G) {delta : ℝ}
    (hE : ∀ t, ((E t).card : ℝ) ≤ delta * (Fintype.card G : ℝ))
    (hindependent : ∀ t a, E (Function.update t i a) = E t) :
    (𝔼 t : I → G, if -(t i) ∈ E t then (1 : ℝ) else 0) ≤ delta := by
  classical
  rw [expect_split_coordinate i]
  apply (Finset.expect_le_expect (fun z _ => ?_)).trans_eq (Finset.expect_const Finset.univ_nonempty delta)
  let e := Equiv.funSplitAt i G
  have hupdate (a : G) : Function.update (e.symm (0, z)) i a = e.symm (a, z) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have heq (a : G) : E (e.symm (a, z)) = E (e.symm (0, z)) := by
    rw [← hupdate a]
    exact hindependent _ _
  have hval (a : G) : e.symm (a, z) i = a := by
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  change (𝔼 a : G, if -(e.symm (a, z) i) ∈ E (e.symm (a, z)) then (1 : ℝ) else 0) ≤ delta
  simp_rw [hval, heq]
  rw [expect_neg_membership]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
  exact hE _

theorem finite_union_indicator_mean_le {I X : Type*} [Fintype I] [Fintype X]
    (bad : I → X → Prop) [∀ i, DecidablePred (bad i)] {delta : ℝ}
    (hbad : ∀ i, (𝔼 x, if bad i x then (1 : ℝ) else 0) ≤ delta) :
    (𝔼 x, if ∃ i, bad i x then (1 : ℝ) else 0) ≤ (Fintype.card I : ℝ) * delta := by
  classical
  have hpoint (x : X) : (if ∃ i, bad i x then (1 : ℝ) else 0) ≤
      ∑ i, if bad i x then (1 : ℝ) else 0 := by
    split_ifs with hx
    · obtain ⟨i, hi⟩ := hx
      have h := Finset.single_le_sum (f := fun i => if bad i x then (1 : ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [hi, ite_true] using h
    · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  calc
    _ ≤ 𝔼 x, ∑ i, if bad i x then (1 : ℝ) else 0 := Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ i, 𝔼 x, if bad i x then (1 : ℝ) else 0 := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _i : I, delta := Finset.sum_le_sum (fun i _ => hbad i)
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateExceptionUnion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_coordinate_exception_union {I G : Type*} [Fintype I] [DecidableEq I]
    [AddGroup G] [Fintype G] [DecidableEq G]
    (E : I → (I → G) → Finset G) {delta : ℝ}
    (hE : ∀ i t, ((E i t).card : ℝ) ≤ delta * Fintype.card G)
    (hindependent : ∀ i t a, E i (Function.update t i a) = E i t) :
    ∃ S : Finset (I → G),
      (S.card : ℝ) ≤ (Fintype.card I : ℝ) * delta * Fintype.card (I → G) ∧
      ∀ t, t ∉ S → ∀ i, -(t i) ∉ E i t := by
  classical
  let S : Finset (I → G) := Finset.univ.filter (fun t => ∃ i, -(t i) ∈ E i t)
  have hmean := finite_union_indicator_mean_le (fun i t => -(t i) ∈ E i t)
    (fun i => conditional_neg_coordinate_bad_mean i (E i) (hE i) (hindependent i))
  have hid : (𝔼 t : I → G, if ∃ i, -(t i) ∈ E i t then (1 : ℝ) else 0) =
      (S.card : ℝ) / Fintype.card (I → G) := by
    simp [Fintype.expect_eq_sum_div_card, S]
  rw [hid] at hmean
  refine ⟨S, ?_, ?_⟩
  · exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card (I → G))).mp hmean
  · intro t ht i hi
    exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, hi⟩⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem orderedProduct_normalized_telescope (n : ℕ) (x : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    (∏ i, x i) / c ^ n - 1 =
      ∑ i, (c ^ i.val / c ^ n) * (x i - c) * orderedProductTail x i := by
  calc
    _ = ((∏ i, x i) - c ^ n) / c ^ n := by rw [sub_div, div_self (pow_ne_zero n hc)]
    _ = (∑ i, c ^ i.val * (x i - c) * orderedProductTail x i) / c ^ n := by
      rw [orderedProduct_telescope]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem normalizedAxisProduct_tested_le {G : Type*} [Add G] [Fintype G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (c : ℝ) (hc : 1 ≤ c)
    (T : G → ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hinsert : ∀ i, (𝔼 y, (f i (y + t i) - c) * axisSuffix f t i y * T y) ≤ error) :
    (𝔼 y, (normalizedAxisProduct f t c y - 1) * T y) ≤ (n : ℝ) * error := by
  have hc0 : 0 < c := by linarith
  have hpoint (y) : (normalizedAxisProduct f t c y - 1) * T y =
      ∑ i, (c ^ i.val / c ^ n) * ((f i (y + t i) - c) * axisSuffix f t i y * T y) := by
    rw [normalizedAxisProduct, axisProduct, orderedProduct_normalized_telescope n _ c hc0.ne', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    change (c ^ i.val / c ^ n) * (f i (y + t i) - c) *
      orderedProductTail (fun j => f j (y + t j)) i * T y = _
    unfold axisSuffix
    ring
  calc
    _ = ∑ i, (c ^ i.val / c ^ n) *
        (𝔼 y, (f i (y + t i) - c) * axisSuffix f t i y * T y) := by
      simp only [hpoint, Finset.expect_sum_comm, ← Finset.mul_expect]
    _ ≤ ∑ _i : Fin n, error := by
      apply Finset.sum_le_sum
      intro i _
      have hcoeff0 : 0 ≤ c ^ i.val / c ^ n := div_nonneg (pow_nonneg hc0.le _) (pow_nonneg hc0.le _)
      have hcoeff1 : c ^ i.val / c ^ n ≤ 1 :=
        (div_le_one (pow_pos hc0 n)).mpr (pow_le_pow_right₀ hc (Nat.le_of_lt i.isLt))
      exact (mul_le_mul_of_nonneg_left (hinsert i) hcoeff0).trans
        (mul_le_of_le_one_left herror hcoeff1)
    _ = _ := by simp

theorem normalizedAxisProduct_bounds {G : Type*} [Add G] {n : ℕ} {p c : ℝ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y ∧ f i y ≤ Real.exp p)
    (t : Fin n → G) (hc : 1 ≤ c) (y : G) :
    0 ≤ normalizedAxisProduct f t c y ∧ normalizedAxisProduct f t c y ≤ Real.exp ((n : ℝ) * p) := by
  have hnonneg := axisProduct_nonneg f (fun i y => (hf i y).1) t y
  refine ⟨div_nonneg hnonneg (pow_nonneg (by linarith) _), ?_⟩
  exact (div_le_self hnonneg (one_le_pow₀ hc)).trans (axisProduct_le_exp f hf t y)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

theorem cyclic_difference_norm_bound {N : ℕ} [NeZero N] {p epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) (f g : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) (x : ZMod N) :
    ‖((f x - (1 + epsilon) * g x : ℝ) : ℂ)‖ ≤ Real.exp (p + 2) := by
  have hm0 : 0 ≤ (1 + epsilon) * g x := mul_nonneg (by linarith) (hg x).1
  have hm : (1 + epsilon) * g x ≤ 2 * Real.exp p :=
    (mul_le_mul_of_nonneg_right (by linarith : 1 + epsilon ≤ 2) (hg x).1).trans
      (mul_le_mul_of_nonneg_left (hg x).2 (by norm_num))
  have hnorm : |f x - (1 + epsilon) * g x| ≤ 2 * Real.exp p := by
    rw [abs_le]
    constructor <;> linarith [(hf x).1, (hf x).2, Real.exp_pos p]
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply hnorm.trans
  exact NativeModelingNumerics.mul_exp_le_exp
    (by linarith [Real.add_one_le_exp (2 : ℝ)]) le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cyclicShiftComparison_translated (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p : ℝ}, 2 ≤ p → Odd N →
      Real.exp ((p + 2) ^ C) ≤ N → ∀ f g J : ZMod N → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      (∀ x, 0 ≤ J x ∧ J x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) f g →
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicTranslatedNiltestShiftBound (s - 1) N p (Real.exp (-p))
          (fun x => f x - (1 + epsilon) * g x) J E := by
  obtain ⟨c, hc, hshift⟩ := exists_cyclicShiftComparison_positive_s2 s hs hepsilon hepsilon1
  obtain ⟨D, _, htesting⟩ := exists_translated_shift_testing_bound 1
  let Y : Polynomial ℕ := Polynomial.X
  let Q := 8 * Y + 8
  let B := (Q + Polynomial.C D) ^ D
  let R := B + Q + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((R + 2) ^ c)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hodd hN f g J hf hg hJ hcompare
  let q := 8 * p + 8
  let b₀ := (q + D) ^ D
  let r := b₀ + q + 10
  have hp0 : 0 ≤ p := by linarith
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hb : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := hpq.trans hqr
  have hr : 2 ≤ r := hp.trans hpr
  have hrr : r ≤ (r + 2) ^ c := le_power_budget (by linarith) (by omega)
  have hcost : (r + 2) ^ c ≤ (p + 2) ^ C := by
    simpa [Y, Q, B, R, q, b₀, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hNr : Real.exp ((r + 2) ^ c) ≤ N := (Real.exp_le_exp.mpr hcost).trans hN
  have hcap (v : ZMod N → ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp p) :
      ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp r :=
    fun x => ⟨(hv x).1, (hv x).2.trans (Real.exp_le_exp.mpr hpr)⟩
  obtain ⟨E, hE, hbound⟩ := hshift N r hr hodd hNr f g J (hcap f hf) (hcap g hg) (hcap J hJ)
    (hcompare.mono_budget hcost (Real.exp_le_exp.mpr (neg_le_neg hcost)))
  refine ⟨E, hE.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hpr)) (Nat.cast_nonneg _)), ?_⟩
  intro h hh T hT b
  have hweight (x) : |(f x - (1 + epsilon) * g x) * J (x + h)| ≤ Real.exp (2 * p + 2) := by
    have hd := cyclic_difference_norm_bound hepsilon hepsilon1 f g hf hg x
    rw [Complex.norm_real, Real.norm_eq_abs] at hd
    rw [abs_mul, abs_of_nonneg (hJ (x + h)).1]
    calc
      _ ≤ Real.exp (p + 2) * Real.exp p := mul_le_mul hd (hJ (x + h)).2 (hJ (x + h)).1 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hinv : 1 / Real.exp (-q) ≤ Real.exp ((q + 2) ^ (1 : ℕ)) := by
    rw [Real.exp_neg, one_div, inv_inv, pow_one]
    exact Real.exp_le_exp.mpr (by linarith)
  have htest := htesting hq (Real.exp_pos (-q)) hinv
    (by dsimp [r, b₀]; linarith : (q + D) ^ D ≤ r) (Real.exp_nonneg (-r))
    (Real.exp_nonneg (2 * p + 2)) (fun x => f x - (1 + epsilon) * g x) J E
    hbound h hh hweight T (hT.mono le_rfl hpq) b
  apply htest.trans
  exact translated_shift_error_bound hp hb ((Real.exp_le_exp.mpr hrr).trans hNr)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem exists_axis_compression (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N n : ℕ} [NeZero N] {p r g : ℝ},
      0 ≤ p → 2 ≤ r → p ≤ r → (n : ℝ) * p ≤ r → 1 ≤ g → g ≤ Real.exp r →
      Odd N → Real.exp ((r + 2) ^ C) ≤ N →
      ∀ f : Fin n → ZMod N → ℝ, (∀ i x, 0 ≤ f i x ∧ f i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((r + 2) ^ C)
        (Real.exp (-((r + 2) ^ C))) (f i) (fun _ => g)) →
      ∃ S : Finset (Fin n → ZMod N),
        (S.card : ℝ) ≤ (n : ℝ) * Real.exp (-r) * (N : ℝ) ^ n ∧
        (∀ t y, 0 ≤ normalizedAxisProduct f t ((1 + epsilon) * g) y ∧
          normalizedAxisProduct f t ((1 + epsilon) * g) y ≤ Real.exp ((n : ℝ) * p)) ∧
        ∀ t, t ∉ S → CyclicNiltestUpperComparison.{0} (s - 1) N r
          ((n : ℝ) * Real.exp (-r)) (normalizedAxisProduct f t ((1 + epsilon) * g)) (fun _ => 1) := by
  classical
  obtain ⟨C, hC, hshift⟩ := exists_cyclicShiftComparison_translated s hs hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro N n _ p r g hp hr hpr hnpr hg hgb hodd hN f hf hcompare
  let c := (1 + epsilon) * g
  have hc : 1 ≤ c := by
    dsimp [c]
    calc
      1 ≤ g := hg
      _ = 1 * g := (one_mul g).symm
      _ ≤ (1 + epsilon) * g := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hex (i : Fin n) (t : Fin n → ZMod N) :
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-r) * N ∧
        CyclicTranslatedNiltestShiftBound (s - 1) N r (Real.exp (-r))
          (fun x => f i x - c) (axisSuffix f t i) E := by
    apply hshift N hr hodd hN (f i) (fun _ => g) (axisSuffix f t i)
    · intro x
      exact ⟨(hf i x).1, (hf i x).2.trans (Real.exp_le_exp.mpr hpr)⟩
    · intro x
      exact ⟨by linarith, hgb⟩
    · intro x
      exact ⟨axisSuffix_nonneg f (fun j y => (hf j y).1) t i x,
        (axisSuffix_le_exp hp f hf t i x).trans (Real.exp_le_exp.mpr hnpr)⟩
    · exact hcompare i
  choose E hE hbound using hex
  let A : Fin n → (Fin n → ZMod N) → Finset (ZMod N) :=
    fun i t => E i (Function.update t i 0)
  have hA (i) (t) : ((A i t).card : ℝ) ≤ Real.exp (-r) * Fintype.card (ZMod N) := by
    simpa only [A, ZMod.card] using hE i (Function.update t i 0)
  have hAi (i) (t) (a : ZMod N) : A i (Function.update t i a) = A i t := by
    simp only [A, Function.update_idem]
  obtain ⟨S, hS, hgood⟩ := exists_coordinate_exception_union A hA hAi
  refine ⟨S, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin, Fintype.card_fun, ZMod.card, Nat.cast_pow] using hS
  · intro t y
    exact normalizedAxisProduct_bounds f hf t hc y
  · intro t ht L _ _ degree dim _ _ _ _ D hdegree T hT hTc
    let U : ZMod N → ℝ := fun x => (T.evalCyclic N (fun _ => x)).re
    have hU : PositiveCyclicNiltest.{0} (s - 1) N r U :=
      .of_test D hdegree T hT hTc (fun _ => rfl)
    apply normalizedAxisProduct_tested_le f t c hc U (Real.exp_nonneg (-r))
    intro i
    have hi := hgood t ht i
    have hb := hbound i (Function.update t i 0)
    have hJ : axisSuffix f (Function.update t i 0) i = axisSuffix f t i := by
      funext y
      exact axisSuffix_update f t i 0 y
    rw [hJ] at hb
    have hcorr := hb (-(t i)) hi U hU (-(t i))
    have heq : (𝔼 y, (f i (y + t i) - c) * axisSuffix f t i y * U y) =
        𝔼 x, (f i x - c) * axisSuffix f t i (x + -(t i)) * U (-(t i) + x) := by
      apply Fintype.expect_equiv (Equiv.addRight (t i))
      intro y
      simp [add_assoc, add_comm]
    exact heq.trans_le hcorr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteExceptionalMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_le_of_exceptional_set {X : Type*} [Fintype X] [Nonempty X]
    (E : Finset X) (F : X → ℝ) {A B delta : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : (E.card : ℝ) ≤ delta * Fintype.card X)
    (hbound : ∀ x, F x ≤ B) (hgood : ∀ x, x ∉ E → F x ≤ A) :
    (𝔼 x, F x) ≤ A + B * delta := by
  classical
  have hcard : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hind : (𝔼 x : X, if x ∈ E then (1 : ℝ) else 0) ≤ delta := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact (div_le_iff₀ hcard).mpr hE
  calc
    _ ≤ 𝔼 x, (A + B * (if x ∈ E then (1 : ℝ) else 0)) := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hx : x ∈ E
      · simpa only [if_pos hx, mul_one] using (hbound x).trans (le_add_of_nonneg_left hA)
      · simpa only [if_neg hx, mul_zero, add_zero] using hgood x hx
    _ = A + B * (𝔼 x : X, if x ∈ E then (1 : ℝ) else 0) := by
      rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hind hB)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialAxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_polynomial_axis_compression (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N n : ℕ} [NeZero N] {p L g : ℝ},
      2 ≤ p → 2 ≤ L → (n : ℝ) ≤ p → 1 ≤ g → g ≤ Real.exp p →
      Odd N → Real.exp ((p + L + 2) ^ C) ≤ N →
      ∀ f : Fin n → ZMod N → ℝ, (∀ i x, 0 ≤ f i x ∧ f i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
        (Real.exp (-((p + L + 2) ^ C))) (f i) (fun _ => g)) →
      ∃ S : Finset (Fin n → ZMod N),
        (S.card : ℝ) ≤ Real.exp (-L) * (N : ℝ) ^ n ∧
        (∀ t y, 0 ≤ normalizedAxisProduct f t ((1 + epsilon) * g) y ∧
          normalizedAxisProduct f t ((1 + epsilon) * g) y ≤ Real.exp (p ^ 2)) ∧
        ∀ t, t ∉ S → CyclicNiltestUpperComparison.{0} (s - 1) N L (Real.exp (-L))
          (normalizedAxisProduct f t ((1 + epsilon) * g)) (fun _ => 1) := by
  obtain ⟨c, _, hcompress⟩ := exists_axis_compression s hs hepsilon hepsilon1
  let Y : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (((Y + 2) ^ 2 + 2) ^ c)
  refine ⟨C, hC, ?_⟩
  intro N n _ p L g hp hL hn hg hgb hodd hN f hf hcompare
  let r := (p + L + 2) ^ 2
  have hp0 : 0 ≤ p := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hsum : p + L ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + L)]
  have hpr : p ≤ r := by linarith
  have hLr : L ≤ r := by linarith
  have hp2 : p ^ 2 ≤ r := pow_le_pow_left₀ hp0 (by linarith : p ≤ p + L + 2) 2
  have hnp : (n : ℝ) * p ≤ p ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hn hp0
  have hcost : (r + 2) ^ c ≤ (p + L + 2) ^ C := by
    simpa [Y, r, Polynomial.eval₂_pow] using hbudget (p + L) (by linarith)
  obtain ⟨S, hS, hcap, hgood⟩ := hcompress hp0 (hp.trans hpr) hpr (hnp.trans hp2) hg
    (hgb.trans (Real.exp_le_exp.mpr hpr)) hodd ((Real.exp_le_exp.mpr hcost).trans hN) f hf
    (fun i => CyclicNiltestUpperComparison.mono_budget (hcompare i) hcost
      (Real.exp_le_exp.mpr (neg_le_neg hcost)))
  have hnexp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have herr : (n : ℝ) * Real.exp (-r) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp p * Real.exp (-r) := mul_le_mul_of_nonneg_right hnexp (Real.exp_nonneg _)
      _ = Real.exp (p - r) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  refine ⟨S, hS.trans (mul_le_mul_of_nonneg_right herr (pow_nonneg (Nat.cast_nonneg N) n)), ?_, ?_⟩
  · intro t y
    exact ⟨(hcap t y).1, (hcap t y).2.trans (Real.exp_le_exp.mpr hnp)⟩
  · intro t ht
    exact CyclicNiltestUpperComparison.mono_budget (hgood t ht) hLr herr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SimultaneousAxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_simultaneous_axis_compression (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] {N n : ℕ} [NeZero N] {p L g : ℝ},
      2 ≤ p → 2 ≤ L → (n : ℝ) ≤ p → 1 ≤ g → g ≤ Real.exp p →
      Odd N → Real.exp ((p + L + 2) ^ C) ≤ N →
      ∀ f : I → Fin n → ZMod N → ℝ, (∀ i j x, 0 ≤ f i j x ∧ f i j x ≤ Real.exp p) →
      (∀ i j, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
        (Real.exp (-((p + L + 2) ^ C))) (f i j) (fun _ => g)) →
      ∃ S : Finset (Fin n → ZMod N),
        (S.card : ℝ) ≤ (Fintype.card I : ℝ) * Real.exp (-L) * (N : ℝ) ^ n ∧
        (∀ i t y, 0 ≤ normalizedAxisProduct (f i) t ((1 + epsilon) * g) y ∧
          normalizedAxisProduct (f i) t ((1 + epsilon) * g) y ≤ Real.exp (p ^ 2)) ∧
        ∀ t, t ∉ S → ∀ i, CyclicNiltestUpperComparison.{0} (s - 1) N L (Real.exp (-L))
          (normalizedAxisProduct (f i) t ((1 + epsilon) * g)) (fun _ => 1) := by
  classical
  obtain ⟨C, hC, hcompress⟩ := exists_polynomial_axis_compression s hs hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro I _ N n _ p L g hp hL hn hg hgb hodd hN f hf hcompare
  have hex (i : I) := hcompress hp hL hn hg hgb hodd hN (f i) (hf i) (hcompare i)
  choose S hS hcap hgood using hex
  let E := Finset.univ.biUnion S
  have hsub (i : I) : S i ⊆ E := by
    intro t ht
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ht⟩
  refine ⟨E, ?_, hcap, ?_⟩
  · calc
      (E.card : ℝ) ≤ ∑ i, ((S i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : E.card ≤ ∑ i, (S i).card)
      _ ≤ ∑ _i : I, Real.exp (-L) * (N : ℝ) ^ n := Finset.sum_le_sum (fun i _ => hS i)
      _ = _ := by simp [mul_assoc]
  · intro t ht i
    exact hgood i t (fun hi => ht (hsub i hi))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveGridFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem positiveGridVertex_card {j : ℕ} (a : Fin j → ℕ) :
    Fintype.card (PositiveGridVertex a) = positiveGridVolume a := by
  simp [PositiveGridVertex, positiveGridVolume, Fintype.card_pi]

theorem positiveGridVolume_succ {j : ℕ} (a : Fin (j + 1) → ℕ) :
    positiveGridVolume a = a 0 * positiveGridVolume (fun i => a i.succ) := by
  exact Fin.prod_univ_succ a

theorem positiveGridProduct_le_exp {j : ℕ} (a : Fin j → ℕ) {G : Type*} [AddCommMonoid G]
    {p : ℝ} (f : PositiveGridVertex a → G → ℝ)
    (hf : ∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) (t) :
    positiveGridProduct a f t ≤ Real.exp ((positiveGridVolume a : ℝ) * p) := by
  calc
    _ ≤ ∏ _b : PositiveGridVertex a, Real.exp p :=
      Finset.prod_le_prod (fun b _ => (hf b _).1) (fun b _ => (hf b _).2)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, positiveGridVertex_card, Real.exp_nat_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem prod_dependent_fin_cons {j : ℕ} {X : Fin (j + 1) → Type*} [∀ i, Fintype (X i)]
    {M : Type*} [CommMonoid M] (F : (∀ i, X i) → M) :
    (∏ x, F x) = ∏ y : ∀ i : Fin j, X i.succ, ∏ a : X 0, F (Fin.cons a y) := by
  calc
    _ = ∏ p : X 0 × (∀ i : Fin j, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by rw [Fintype.prod_prod_type, Finset.prod_comm]

theorem positiveGridProduct_cons {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*}
    [AddCommMonoid G] (f : PositiveGridVertex a → G → ℝ) (t : Fin (a 0) → G)
    (u : PositiveGridShifts (fun i => a i.succ) G) {c : ℝ} (hc : c ≠ 0) :
    positiveGridProduct a f (Fin.cons t u) = c ^ positiveGridVolume a *
      positiveGridProduct (fun i => a i.succ) (positiveGridFiber a f t c) u := by
  have heq (b : PositiveGridVertex (fun i => a i.succ)) :
      (∏ i : Fin (a 0), f (Fin.cons i b) (∑ k, (Fin.cons t u : PositiveGridShifts a G) k ((Fin.cons i b : PositiveGridVertex a) k))) =
        c ^ a 0 * positiveGridFiber a f t c b (∑ k, u k (b k)) := by
    simp only [positiveGridFiber, normalizedAxisProduct, axisProduct, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hc)]
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (f (Fin.cons i b)) (add_comm _ _)
  unfold positiveGridProduct
  rw [prod_dependent_fin_cons]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, positiveGridVertex_card]
  rw [← pow_mul, positiveGridVolume_succ]

theorem positiveGridMean_first_axis {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) :
    positiveGridMean a f = 𝔼 t : Fin (a 0) → G,
      𝔼 u : PositiveGridShifts (fun i => a i.succ) G,
        positiveGridProduct a f (Fin.cons t u) := by
  exact expect_dependent_fin_cons (fun t => positiveGridProduct a f t)

theorem positiveGridMean_fiber {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ)
    (t : Fin (a 0) → G) {c : ℝ} (hc : c ≠ 0) :
    (𝔼 u : PositiveGridShifts (fun i => a i.succ) G, positiveGridProduct a f (Fin.cons t u)) =
      c ^ positiveGridVolume a * positiveGridMean (fun i => a i.succ) (positiveGridFiber a f t c) := by
  simp only [positiveGridProduct_cons a f t _ hc, positiveGridMean, Finset.mul_expect]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positiveGrid_compression_bound_s2_oai (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {j N : ℕ} [NeZero N] {p L g A : ℝ},
      2 ≤ p → 2 ≤ L → 1 ≤ g → g ≤ Real.exp p → 0 ≤ A → Odd N →
      Real.exp ((p + L + 2) ^ C) ≤ N →
      ∀ (a : Fin (j + 1) → ℕ), (a 0 : ℝ) ≤ p →
      ∀ f : PositiveGridVertex a → ZMod N → ℝ,
      (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
      (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
        (Real.exp (-((p + L + 2) ^ C))) (f b) (fun _ => g)) →
      (∀ h : PositiveGridVertex (fun i => a i.succ) → ZMod N → ℝ,
        (∀ b x, 0 ≤ h b x ∧ h b x ≤ Real.exp (p ^ 2)) →
        (∀ b, CyclicNiltestUpperComparison.{0} (s - 1) N L (Real.exp (-L)) (h b) (fun _ => 1)) →
        positiveGridMean (fun i => a i.succ) h ≤ A) →
      positiveGridMean a f ≤ ((1 + epsilon) * g) ^ positiveGridVolume a * A +
        Real.exp ((positiveGridVolume a : ℝ) * p) *
          (positiveGridVolume (fun i => a i.succ) : ℝ) * Real.exp (-L) := by
  classical
  obtain ⟨C, hC, hcompress⟩ := exists_simultaneous_axis_compression s hs hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro j N _ p L g A hp hL hg hgb hA hodd hN a ha f hf hcompare htail
  let c := (1 + epsilon) * g
  have hc : 0 < c := mul_pos (by linarith) (by linarith)
  obtain ⟨S, hS, hcap, hgood⟩ := hcompress hp hL ha hg hgb hodd hN
    (fun b i => f (Fin.cons i b)) (fun b i => hf (Fin.cons i b))
    (fun b i => hcompare (Fin.cons i b))
  have hSc : (S.card : ℝ) ≤
      ((positiveGridVolume (fun i => a i.succ) : ℝ) * Real.exp (-L)) *
        Fintype.card (Fin (a 0) → ZMod N) := by
    simpa only [positiveGridVertex_card, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      Nat.cast_pow] using hS
  let F : (Fin (a 0) → ZMod N) → ℝ := fun t =>
    𝔼 u : PositiveGridShifts (fun i => a i.succ) (ZMod N), positiveGridProduct a f (Fin.cons t u)
  have hbound (t) : F t ≤ Real.exp ((positiveGridVolume a : ℝ) * p) := by
    exact (Finset.expect_le_expect (fun u _ => positiveGridProduct_le_exp a f hf _)).trans_eq
      (Fintype.expect_const _)
  have hgoodF (t) (ht : t ∉ S) : F t ≤ c ^ positiveGridVolume a * A := by
    dsimp only [F]
    rw [positiveGridMean_fiber a f t hc.ne']
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc.le _)
    apply htail
    · exact fun b x => hcap b t x
    · exact hgood t ht
  rw [positiveGridMean_first_axis]
  have hresult := expect_le_of_exceptional_set S F (mul_nonneg (pow_nonneg hc.le _) hA)
    (Real.exp_nonneg _) hSc hbound hgoodF
  simpa only [F, c, mul_assoc] using hresult

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_positiveGrid_compression_bound_s2_oai := @OAI.Erdos3.exists_positiveGrid_compression_bound_s2_oai
