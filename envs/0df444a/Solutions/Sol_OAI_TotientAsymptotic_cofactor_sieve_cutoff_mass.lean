-- Prove2me | solution 1 for OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:33:00.590969+00:00
-- url     : https://prove2.me/submissions/562ed18b-88e3-459e-a475-ced50ba91993

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_AuxResults
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset


namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)


theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl


end Aux
end
end

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_Basic
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)

local notation3 "g" => SelbergSieve.selbergTerms s

section SieveLemmas

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, prod_inv_distrib, mul_inv, inv_inv]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  revert hnu_nonzero; contrapose!
  exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu _ l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => g x,
        Nat.sum_divisorsAntidiagonal' fun x _ => g x, sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree g (selbergTerms_mult s) d l h]
      · ring
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl; apply selbergTerms_pos; exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms s d hd]

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ X * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

-- Results about Lambda Squared Sieves
section LambdaSquared

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]

  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P :=
    Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [sum_ite_eq_of_mem' (divisors P) (d1.lcm d2) _ (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩)]
  rw [s.nu_mult.map_lcm]
  · ring
  refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
  trans d1
  · exact Nat.gcd_dvd_left d1 d2
  · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [lambdaSquared_mainSum_eq_quad_form s w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [nu_eq_conv_one_div_selbergTerms s _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _
    rw [sum_comm]
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end SelbergSieve
end
end

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_Selberg
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/


noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ y then g k * S⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors P) l (fun _ => if l^2 ≤ y then g l * μ l * S⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) μ⁺ = S⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l * (S⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/g l * g l * g l * (μ l:ℝ)^2  * (S⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d * (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧
      Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  all_goals try with_reducible_and_instances rfl
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      exact (mul_le_of_le_one_left (abs_nonneg <| γ d2) (s.selberg_bound_weights d1)).trans
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| R d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ X * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve
end
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete two-linear-form sieve used for shifted primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma shiftedSievePolynomial_strictMono (b : ℕ) : StrictMono (shiftedSievePolynomial b) := by
  intro q r hqr
  have hsq := Nat.mul_le_mul hqr.le hqr.le
  have hh := Nat.mul_le_mul_left b hsq
  dsimp [shiftedSievePolynomial]
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PeriodicSieveCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval errors for the periodic congruence classes in the sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma count_periodic_blocks (d : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n ↔ P (n%d)) (q r : ℕ) :
    Nat.count P (q*d+r) = q*Nat.count P d+Nat.count P r := by
  have hshift (q : ℕ) : (fun k => P (q*d+k)) = P := by
    funext k
    apply propext
    rw [hP (q*d+k)]
    simp only [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_mod]
    exact (hP k).symm
  have hblocks : Nat.count P (q*d)=q*Nat.count P d := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul,Nat.count_add,ih]
      simp only [hshift]
      ring
  rw [Nat.count_add,hblocks]
  simp only [hshift]

lemma count_periodic_error (d : ℕ) (hd : 0 < d) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n ↔ P (n%d)) (N : ℕ) :
    |(Nat.count P N:ℝ)-(N:ℝ)/d*(Nat.count P d:ℝ)| ≤ d := by
  have hsplit : N=(N/d)*d+N%d := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm
  have hc : Nat.count P N=(N/d)*Nat.count P d+Nat.count P (N%d) := by
    conv_lhs => rw [hsplit]
    exact count_periodic_blocks d P hP (N/d) (N%d)
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hr : ((N%d:ℕ):ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have htail : (Nat.count P (N%d):ℝ) ≤ ((N%d:ℕ):ℝ) := by exact_mod_cast Nat.count_le P
  have hmass : (Nat.count P d:ℝ) ≤ d := by exact_mod_cast Nat.count_le P
  have hfrac : ((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) ≤ ((N%d:ℕ):ℝ) := by
    calc
      _ ≤ ((N%d:ℕ):ℝ)/d*d := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := div_mul_cancel₀ _ hdR.ne'
  have hid : (Nat.count P N:ℝ)-(N:ℝ)/d*(Nat.count P d:ℝ) =
      (Nat.count P (N%d):ℝ)-((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) := by
    rw [hc]
    push_cast
    have hNr : (N:ℝ)=(N/d:ℕ)* (d:ℝ)+(N%d:ℕ) := by exact_mod_cast hsplit
    rw [hNr]
    field_simp
    ring
  rw [hid]
  apply abs_le.mpr
  constructor
  · have hnon : (0:ℝ) ≤ Nat.count P (N%d) := Nat.cast_nonneg _
    linarith
  · have hnon : (0:ℝ) ≤ ((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) := by positivity
    linarith

lemma shiftedSievePolynomial_mod (b d q : ℕ) :
    shiftedSievePolynomial b q % d = shiftedSievePolynomial b (q%d) % d := by
  simp [shiftedSievePolynomial,Nat.add_mod,Nat.mul_mod]

lemma shiftedSieve_count_error (b d : ℕ) (hd : 0 < d) (N : ℕ) :
    |(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) N:ℝ)-
      (N:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ)| ≤ d := by
  apply count_periodic_error d hd
  intro q
  simp only [Nat.dvd_iff_mod_eq_zero,shiftedSievePolynomial_mod b d q]
lemma interval_count_discrepancy (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    |(((Finset.Icc 1 N).filter P).card:ℝ)-(Nat.count P N:ℝ)| ≤ 1 := by
  have hupper : ((Finset.Icc 1 N).filter P).card ≤ Nat.count P N+1 := by
    have hs : (Finset.Icc 1 N).filter P ⊆ (Finset.range (N+1)).filter P := by
      intro n hn
      obtain ⟨hn,hP⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega),hP⟩
    have hh := Finset.card_le_card hs
    rw [← Nat.count_eq_card_filter_range,Nat.count_succ] at hh
    split_ifs at hh <;> omega
  have hlower : Nat.count P N ≤ ((Finset.Icc 1 N).filter P).card+1 := by
    have hs : (Finset.range N).filter P ⊆ insert 0 ((Finset.Icc 1 N).filter P) := by
      intro n hn
      obtain ⟨hn,hP⟩ := Finset.mem_filter.mp hn
      by_cases hz : n=0
      · simp [hz]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨by omega,by have := Finset.mem_range.mp hn; omega⟩,hP⟩
    have hh := (Finset.card_le_card hs).trans (Finset.card_insert_le 0 _)
    rwa [← Nat.count_eq_card_filter_range] at hh
  have hu : (((Finset.Icc 1 N).filter P).card:ℝ) ≤ (Nat.count P N:ℝ)+1 := by exact_mod_cast hupper
  have hl : (Nat.count P N:ℝ) ≤ (((Finset.Icc 1 N).filter P).card:ℝ)+1 := by exact_mod_cast hlower
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma shiftedSieve_interval_error (b d : ℕ) (hd : 0 < d) (N : ℕ) :
    |(((Finset.Icc 1 N).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ)-
      (N:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ)| ≤ d+1 := by
  calc
    _ ≤ |(((Finset.Icc 1 N).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ)-
        (Nat.count (fun q => d ∣ shiftedSievePolynomial b q) N:ℝ)|+
      |(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) N:ℝ)-
        (N:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ)| := abs_sub_le _ _ _
    _ ≤ 1+d := add_le_add (interval_count_discrepancy _ N) (shiftedSieve_count_error b d hd N)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveCRT
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication of the exact shifted-prime residue counts by the Chinese remainder theorem. -/
noncomputable section
namespace TotientAsymptotic

lemma shiftedRootCount_eq_card (d b : ℕ) [NeZero d] :
    shiftedRootCount d b = (shiftedSieveRoots d b).card := by
  rw [shiftedRootCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

lemma shiftedRootCount_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) (b : ℕ) :
    shiftedRootCount (m*n) b = shiftedRootCount m b*shiftedRootCount n b := by
  let _ : NeZero m := ⟨hm⟩
  let _ : NeZero n := ⟨hn⟩
  let e := ZMod.chineseRemainder hcop
  have he (r : ZMod (m*n)) : r*((b:ZMod (m*n))*r+1)=0 ↔
      (e r).1*((b:ZMod m)*(e r).1+1)=0 ∧ (e r).2*((b:ZMod n)*(e r).2+1)=0 := by
    calc
      _ ↔ e (r*((b:ZMod (m*n))*r+1))=0 := e.map_eq_zero_iff.symm
      _ ↔ _ := by
        simp only [map_mul,map_add,map_natCast,map_one,Prod.ext_iff]
        rfl
  let ep : {r : ZMod (m*n) // r*((b:ZMod (m*n))*r+1)=0} ≃
      {r : ZMod m × ZMod n //
        r.1*((b:ZMod m)*r.1+1)=0 ∧ r.2*((b:ZMod n)*r.2+1)=0} :=
    e.toEquiv.subtypeEquiv he
  let ee := ep.trans (Equiv.subtypeProdEquivProd
    (p := fun r : ZMod m => r*((b:ZMod m)*r+1)=0)
    (q := fun r : ZMod n => r*((b:ZMod n)*r+1)=0))
  unfold shiftedRootCount
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  exact (Fintype.card_congr ee).trans (Fintype.card_prod _ _)

lemma shiftedRootCount_prime (p b : ℕ) [Fact p.Prime] :
    shiftedRootCount p b = if p ∣ b then 1 else 2 := by
  rw [shiftedRootCount_eq_card,shiftedSieveRoots_card]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedResidues
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying finite congruence counts with the exact CRT root count. -/
noncomputable section
namespace TotientAsymptotic

lemma shiftedRootCount_eq_count (d b : ℕ) (hd : 0 < d) :
    shiftedRootCount d b = Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let e : {q : ℕ // q<d ∧ d ∣ shiftedSievePolynomial b q} ≃
      {r : ZMod d // r*((b:ZMod d)*r+1)=0} := {
    toFun := fun q => ⟨q.val,by
      have hh := (ZMod.natCast_eq_zero_iff (shiftedSievePolynomial b q.val) d).mpr q.property.2
      simpa only [shiftedSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh⟩
    invFun := fun r => ⟨r.val.val, ZMod.val_lt r.val,by
      apply (ZMod.natCast_eq_zero_iff (shiftedSievePolynomial b r.val.val) d).mp
      simpa only [shiftedSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
        ZMod.natCast_zmod_val] using r.property⟩
    left_inv := fun q => by
      apply Subtype.ext
      exact ZMod.val_natCast_of_lt q.property.1
    right_inv := fun r => by
      apply Subtype.ext
      exact ZMod.natCast_zmod_val r.val }
  let _ : Fintype {q : ℕ // q<d ∧ d ∣ shiftedSievePolynomial b q} :=
    Nat.CountSet.fintype (fun q => d ∣ shiftedSievePolynomial b q) d
  rw [Nat.count_eq_card_fintype]
  exact (Nat.card_congr e).symm.trans Nat.card_eq_fintype_card

lemma shiftedRootCount_one (b : ℕ) : shiftedRootCount 1 b = 1 := by
  rw [shiftedRootCount_eq_count 1 b (by norm_num),Nat.count_one]
  simp [shiftedSievePolynomial]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedDensity
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete multiplicative sieve density equals the exact residue proportion. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma shiftedRootCount_prod (b : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) :
    shiftedRootCount (∏ p ∈ S,p) b = ∏ p ∈ S,shiftedRootCount p b := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using shiftedRootCount_one b
  | @insert p S hp ih =>
    have hprime := hS p (Finset.mem_insert_self _ _)
    have hS' : ∀ q ∈ S,q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S,q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hprime.coprime_iff_not_dvd.mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hprime (hS' q hq)).mp hd
      exact hp (he ▸ hq)
    rw [Finset.prod_insert hp,shiftedRootCount_mul hprime.ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS' q hq).ne_zero)) hcop,
      ih hS',Finset.prod_insert hp]

lemma shiftedRootCount_density (b d : ℕ) (hd : Squarefree d) :
    (shiftedRootCount d b:ℝ) = d*shiftedSieveDensity b d := by
  classical
  have hprod : ∏ p ∈ d.primeFactors,p = d := Nat.prod_primeFactors_of_squarefree hd
  have hcount : shiftedRootCount d b = ∏ p ∈ d.primeFactors,if p ∣ b then 1 else 2 := by
    conv_lhs => rw [← hprod]
    rw [shiftedRootCount_prod b d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    apply Finset.prod_congr rfl
    intro p hp
    let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact shiftedRootCount_prime p b
  have hdensity : shiftedSieveDensity b d =
      ∏ p ∈ d.primeFactors,if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ) :=
    ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero
  calc
    _ = ∏ p ∈ d.primeFactors,if p ∣ b then (1:ℝ) else 2 := by
      rw [hcount,Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> simp
    _ = ∏ p ∈ d.primeFactors,(p:ℝ)*(if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ)) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p:ℝ)≠0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      split_ifs <;> field_simp
    _ = _ := by
      rw [Finset.prod_mul_distrib,hdensity,← Nat.cast_prod,hprod]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact translation of simultaneous shifted primes into the Selberg sieve. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.omega
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma shiftedPrimePair_coprime {b X z q : ℕ} (hq : q ∈ shiftedPrimePairs b X z) :
    (∏ p ∈ oddSievePrimes z,p).Coprime (shiftedSievePolynomial b q) := by
  obtain ⟨_,hprime,hshift,hzq,hzs⟩ := Finset.mem_filter.mp hq
  apply Nat.coprime_of_dvd
  intro p hp hpd hpv
  have hpz := (mem_oddSievePrimes.mp (mem_oddSievePrimes_of_dvd hp hpd)).1
  change p ∣ q*(b*q+1) at hpv
  rcases hp.dvd_mul.mp hpv with hd | hd
  · have he := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hd
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp hshift).mp hd
    omega

lemma shiftedPrimePairs_le_sifted (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((shiftedPrimePairs b X z).card:ℝ) ≤
      siftedSum (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) := by
  let f := shiftedSievePolynomial b
  have hinj := (shiftedSievePolynomial_strictMono b).injective
  have hsubset : (shiftedPrimePairs b X z).image f ⊆
      ((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ oddSievePrimes z,p).Coprime n) := by
    intro n hn
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,(Finset.mem_filter.mp hq).1,rfl⟩,
      shiftedPrimePair_coprime hq⟩
  have hh := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ hinj] at hh
  have he : siftedSum (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) =
      (((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ oddSievePrimes z,p).Coprime n)).card := by
    change (∑ d ∈ (Finset.Icc 1 X).image f,
      if (∏ p ∈ oddSievePrimes z,p).Coprime d then (1:ℝ) else 0) = _
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast hh

lemma shiftedPrimeSieve_multSum (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) :
    multSum (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d =
      (((Finset.Icc 1 X).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ) := by
  simp only [multSum,shiftedPrimeSieve]
  rw [Finset.sum_image]
  · simp only [Finset.sum_boole]
  · exact fun a _ b _ h => (shiftedSievePolynomial_strictMono _).injective h

/-- A genuine sieve bound for the actual prime pairs, with the exact local
remainders still visible for the next arithmetic estimate. -/
theorem shiftedPrimePairs_selberg (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    let s := shiftedPrimeSieve b X z y hy
    ((shiftedPrimePairs b X z).card:ℝ) ≤ X / selbergBoundingSum s +
      ∑ d ∈ (∏ p ∈ oddSievePrimes z,p).divisors,
        if (d:ℝ) ≤ y then (3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
          |rem (s := s.toBoundingSieve) d| else 0 := by
  exact (shiftedPrimePairs_le_sifted b X z y hy).trans
    (selberg_bound_simple (shiftedPrimeSieve b X z y hy))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveRemainder
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit local discrepancy bound for the actual shifted-prime sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma shiftedPrimeSieve_rem_le (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) {d : ℕ}
    (hd : Squarefree d) :
    |BoundingSieve.rem (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d| ≤ d+1 := by
  rw [BoundingSieve.rem,shiftedPrimeSieve_multSum]
  change |(((Finset.Icc 1 X).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ)-
    shiftedSieveDensity b d*(X:ℝ)| ≤ d+1
  have he : (X:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ) =
      shiftedSieveDensity b d*(X:ℝ) := by
    rw [← shiftedRootCount_eq_count d b (Nat.pos_of_ne_zero hd.ne_zero),shiftedRootCount_density b d hd]
    field_simp [show (d:ℝ)≠0 by exact_mod_cast hd.ne_zero]
  rw [← he]
  exact shiftedSieve_interval_error b d (Nat.pos_of_ne_zero hd.ne_zero) X

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveError
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial bound for the complete error term of the concrete Selberg sieve. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma odd_sieve_divisor_weight {z d : ℕ} (hd : d ∣ ∏ p ∈ oddSievePrimes z,p) :
    (3:ℕ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
  have hsq := (oddSievePrimes_prod_squarefree z).squarefree_of_dvd hd
  have hlen : ArithmeticFunction.cardDistinctFactors d ≤ d.primeFactorsList.length :=
    d.primeFactorsList.dedup_sublist.length_le
  calc
    _ ≤ 3^d.primeFactorsList.length := Nat.pow_le_pow_right (by norm_num) hlen
    _ ≤ d.primeFactorsList.prod := List.pow_card_le_prod _ 3 (by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactorsList hp
      have hmem := mem_oddSievePrimes_of_dvd hprime ((Nat.dvd_of_mem_primeFactorsList hp).trans hd)
      have hh := mem_oddSievePrimes.mp hmem
      have := hprime.two_le
      omega)
    _ = d := Nat.prod_primeFactorsList hsq.ne_zero

lemma shiftedPrimeSieve_error_sum (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ (∏ p ∈ oddSievePrimes z,p).divisors,
      if (d:ℝ) ≤ y then (3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
        |rem (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d| else 0) ≤ 2*y^3 := by
  classical
  let P : ℕ := ∏ p ∈ oddSievePrimes z,p
  let T : Finset ℕ := P.divisors.filter (fun d : ℕ => (d:ℝ) ≤ y)
  have hP := oddSievePrimes_prod_squarefree z
  have hT (d : ℕ) (hd : d∈T) : d∣P ∧ 1≤d ∧ (d:ℝ)≤y := by
    obtain ⟨hd,hy⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd,hP0⟩ := Nat.mem_divisors.mp hd
    have h0 : d≠0 := by
      intro h
      subst d
      exact hP0 (zero_dvd_iff.mp hd)
    exact ⟨hd,Nat.one_le_iff_ne_zero.mpr h0,hy⟩
  have hcard : (T.card:ℝ) ≤ y := by
    have hsub : T ⊆ Finset.Icc 1 ⌊y⌋₊ := by
      intro d hd
      have hh := hT d hd
      exact Finset.mem_Icc.mpr ⟨hh.2.1,Nat.le_floor hh.2.2⟩
    have hh := Finset.card_le_card hsub
    have hc : (T.card:ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast (by simpa using hh : T.card ≤ ⌊y⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  rw [← Finset.sum_filter]
  change (∑ d ∈ T,(3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
      |rem (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d|) ≤ _
  calc
    _ ≤ ∑ _d ∈ T,2*y^2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd,h1,hdy⟩ := hT d hd
      have hweight : (3:ℝ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
        exact_mod_cast odd_sieve_divisor_weight hd
      have hrem := shiftedPrimeSieve_rem_le b X z y hy (hP.squarefree_of_dvd hd)
      have hdR : (1:ℝ)≤d := by exact_mod_cast h1
      have hh := mul_le_mul hweight hrem (abs_nonneg _) (by positivity : (0:ℝ)≤d)
      nlinarith
    _ = (T.card:ℝ)*(2*y^2) := by simp
    _ ≤ y*(2*y^2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- All arithmetic remainders in the two-linear-form sieve are now eliminated. -/
theorem shiftedPrimePairs_bound (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((shiftedPrimePairs b X z).card:ℝ) ≤
      X/selbergBoundingSum (shiftedPrimeSieve b X z y hy)+2*y^3 :=
  (shiftedPrimePairs_selberg b X z y hy).trans
    (add_le_add le_rfl (shiftedPrimeSieve_error_sum b X z y hy))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factor-count additivity and largest-factor alignment for collision pairs. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeFactor_le_largest {n p : ℕ} (hp : p ∈ n.primeFactorsList) :
    p ≤ largestPrimeFactor n := by
  have hm : p ∈ n.primeFactors := by
    change p ∈ n.primeFactorsList.toFinset
    exact List.mem_toFinset.mpr hp
  exact (Finset.le_sup (f := id) hm).trans (le_max_right _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothSuffix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the residual totient in an actual basic collision witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma largestPrimeFactor_le_of_prime_divisors {n z : ℕ} (hz : 1 ≤ z)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → n ≠ 0 → p ≤ z) : largestPrimeFactor n ≤ z := by
  apply max_le hz
  apply Finset.sup_le
  intro p hp
  obtain ⟨hp', hd, hn⟩ := Nat.mem_primeFactors.mp hp
  exact h p hp' hd hn

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalPrimeBands
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-factor bands derived from normality, including the small-prime case. -/

noncomputable section

namespace TotientAsymptotic

lemma largestPrimeFactor_le_self {n : ℕ} (hn : 1 ≤ n) : largestPrimeFactor n ≤ n := by
  apply largestPrimeFactor_le_of_prime_divisors hn
  intro p _ hp hn0
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteSieveMass
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite product mass and its first logarithmic moment for the Selberg denominator. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma subset_weight_moment (S : Finset ℕ) (w l : ℕ → ℝ)
    (hw : ∀ p ∈ S,0 ≤ w p) :
    (∑ T ∈ S.powerset,(∏ p ∈ T,w p)*(∑ p ∈ T,l p)) =
      (∏ p ∈ S,(1+w p))*(∑ p ∈ S,w p*l p/(1+w p)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hwS : ∀ p ∈ S,0 ≤ w p := fun p hp => hw p (Finset.mem_insert_of_mem hp)
    have ha0 := hw a (Finset.mem_insert_self _ _)
    have hne : 1+w a ≠ 0 := by linarith
    have hnew : (∑ T ∈ S.powerset,(∏ p ∈ insert a T,w p)*(∑ p ∈ insert a T,l p)) =
        w a*l a*(∑ T ∈ S.powerset,∏ p ∈ T,w p)+
          w a*(∑ T ∈ S.powerset,(∏ p ∈ T,w p)*(∑ p ∈ T,l p)) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      rw [Finset.prod_insert haT,Finset.sum_insert haT]
      ring_nf
    rw [Finset.sum_powerset_insert ha,hnew,← Finset.prod_one_add,ih hwS,
      Finset.prod_insert ha,Finset.sum_insert ha]
    field_simp [hne]
    ring

/-- If the first moment is at most half the cutoff, at least half of the
Euler-product mass comes from subsets below that cutoff. -/
lemma subset_weight_below_half (S : Finset ℕ) (w l : ℕ → ℝ)
    (hw : ∀ p ∈ S,0 ≤ w p) (hl : ∀ p ∈ S,0 ≤ l p)
    {L : ℝ} (hL : 0 < L)
    (hmean : (∑ p ∈ S,w p*l p/(1+w p)) ≤ L/2) :
    (∏ p ∈ S,(1+w p))/2 ≤
      ∑ T ∈ S.powerset,if (∑ p ∈ T,l p) ≤ L then (∏ p ∈ T,w p) else 0 := by
  classical
  have hwT (T : Finset ℕ) (hT : T ∈ S.powerset) : 0 ≤ ∏ p ∈ T,w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hT hp))
  have hlT (T : Finset ℕ) (hT : T ∈ S.powerset) : 0 ≤ ∑ p ∈ T,l p :=
    Finset.sum_nonneg (fun p hp => hl p (Finset.mem_powerset.mp hT hp))
  have hpoint : ∀ T ∈ S.powerset,L*(∏ p ∈ T,w p) ≤
      L*(if (∑ p ∈ T,l p) ≤ L then (∏ p ∈ T,w p) else 0)+
        (∏ p ∈ T,w p)*(∑ p ∈ T,l p) := by
    intro T hT
    split_ifs with hsmall
    · nlinarith [mul_nonneg (hwT T hT) (hlT T hT)]
    · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) (hwT T hT)
      nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.prod_one_add,
    subset_weight_moment S w l hw] at hsum
  have hprod : 0 ≤ ∏ p ∈ S,(1+w p) := Finset.prod_nonneg (fun p hp => by have := hw p hp; linarith)
  have hm := mul_le_mul_of_nonneg_left hmean hprod
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorEnvelope
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The cofactor envelope from Mertens' published prime-product theorem.
We use only its upper bound, stated as Theorem 1.1, equation (1.2), in
J. D. Lichtman, *Mertens' prime product formula, dissected*,
arXiv:2002.03361v3 (2021), citing Mertens (1874),
*J. reine angew. Math.* 78, 46–62. This is an explicit conditional input.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma totient_ratio_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (p : ℝ)/(p-1) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hprod : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p-1 : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have he := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
  push_cast at he
  have he' : (n.totient : ℝ)*(∏ p ∈ n.primeFactors, (p : ℝ)) =
      n*(∏ p ∈ n.primeFactors, (p-1 : ℝ)) := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [Finset.prod_div_distrib]
  exact (div_eq_div_iff hφ.ne' hprod.ne').mpr (by nlinarith [he'])

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensLogMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite summation-by-parts bound sufficient for the Mertens product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma weighted_sum_le_harmonic (a : ℕ → ℝ) (C : ℝ)
    (ha0 : a 0=0)
    (hA : ∀ n : ℕ, (∑ i ∈ Finset.range (n+1), a i) ≤ C*(n+1)) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), a i/(i : ℝ)) ≤
      (∑ i ∈ Finset.range (n+1), a i)/(n+1)+C*(harmonic n : ℝ) := by
  induction n with
  | zero => simp [ha0]
  | succ n ih =>
    have hn : (0 : ℝ)<n+1 := by positivity
    have hn2 : (0 : ℝ)<n+2 := by positivity
    let A := ∑ i ∈ Finset.range (n+2), a i
    have hA' : A ≤ C*(n+2) := by
      convert hA (n+1) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    have hstep : A/(n+1) ≤ A/(n+2)+C/(n+1) := by
      apply (div_le_iff₀ hn).mpr
      have hdiv : A/(n+2) ≤ C := (div_le_iff₀ hn2).mpr hA'
      have he : A/(n+2)*(n+2)=A := div_mul_cancel₀ A hn2.ne'
      rw [add_mul,div_mul_cancel₀ _ hn.ne']
      nlinarith
    have hrec : A=(∑ i ∈ Finset.range (n+1), a i)+a (n+1) := by
      exact Finset.sum_range_succ a (n+1)
    calc
      _ = (∑ i ∈ Finset.range (n+1), a i/(i : ℝ))+a (n+1)/(n+1) := by
        rw [Finset.sum_range_succ]
        push_cast
        rfl
      _ ≤ (∑ i ∈ Finset.range (n+1), a i)/(n+1)+C*(harmonic n : ℝ)+
          a (n+1)/(n+1) := add_le_add ih le_rfl
      _ = A/(n+1)+C*(harmonic n : ℝ) := by
        rw [hrec,add_div]
        ring
      _ ≤ A/(n+2)+C/(n+1)+C*(harmonic n : ℝ) := add_le_add hstep le_rfl
      _ = _ := by
        rw [harmonic_succ]
        push_cast
        dsimp [A]
        ring

/-- Only a coarse logarithmic bound is needed; no Mertens theorem is assumed. -/
lemma prime_log_mass_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ)) ≤
      Real.log 4*(2+Real.log N) := by
  classical
  let a : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have he (n : ℕ) : (∑ i ∈ Finset.range (n+1), a i)=Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,← Nat.range_succ_eq_Icc_zero,
      Finset.sum_filter]

  have hA (n : ℕ) : (∑ i ∈ Finset.range (n+1), a i) ≤ Real.log 4*(n+1) := by
    rw [he]
    have hh := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have hc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hb := weighted_sum_le_harmonic a (Real.log 4) (by simp [a]) hA N
  have hsum : (∑ i ∈ Finset.range (N+1), a i/(i : ℝ))=
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ) := by
    rw [Nat.range_succ_eq_Icc_zero,Finset.sum_filter]
    simp only [a,ite_div,zero_div]
    symm
    apply Finset.sum_subset (fun p hp => by
      have hh := Finset.mem_Icc.mp hp
      exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩)
    · intro p hp hnot
      have hp2 : p<2 := by
        have hh := Finset.mem_Icc.mp hp
        simp only [Finset.mem_Icc,not_and_or,not_le] at hnot
        omega
      have hprime : ¬p.Prime := fun hh => (not_le_of_gt hp2) hh.two_le
      simp [hprime]
  rw [hsum] at hb
  have ht := (div_le_iff₀ (show (0 : ℝ)<N+1 by positivity)).mpr (hA N)
  have hh := harmonic_le_one_add_log N
  have hc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh hc
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveDenominator
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler-product lower bound for the concrete Selberg denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma shiftedSieveWeight_nonneg (b : ℕ) {z p : ℕ} (hp : p ∈ oddSievePrimes z) :
    0 ≤ shiftedSieveWeight b p := by
  obtain ⟨_,hpp,hp2⟩ := mem_oddSievePrimes.mp hp
  exact div_nonneg (shiftedSieveDensity_positive b p hpp).le
    (sub_pos.mpr (shiftedSieveDensity_lt_one b p hpp hp2)).le

lemma shiftedSieveWeight_moment (b : ℕ) {z p : ℕ} (hp : p ∈ oddSievePrimes z) :
    shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p) =
      shiftedSieveDensity b p * Real.log p := by
  obtain ⟨_,hpp,hp2⟩ := mem_oddSievePrimes.mp hp
  have hn : 1-shiftedSieveDensity b p ≠ 0 :=
    (sub_pos.mpr (shiftedSieveDensity_lt_one b p hpp hp2)).ne'
  have hn' : 1+shiftedSieveWeight b p ≠ 0 := by
    have := shiftedSieveWeight_nonneg b hp
    linarith
  unfold shiftedSieveWeight
  field_simp
  ring

lemma shiftedSieve_moment_le (b z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ oddSievePrimes z,
      shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p)) ≤
        2*Real.log 4*(2+Real.log z) := by
  have hpoint (p : ℕ) (hp : p ∈ oddSievePrimes z) :
      shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p) ≤
        2*(Real.log p/(p:ℝ)) := by
    obtain ⟨_,hpp,_⟩ := mem_oddSievePrimes.mp hp
    rw [shiftedSieveWeight_moment b hp,shiftedSieveDensity_prime b p hpp]
    have hp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    split_ifs <;> simp only [div_eq_mul_inv] <;> nlinarith [mul_nonneg (inv_nonneg.mpr hp0.le) hl]
  calc
    _ ≤ ∑ p ∈ oddSievePrimes z,2*(Real.log p/(p:ℝ)) := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,2*(Real.log p/(p:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpz,hpp,_⟩ := mem_oddSievePrimes.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le,hpz⟩,hpp⟩
      · intro p hp _
        have hpp := (Finset.mem_filter.mp hp).2
        exact mul_nonneg (by norm_num) (div_nonneg
          (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) (Nat.cast_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      nlinarith [prime_log_mass_le z hz]

lemma shiftedSieveTerms_prod (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (T : Finset ℕ) (hT : T ⊆ oddSievePrimes z) :
    selbergTerms (shiftedPrimeSieve b X z y hy).toBoundingSieve (∏ p ∈ T,p) =
      ∏ p ∈ T,shiftedSieveWeight b p := by
  rw [(selbergTerms_mult _).map_prod_of_prime T
    (fun p hp => (mem_oddSievePrimes.mp (hT hp)).2.1)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (mem_oddSievePrimes.mp (hT hp)).2.1
  rw [SelbergSieve.selbergTerms_apply]
  simp only [hpp.primeFactors,Finset.prod_singleton]
  change shiftedSieveDensity b p * (1/(1-shiftedSieveDensity b p)) = _
  simp [shiftedSieveWeight,div_eq_mul_inv]

lemma shiftedSieveBoundingSum_powerset (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    selbergBoundingSum (shiftedPrimeSieve b X z y hy) =
      ∑ T ∈ (oddSievePrimes z).powerset,
        if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then ∏ p ∈ T,shiftedSieveWeight b p else 0 := by
  classical
  have hsq := oddSievePrimes_prod_squarefree z
  unfold selbergBoundingSum
  change (∑ d ∈ (∏ p ∈ oddSievePrimes z,p).divisors,
    if (d:ℝ)^2 ≤ y then selbergTerms (shiftedPrimeSieve b X z y hy).toBoundingSieve d else 0) = _
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero,Nat.factors_eq]
  simp only [List.toFinset_coe,Finset.prod_val]
  change (∑ T ∈ (∏ p ∈ oddSievePrimes z,p).primeFactors.powerset,
    if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then
      selbergTerms (shiftedPrimeSieve b X z y hy).toBoundingSieve (∏ p ∈ T,p) else 0) = _
  rw [Nat.primeFactors_prod (fun p hp => (mem_oddSievePrimes.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [shiftedSieveTerms_prod b X z y hy T (Finset.mem_powerset.mp hT)]

/-- The logarithmic first moment confines at least half of the Euler product to
integers within the square-root cutoff used by Selberg's denominator. -/
theorem shiftedSieveBoundingSum_lower (b X z : ℕ) (y : ℝ) (hy : 1 < y)
    (hz : 2 ≤ z) (hscale : 8*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    (∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p))/2 ≤
      selbergBoundingSum (shiftedPrimeSieve b X z y hy.le) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hl : 0 < Real.log y / 2 := by positivity
  have hm : (∑ p ∈ oddSievePrimes z,
      shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p)) ≤
        (Real.log y/2)/2 := by
    nlinarith [shiftedSieve_moment_le b z hz]
  have hh := subset_weight_below_half (oddSievePrimes z) (shiftedSieveWeight b)
    (fun p => Real.log p) (fun p hp => shiftedSieveWeight_nonneg b hp)
    (fun p hp => Real.log_nonneg (by
      exact_mod_cast (mem_oddSievePrimes.mp hp).2.1.one_lt.le)) hl hm
  apply hh.trans
  rw [shiftedSieveBoundingSum_powerset]
  apply Finset.sum_le_sum
  intro T hT
  have hTp := Finset.mem_powerset.mp hT
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => (mem_oddSievePrimes.mp (hTp hp)).2.1
  have hpos : (0:ℝ) < (∏ p ∈ T,p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hlog : Real.log ((∏ p ∈ T,p : ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
    rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
  split_ifs with hsmall hcut hcut
  · exact le_rfl
  · exfalso
    apply hcut
    apply (Real.log_le_log_iff (sq_pos_of_pos hpos) (by linarith : 0<y)).mp
    rw [Real.log_pow,hlog]
    norm_num
    linarith
  · exact Finset.prod_nonneg (fun p hp => shiftedSieveWeight_nonneg b (hTp hp))
  · exact le_rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothResidualMass
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler product bounds the entire smooth residual-integer sum. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_reciprocal_norm_lt_one {p : ℕ} (hp : p.Prime) : ‖reciprocalNatHom p‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simpa only [reciprocalNatHom,MonoidHom.coe_mk,OneHom.coe_mk,Real.norm_eq_abs,
    abs_inv,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)] using (inv_lt_one₀ (zero_lt_one.trans hpR)).mpr hpR

lemma reciprocal_prime_factor (p : ℕ) (hp : p.Prime) :
    (1-reciprocalNatHom p)⁻¹=(p : ℝ)/(p-1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change (1-(p : ℝ)⁻¹)⁻¹=(p : ℝ)/(p-1)
  field_simp

/-- Only positivity and smoothness are used; the residuals may repeat prime
factors and the upper cutoff on their size is arbitrary. -/
theorem smooth_residual_reciprocal_mass (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N) :
    (∑ n ∈ Q, (n : ℝ)⁻¹) ≤ primeEulerProduct N := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (primeFactor_le_largest hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ T, reciprocalNatHom n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    change (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ Q.attach, (n.val : ℝ)⁻¹
    exact (Finset.sum_attach Q (fun n : ℕ => (n : ℝ)⁻¹)).symm
  have hseries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalNatHom) (fun {_} hp => prime_reciprocal_norm_lt_one hp) S
  calc
    _ = ∑ n ∈ T, reciprocalNatHom n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, reciprocalNatHom n := by
      apply hseries.1.of_norm.sum_le_tsum
      intro n _
      change 0 ≤ (n.val : ℝ)⁻¹
      positivity
    _ = ∏ p ∈ S with p.Prime, (1-reciprocalNatHom p)⁻¹ := hseries.2.tsum_eq
    _ = primeEulerProduct N := by
      apply Finset.prod_congr rfl
      intro p hp
      exact reciprocal_prime_factor p (Finset.mem_filter.mp hp).2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SieveEulerProduct
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary lower bounds for the sieve Euler product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeEulerProduct_log_lower (N : ℕ) : Real.log N ≤ primeEulerProduct N := by
  have h := smooth_residual_reciprocal_mass N (Finset.Icc 1 N) (by
    intro n hn
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hn
    exact ⟨hn1,(largestPrimeFactor_le_self hn1).trans hnN⟩)
  have he : (∑ n ∈ Finset.Icc 1 N,(n:ℝ)⁻¹) = (harmonic N:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [he] at h
  have hl := log_le_harmonic_floor (N:ℝ) (Nat.cast_nonneg N)
  simp only [Nat.floor_natCast] at hl
  exact hl.trans h

lemma oddEulerProduct_eq (z : ℕ) (hz : 2 ≤ z) :
    primeEulerProduct z = 2 * ∏ p ∈ oddSievePrimes z,(p:ℝ)/(p-1) := by
  classical
  have htwo : 2 ∈ (Finset.Icc 2 z).filter Nat.Prime := by norm_num [hz]
  have hs : oddSievePrimes z = ((Finset.Icc 2 z).filter Nat.Prime).erase 2 := by
    ext p
    simp only [mem_oddSievePrimes,Finset.mem_erase,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hpz,hpp,hp2⟩
      exact ⟨hp2,⟨hpp.two_le,hpz⟩,hpp⟩
    · rintro ⟨hp2,⟨_,hpz⟩,hpp⟩
      exact ⟨hpz,hpp,hp2⟩
  rw [hs,primeEulerProduct,← Finset.mul_prod_erase _ _ htwo]
  norm_num

lemma oddEulerProduct_log_lower (z : ℕ) (hz : 2 ≤ z) :
    Real.log z / 2 ≤ ∏ p ∈ oddSievePrimes z,(p:ℝ)/(p-1) := by
  have h := primeEulerProduct_log_lower z
  rw [oddEulerProduct_eq z hz] at h
  linarith

lemma shiftedSieveWeight_euler_factor (b p : ℕ) (hpp : p.Prime) (hp2 : p ≠ 2) :
    ((p:ℝ)/(p-1))^2 ≤
      (1+shiftedSieveWeight b p) * (if p ∣ b then (p:ℝ)/(p-1) else 1) := by
  have hpR : (2:ℝ) < p := by have := hpp.two_le; exact_mod_cast (by omega : 2<p)
  rw [shiftedSieveWeight,shiftedSieveDensity_prime b p hpp]
  split_ifs with hd
  · have hn : (p:ℝ)≠0 := by linarith
    have he : 1+(p:ℝ)⁻¹/(1-(p:ℝ)⁻¹) = (p:ℝ)/(p-1) := by
      field_simp [show (p:ℝ)-1≠0 by linarith]
      ring
    rw [he]
    exact le_of_eq (pow_two _)
  · have hn : (p:ℝ)-2>0 := by linarith
    have hn' : (p:ℝ)-1>0 := by linarith
    have he : 1+2/(p:ℝ)/(1-2/(p:ℝ)) = (p:ℝ)/(p-2) := by field_simp <;> ring
    rw [mul_one,he]
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hn') hn).mpr
    nlinarith

lemma sieve_exceptional_product_le_totient {b : ℕ} (hb : 0 < b) (z : ℕ) :
    (∏ p ∈ oddSievePrimes z,if p ∣ b then (p:ℝ)/(p-1) else 1) ≤ (b:ℝ)/b.totient := by
  classical
  rw [← Finset.prod_filter,totient_ratio_product hb]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_oddSievePrimes.mp hp).2.1,hd,hb.ne'⟩
  · intro p hp
    have hpp := (mem_oddSievePrimes.mp (Finset.mem_filter.mp hp).1).2.1
    have hp1 : (1:ℝ)<p := by exact_mod_cast hpp.one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · intro p hp _
    have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    apply (le_div_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
    linarith

lemma shiftedSieveEulerProduct_lower {b : ℕ} (hb : 0 < b) (z : ℕ) (hz : 2 ≤ z) :
    (Real.log z)^2 / 4 ≤
      (∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p)) * ((b:ℝ)/b.totient) := by
  have hfactor : (∏ p ∈ oddSievePrimes z,(p:ℝ)/(p-1))^2 ≤
      (∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p)) *
        (∏ p ∈ oddSievePrimes z,if p ∣ b then (p:ℝ)/(p-1) else 1) := by
    rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p hp
      positivity
    · intro p hp
      exact shiftedSieveWeight_euler_factor b p (mem_oddSievePrimes.mp hp).2.1
        (mem_oddSievePrimes.mp hp).2.2
  have hp : 0 ≤ ∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p) :=
    Finset.prod_nonneg (fun p hp => by have := shiftedSieveWeight_nonneg b hp; linarith)
  have he := mul_le_mul_of_nonneg_left (sieve_exceptional_product_le_totient hb z) hp
  have hl := oddEulerProduct_log_lower z hz
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast (show 1≤z by omega))
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CanceledPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal cost of fixing the canceled primes, from Mertens' input. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeEulerProduct_pos (N : ℕ) : 0 < primeEulerProduct N := by
  apply Finset.prod_pos
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_pos (by linarith) (by linarith)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensEuler
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler product controlled by a convergent real power series. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace TotientAsymptotic

lemma negative_power_sum_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ)^(-s)) ≤ 1+1/(s-1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x^(-s)) 1
    (fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (by simpa using hx)) hxy (by linarith))
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (zero_lt_one.trans (by simpa using hx)).le _)
  simp only [Nat.cast_one] at htail
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0 : ℝ)<1)] at htail
  have he : (∑' n : ℕ, (n : ℝ)^(-s))=1+∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s) := by
    rw [← hsum.sum_add_tsum_nat_add 2]
    norm_num [Finset.sum_range_succ,show s≠0 by linarith]
    congr 1
    funext n
    congr 1
    ring
  rw [he]
  have htail' : (∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s)) ≤ 1/(s-1) := by
    have hi : -(1 : ℝ)^(-s+1)/(-s+1)=1/(s-1) := by
      rw [Real.one_rpow,show -s+1= -(s-1) by ring]
      simp only [div_neg,neg_div,neg_neg]
    exact hi ▸ htail
  linarith

lemma finite_power_euler_product_le {s : ℝ} (hs : 1 < s) (S : Finset ℕ) :
    (∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹) ≤ 1+1/(s-1) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖negativePower s p‖<1 := by
    intro p hp
    change ‖(p : ℝ)^(-s)‖<1
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by exact_mod_cast hp.one_lt)
      (show -s<0 by linarith)
    simpa only [Real.rpow_zero] using h
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := negativePower s) hp S
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hb := hsum.tsum_subtype_le (fun n : ℕ => (n : ℝ)^(-s))
    (Nat.factoredNumbers S) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have heq : (∑' n : Nat.factoredNumbers S, negativePower s n)=
      ∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹ := he.2.tsum_eq
  exact heq.symm.trans_le (hb.trans (negative_power_sum_le hs))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensFactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the ordinary and convergent prime Euler factors. -/
noncomputable section
namespace TotientAsymptotic

lemma mertens_factor_le {u : ℝ} (hu : 0<u) {p : ℕ} (hp : p.Prime) :
    (p : ℝ)/(p-1) ≤ Real.exp (2*u*Real.log p/p)*(1-(p : ℝ)^(-(1+u)))⁻¹ := by
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ)<p := by linarith
  have hd : (0 : ℝ)<p-1 := by linarith
  have hv : 0≤u*Real.log p := mul_nonneg hu.le (Real.log_nonneg (by linarith))
  have hpow : (p : ℝ)^(-(1+u))=(p : ℝ)⁻¹*Real.exp (-(u*Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0]
    have he : Real.log (p : ℝ)*(-(1+u))= -Real.log p+ -(u*Real.log p) := by ring
    rw [he,Real.exp_add,Real.exp_neg,Real.exp_log hp0]
  have hpowlt : (p : ℝ)^(-(1+u))<1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by linarith)
      (show -(1+u)<0 by linarith)
    simpa using h
  have hB : 0<1-(p : ℝ)^(-(1+u)) := by linarith
  have hr : (1 : ℝ)/(p-1)≤2/p := by
    apply (div_le_div_iff₀ hd hp0).mpr
    nlinarith
  have he : (p : ℝ)/(p-1)*(1-(p : ℝ)^(-(1+u))) ≤ Real.exp (2*u*Real.log p/p) := by
    calc
      _ = 1+(1-Real.exp (-(u*Real.log p)))/(p-1) := by
        rw [hpow]
        field_simp
        ring
      _ ≤ 1+(u*Real.log p)/(p-1) := by
        apply add_le_add le_rfl
        apply div_le_div_of_nonneg_right _ hd.le
        linarith [Real.one_sub_le_exp_neg (u*Real.log p)]
      _ ≤ 1+2*u*Real.log p/p := by
        have hh := mul_le_mul_of_nonneg_left hr hv
        first | (convert add_le_add_left hh 1 using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((add_le_add_left hh 1).trans (le_of_eq (by ring)))
      _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (2*u*Real.log p/p)
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hB).mpr he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensProduct
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete Mertens upper bound used by the totient asymptotic. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeEulerProduct_rankin {u : ℝ} (hu : 0<u) (N : ℕ) :
    primeEulerProduct N ≤
      Real.exp (2*u*(∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        Real.log p/(p : ℝ)))*(1+1/u) := by
  let S := (Finset.Icc 2 N).filter Nat.Prime
  have he : (∏ p ∈ S, Real.exp (2*u*Real.log p/p))=
      Real.exp (2*u*(∑ p ∈ S, Real.log p/p)) := by
    rw [← Real.exp_sum,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring
  calc
    primeEulerProduct N ≤ ∏ p ∈ S,
        Real.exp (2*u*Real.log p/p)*(1-(p : ℝ)^(-(1+u)))⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp
        exact mertens_factor_le hu (Finset.mem_filter.mp hp).2
    _ = Real.exp (2*u*(∑ p ∈ S, Real.log p/p))*
        ∏ p ∈ S, (1-(p : ℝ)^(-(1+u)))⁻¹ := by
      rw [Finset.prod_mul_distrib,he]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hh := finite_power_euler_product_le (show 1<1+u by linarith) (Finset.Icc 2 N)
      simpa only [add_sub_cancel_left] using hh

/-- Mertens' full asymptotic is unnecessary here: Chebyshev, finite Euler
products and the integral test prove exactly the required upper bound. -/
theorem mertensProductInput : MertensProductInput := by
  refine ⟨3*Real.exp (10*Real.log 4),by positivity,?_⟩
  intro N hN
  have hlog : (1/2 : ℝ)<Real.log N := by
    have hn : (2 : ℝ)≤N := by exact_mod_cast hN
    have hh := Real.log_le_log (by norm_num : (0 : ℝ)<2) hn
    linarith [Real.log_two_gt_d9]
  have hc : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hu : 0<1/Real.log N := by positivity
  have hb := primeEulerProduct_rankin hu N
  have hm := mul_le_mul_of_nonneg_left (prime_log_mass_le N hN)
    (show 0≤2*(1/Real.log N) by positivity)
  have hexp : 2*(1/Real.log N)*(∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      Real.log p/(p : ℝ)) ≤ 10*Real.log 4 := by
    have hi : 1/Real.log N≤2 := by
      apply (div_le_iff₀ (by linarith : 0<Real.log N)).mpr
      linarith
    have he : 2*(1/Real.log N)*(Real.log 4*(2+Real.log N))=
        4*(1/Real.log N)*Real.log 4+2*Real.log 4 := by
      field_simp
      ring
    rw [he] at hm
    nlinarith
  have hlast : 1+1/(1/Real.log N) ≤ 3*Real.log N := by
    simp only [one_div_one_div]
    linarith
  calc
    primeEulerProduct N ≤ Real.exp (2*(1/Real.log N)*
        (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ)))*
        (1+1/(1/Real.log N)) := hb
    _ ≤ Real.exp (10*Real.log 4)*(3*Real.log N) :=
      mul_le_mul (Real.exp_le_exp.mpr hexp) hlast (by positivity) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientRatioLogLog
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform log-log bound for the elementary totient ratio. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma totient_factor_large_prime {p : ℕ} (hp : p.Prime) {L : ℝ}
    (hL : 0<L) (hpL : L≤p) :
    (p:ℝ)/(p-1) ≤ Real.exp (4*Real.log p/L) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := by linarith
  have hp1 : (0:ℝ)<p-1 := by linarith
  have hlog : (1/2:ℝ)≤Real.log p := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hp2
    linarith [Real.log_two_gt_d9]
  have hfirst : (1:ℝ)/(p-1) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith
  have hsecond : 2/(p:ℝ) ≤ 4*Real.log p/L := by
    apply (div_le_div_iff₀ hp0 hL).mpr
    nlinarith
  have he : (p:ℝ)/(p-1) = 1+1/(p-1) := by field_simp <;> ring
  rw [he]
  have hh := Real.add_one_le_exp (4*Real.log p/L)
  linarith

lemma totient_large_prime_product {b : ℕ} (hb : 0<b) {L : ℝ} (hL : 0<L)
    (hbL : Real.log b ≤ L) (T : Finset ℕ) (hT : T ⊆ b.primeFactors)
    (hlarge : ∀ p ∈ T,L≤p) :
    (∏ p ∈ T,(p:ℝ)/(p-1)) ≤ Real.exp 4 := by
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
  have hprod0 : (0:ℝ)<(∏ p ∈ T,p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hdvd : (∏ p ∈ T,p) ∣ b :=
    (Finset.prod_dvd_prod_of_subset T b.primeFactors id hT).trans b.prod_primeFactors_dvd
  have hsum : (∑ p ∈ T,Real.log p) ≤ L := by
    have he : Real.log ((∏ p ∈ T,p : ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
      rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
    rw [← he]
    exact (Real.log_le_log hprod0 (by exact_mod_cast Nat.le_of_dvd hb hdvd)).trans hbL
  calc
    _ ≤ ∏ p ∈ T,Real.exp (4*Real.log p/L) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (1:ℝ)<p := by exact_mod_cast (hprimes p hp).one_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp
        exact totient_factor_large_prime (hprimes p hp) hL (hlarge p hp)
    _ = Real.exp ((4/L)*(∑ p ∈ T,Real.log p)) := by
      rw [← Real.exp_sum,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsum (show 0≤4/L by positivity)
      have he : (4/L)*L=4 := by field_simp
      rwa [he] at hh

/-- Uniformity in `b ≤ x` is the form needed when summing shifted prime pairs. -/
theorem totient_ratio_loglog_bound : ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, Real.exp 2 ≤ x →
    ∀ b : ℕ, 0<b → (b:ℝ)≤x → (b:ℝ)/b.totient ≤ C*Real.log (Real.log x) := by
  classical
  obtain ⟨C,hC,hM⟩ := mertensProductInput
  refine ⟨C*Real.exp 4,by positivity,?_⟩
  intro x hx b hb hbx
  have hx0 : 0<x := (Real.exp_pos 2).trans_le hx
  have hlog : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hN : 2 ≤ ⌊Real.log x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hlog
  let S := b.primeFactors.filter (fun p : ℕ => (p:ℝ)≤Real.log x)
  let T := b.primeFactors.filter (fun p : ℕ => ¬(p:ℝ)≤Real.log x)
  have hsmall : (∏ p ∈ S,(p:ℝ)/(p-1)) ≤ primeEulerProduct ⌊Real.log x⌋₊ := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      obtain ⟨hpb,hpL⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hpb).two_le,Nat.le_floor hpL⟩,
        Nat.prime_of_mem_primeFactors hpb⟩
    · intro p hp
      have hp1 : (1:ℝ)<p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp _
      have hp1 : (1:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
      apply (le_div_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
      linarith
  have hlarge : (∏ p ∈ T,(p:ℝ)/(p-1)) ≤ Real.exp 4 :=
    totient_large_prime_product hb (by linarith)
      (Real.log_le_log (by exact_mod_cast hb) hbx) T (Finset.filter_subset _ _)
      (fun p hp => (le_of_not_ge (Finset.mem_filter.mp hp).2))
  have hsmall0 : 0 ≤ ∏ p ∈ S,(p:ℝ)/(p-1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1:ℝ)<p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplit : (b:ℝ)/b.totient =
      (∏ p ∈ S,(p:ℝ)/(p-1))*(∏ p ∈ T,(p:ℝ)/(p-1)) := by
    rw [totient_ratio_product hb]
    exact (Finset.prod_filter_mul_prod_filter_not b.primeFactors
      (fun p : ℕ => (p:ℝ)≤Real.log x) (fun p => (p:ℝ)/(p-1))).symm
  have hlN : Real.log (⌊Real.log x⌋₊:ℝ) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by exact_mod_cast (show 0<⌊Real.log x⌋₊ by omega))
      (Nat.floor_le (by linarith))
  calc
    (b:ℝ)/b.totient = _ := hsplit
    _ ≤ primeEulerProduct ⌊Real.log x⌋₊ * Real.exp 4 :=
      mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp => by
        have hp1 : (1:ℝ)<p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)))
        (primeEulerProduct_pos _).le
    _ ≤ (C*Real.log (⌊Real.log x⌋₊:ℝ))*Real.exp 4 :=
      mul_le_mul_of_nonneg_right (hM _ hN) (Real.exp_pos _).le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hlN (show 0≤C*Real.exp 4 by positivity)
      nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedPrimePairBound
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-linear-form upper bound with all Selberg quantities eliminated. -/
noncomputable section
open scoped BigOperators
open SelbergSieve
namespace TotientAsymptotic

 theorem shiftedPrimePairs_log_bound {b : ℕ} (hb : 0<b) (X z : ℕ)
    (y : ℝ) (hy : 1<y) (hz : 2≤z)
    (hscale : 8*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    ((shiftedPrimePairs b X z).card:ℝ) ≤
      8*X*((b:ℝ)/b.totient)/(Real.log z)^2+2*y^3 := by
  let s := shiftedPrimeSieve b X z y hy.le
  let P := ∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p)
  let R : ℝ := (b:ℝ)/b.totient
  have hR : 0≤R := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hD : 0 < selbergBoundingSum s := selbergBoundingSum_pos s
  have hlog : 0<Real.log z := Real.log_pos (by exact_mod_cast (show 1<z by omega))
  have hP : P/2 ≤ selbergBoundingSum s := shiftedSieveBoundingSum_lower b X z y hy hz hscale
  have hprod : (Real.log z)^2/4 ≤ P*R := shiftedSieveEulerProduct_lower hb z hz
  have hden : (Real.log z)^2 ≤ 8*selbergBoundingSum s*R := by
    have hh := mul_le_mul_of_nonneg_right hP hR
    nlinarith
  have hmain : (X:ℝ)/selbergBoundingSum s ≤ 8*X*R/(Real.log z)^2 := by
    apply (div_le_div_iff₀ hD (sq_pos_of_pos hlog)).mpr
    have hh := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg X : (0:ℝ)≤X)
    nlinarith
  exact (shiftedPrimePairs_bound b X z y hy.le).trans (add_le_add hmain le_rfl)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllShiftedPrimePairs
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the small primes removed by the sieve cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma allShiftedPrimePairs_card_le (b X : ℕ) : (allShiftedPrimePairs b X).card ≤ X := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun q => q.Prime ∧ (b*q+1).Prime) (Finset.Icc 1 X))
  simpa [allShiftedPrimePairs] using h

lemma allShiftedPrimePairs_cutoff {b : ℕ} (hb : 0<b) (X z : ℕ) :
    (allShiftedPrimePairs b X).card ≤ (shiftedPrimePairs b X z).card+z := by
  classical
  have hsub : allShiftedPrimePairs b X ⊆ shiftedPrimePairs b X z ∪ Finset.Icc 1 z := by
    intro q hq
    obtain ⟨hqX,hqp,hbq⟩ := Finset.mem_filter.mp hq
    by_cases hqz : q≤z
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hqX).1,hqz⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hqX,hqp,hbq,by omega,?_⟩
      have hq : q≤b*q := by simpa using Nat.mul_le_mul_right q hb
      omega
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa using h

lemma totient_ratio_one_le {b : ℕ} (hb : 0<b) : (1:ℝ)≤(b:ℝ)/b.totient := by
  have hφ : (0:ℝ)<b.totient := by exact_mod_cast Nat.totient_pos.mpr hb
  apply (le_div_iff₀ hφ).mpr
  simpa using (show (b.totient:ℝ)≤b by exact_mod_cast Nat.totient_le b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SieveCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit small-power cutoffs for the two-linear-form sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma shiftedPrimeCutoff_bounds {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    2 ≤ shiftedPrimeCutoff L ∧
    L/(256*Real.log 4) ≤ Real.log (shiftedPrimeCutoff L) ∧
    Real.log (shiftedPrimeCutoff L) ≤ L/(128*Real.log 4) ∧
    (shiftedPrimeCutoff L:ℝ) ≤ Real.exp (3*L/4) := by
  have hc : 1 ≤ Real.log 4 := by
    have h := Real.log_two_gt_d9
    have he : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    linarith
  have hL0 : 0<L := by nlinarith
  have hd : 0<128*Real.log 4 := by positivity
  have hu : 4 ≤ L/(128*Real.log 4) := (le_div_iff₀ hd).mpr (by nlinarith)
  have he2 : (2:ℝ) ≤ Real.exp (L/(128*Real.log 4)) := by
    have hh := Real.add_one_le_exp (L/(128*Real.log 4))
    linarith
  have hz : 2 ≤ shiftedPrimeCutoff L := (Nat.le_floor_iff (by positivity)).mpr he2
  have hz0 : (0:ℝ) < shiftedPrimeCutoff L := by exact_mod_cast (show 0 < shiftedPrimeCutoff L by omega)
  have hfloor := Nat.sub_one_lt_floor (Real.exp (L/(128*Real.log 4)))
  have hhalf : Real.exp (L/(128*Real.log 4))/2 ≤ (shiftedPrimeCutoff L:ℝ) := by
    dsimp [shiftedPrimeCutoff]
    linarith
  have hlower := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp] at hlower
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this
    exact this
  have hfrac : L/(256*Real.log 4) = (L/(128*Real.log 4))/2 := by ring
  refine ⟨hz,?_,?_,?_⟩
  · rw [hfrac]
    linarith
  · have hh := Real.log_le_log hz0 (Nat.floor_le (Real.exp_pos _).le)
    simpa only [Real.log_exp] using hh
  · apply (Nat.floor_le (Real.exp_pos _).le).trans
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith

lemma shiftedPrimeCutoff_scale {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    8*Real.log 4*(2+Real.log (shiftedPrimeCutoff L)) ≤
      Real.log (Real.exp (L/4)) := by
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hh := (shiftedPrimeCutoff_bounds hL).2.2.1
  have hm := mul_le_mul_of_nonneg_left hh (show 0≤8*Real.log 4 by positivity)
  have he : 8*Real.log 4*(L/(128*Real.log 4))=L/16 := by field_simp <;> ring
  rw [he] at hm
  rw [Real.log_exp]
  nlinarith

lemma shiftedPrimeCutoff_error {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    (shiftedPrimeCutoff L:ℝ)+2*(Real.exp (L/4))^3 ≤
      96*Real.exp L/L^2 := by
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0<L := by nlinarith
  have he : (Real.exp (L/4))^3 = Real.exp (3*L/4) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hquad := Real.quadratic_le_exp_of_nonneg (by positivity : 0≤L/4)
  have hsmall : L^2 ≤ 32*Real.exp (L/4) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (3*L/4)).le
  have hsum : Real.exp (L/4)*Real.exp (3*L/4)=Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  have hbound : 3*Real.exp (3*L/4) ≤ 96*Real.exp L/L^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL0)).mpr
    rw [mul_assoc,hsum] at hm
    nlinarith
  rw [he]
  exact (by linarith [(shiftedPrimeCutoff_bounds hL).2.2.2] :
    (shiftedPrimeCutoff L:ℝ)+2*Real.exp (3*L/4) ≤ 3*Real.exp (3*L/4)).trans hbound

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrimePairBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform elementary upper-bound sieve for q and bq+1. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma allShiftedPrimePairs_large_bound {b X : ℕ} (hb : 0<b)
    (hX : 512*Real.log 4 ≤ Real.log X) :
    ((allShiftedPrimePairs b X).card:ℝ) ≤
      (8*(256*Real.log 4)^2+96)*X*((b:ℝ)/b.totient)/(Real.log X)^2 := by
  let L := Real.log (X:ℝ)
  let d := 256*Real.log (4:ℝ)
  let R : ℝ := (b:ℝ)/b.totient
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hd : 0<d := by dsimp [d] <;> positivity
  have hL : 0<L := by dsimp [L] <;> nlinarith
  have hX0 : (0:ℝ)<X := zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL)
  have hR : 1≤R := totient_ratio_one_le hb
  have hz := shiftedPrimeCutoff_bounds hX
  have hy : 1<Real.exp (L/4) := Real.one_lt_exp_iff.mpr (by positivity)
  have hp := shiftedPrimePairs_log_bound hb X (shiftedPrimeCutoff L)
    (Real.exp (L/4)) hy hz.1 (shiftedPrimeCutoff_scale hX)
  have hcard : ((allShiftedPrimePairs b X).card:ℝ) ≤
      (shiftedPrimePairs b X (shiftedPrimeCutoff L)).card+shiftedPrimeCutoff L := by
    exact_mod_cast allShiftedPrimePairs_cutoff hb X (shiftedPrimeCutoff L)
  have hmain : 8*X*R/(Real.log (shiftedPrimeCutoff L))^2 ≤ 8*d^2*X*R/L^2 := by
    calc
      _ ≤ 8*X*R/(L/d)^2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos (by positivity)) (pow_le_pow_left₀ (by positivity) hz.2.1 2)
      _ = _ := by field_simp
  have herr := shiftedPrimeCutoff_error hX
  rw [Real.exp_log hX0] at herr
  have herr' : 96*(X:ℝ)/L^2 ≤ 96*X*R/L^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  calc
    ((allShiftedPrimePairs b X).card:ℝ) ≤
        8*X*R/(Real.log (shiftedPrimeCutoff L))^2+
          (shiftedPrimeCutoff L+2*(Real.exp (L/4))^3) := by linarith
    _ ≤ 8*d^2*X*R/L^2+96*X*R/L^2 := add_le_add hmain (herr.trans herr')
    _ = _ := by dsimp [L,d,R] <;> ring

/-- Uniform in the positive coefficient b; no analytic input is assumed. -/
theorem uniform_prime_pair_bound : ∃ C : ℝ, 0<C ∧ ∀ b : ℕ, 0<b →
    ∀ X : ℕ, 2≤X → ((allShiftedPrimePairs b X).card:ℝ) ≤
      C*X*((b:ℝ)/b.totient)/(Real.log X)^2 := by
  let K := 512*Real.log (4:ℝ)
  let A := 8*(256*Real.log (4:ℝ))^2+96
  have hA : 0<A := by dsimp [A] <;> positivity
  have hK : 0<K := by dsimp [K] <;> positivity
  refine ⟨A+K^2,by positivity,?_⟩
  intro b hb X hX
  have hL : 0<Real.log X := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hR : 1≤(b:ℝ)/b.totient := totient_ratio_one_le hb
  by_cases hlarge : K≤Real.log X
  · apply (allShiftedPrimePairs_large_bound hb hlarge).trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hpos : 0≤(X:ℝ)*((b:ℝ)/b.totient) := by positivity
    nlinarith [mul_nonneg (sq_nonneg K) hpos]
  · have hcard : ((allShiftedPrimePairs b X).card:ℝ)≤X := by
      exact_mod_cast allShiftedPrimePairs_card_le b X
    apply hcard.trans
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hsq : (Real.log X)^2≤K^2 := pow_le_pow_left₀ hL.le (le_of_not_ge hlarge) 2
    have h1 := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg X : (0:ℝ)≤X)
    have h2 := mul_le_mul_of_nonneg_left hR (show 0≤(A+K^2)*X by positivity)
    nlinarith [mul_nonneg hA.le (Nat.cast_nonneg X : (0:ℝ)≤X)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorPrimePairMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the uniform prime-pair sieve over a specified cofactor family. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma cofactor_prime_pair_mass : ∃ C : ℝ, 0 < C ∧ ∀ x L : ℝ,
    Real.exp 2 ≤ x → 0 < L → ∀ Q : Finset ℕ,
    (∀ b ∈ Q,0 < b ∧ (b:ℝ) ≤ x ∧ 2 ≤ ⌊x/b⌋₊ ∧ L ≤ Real.log (⌊x/b⌋₊:ℝ)) →
    (∑ b ∈ Q,((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ)) ≤
      C*x*B x/L^2*(∑ b ∈ Q,(b:ℝ)⁻¹) := by
  obtain ⟨C,hC,hpair⟩ := uniform_prime_pair_bound
  obtain ⟨D,hD,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨C*D,by positivity,?_⟩
  intro x L hx hL Q hQ
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlogx : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hB : 0 ≤ B x := Real.log_nonneg (by linarith)
  have hterm (b : ℕ) (hb : b ∈ Q) :
      ((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ) ≤ C*D*x*B x/L^2*(b:ℝ)⁻¹ := by
    obtain ⟨hb0,hbx,hX,hXL⟩ := hQ b hb
    have hbR : (0:ℝ) < b := by exact_mod_cast hb0
    have hfloor : (⌊x/b⌋₊:ℝ) ≤ x/b := Nat.floor_le (div_nonneg hx0.le hbR.le)
    have hrat : (b:ℝ)/b.totient ≤ D*B x := hratio x hx b hb0 hbx
    have hrat0 : 0 ≤ (b:ℝ)/b.totient := by positivity
    have hlogX : 0 < Real.log (⌊x/b⌋₊:ℝ) := hL.trans_le hXL
    calc
      _ ≤ C*(⌊x/b⌋₊:ℝ)*((b:ℝ)/b.totient)/(Real.log (⌊x/b⌋₊:ℝ))^2 :=
        hpair b hb0 _ hX
      _ ≤ C*(x/b)*(D*B x)/L^2 := by
        apply div_le_div₀
        · positivity
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hfloor hC.le) hrat hrat0
            (by positivity)
        · exact sq_pos_of_pos hL
        · exact pow_le_pow_left₀ hL.le hXL 2
      _ = _ := by ring
  calc
    _ ≤ ∑ b ∈ Q,C*D*x*B x/L^2*(b:ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = _ := (Finset.mul_sum ..).symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorSieveCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic endpoint for the cofactor prime-pair sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma floor_log_endpoint {L z : ℝ} (hL : 1 ≤ L) (hz : Real.exp (2*L) ≤ z) :
    2 ≤ ⌊z⌋₊ ∧ L ≤ Real.log (⌊z⌋₊:ℝ) := by
  have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hz0 : 0 ≤ z := (Real.exp_pos _).le.trans hz
  have htwo : 2*Real.exp L ≤ z := by
    have heq : Real.exp (2*L) = (Real.exp L)^2 := by
      rw [show 2*L=L+L by ring,Real.exp_add,pow_two]
    rw [heq] at hz
    nlinarith
  have hf := Nat.lt_floor_add_one z
  have heFloor : Real.exp L ≤ (⌊z⌋₊:ℝ) := by linarith
  have hN : 2 ≤ ⌊z⌋₊ := by exact_mod_cast he.trans heFloor
  refine ⟨hN,?_⟩
  exact (Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < ⌊z⌋₊ by omega))).mpr heFloor

lemma cofactor_sieve_cutoff_mass_oai : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
    Real.exp 2 ≤ x → 0 < B x → 1 ≤ Real.log x/(200*B x) → ∀ Q : Finset ℕ,
    (∀ b ∈ Q,0 < b ∧ (b:ℝ)*Real.exp (Real.log x/(100*B x)) ≤ x) →
    (∑ b ∈ Q,((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ)) ≤
      C*x*(B x)^3/(Real.log x)^2*(∑ b ∈ Q,(b:ℝ)⁻¹) := by
  obtain ⟨C,hC,hbound⟩ := cofactor_prime_pair_mass
  refine ⟨40000*C,by positivity,?_⟩
  intro x hx hB hL Q hQ
  let L := Real.log x/(200*B x)
  have hL0 : 0 < L := by dsimp [L] <;> linarith
  have hQ' : ∀ b ∈ Q,0 < b ∧ (b:ℝ) ≤ x ∧ 2 ≤ ⌊x/b⌋₊ ∧ L ≤ Real.log (⌊x/b⌋₊:ℝ) := by
    intro b hb
    obtain ⟨hb0,hbc⟩ := hQ b hb
    have hbR : (0:ℝ) < b := by exact_mod_cast hb0
    have hcut : Real.exp (2*L) ≤ x/b := by
      apply (le_div_iff₀ hbR).mpr
      rw [show 2*L=Real.log x/(100*B x) by dsimp [L]; ring,mul_comm]
      exact hbc
    have hf := floor_log_endpoint hL hcut
    have hbx : (b:ℝ) ≤ x := by
      have he : 1 ≤ Real.exp (2*L) := Real.one_le_exp (by positivity)
      have hh := mul_le_mul_of_nonneg_left he hbR.le
      have hbc' := (le_div_iff₀ hbR).mp hcut
      nlinarith
    exact ⟨hb0,hbx,hf⟩
  have hh := hbound x L hx hL0 Q hQ'
  have hlog : 0 < Real.log x := by
    have hx0 := (Real.exp_pos 2).trans_le hx
    have ht := (Real.le_log_iff_exp_le hx0).mpr hx
    linarith
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [L]
  field_simp [ne_of_gt hB,ne_of_gt hlog]
  ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass_oai := @OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass_oai
