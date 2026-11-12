-- Prove2me | solution 1 for OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:51:03.142572+00:00
-- url     : https://prove2.me/submissions/c75e7b3d-1111-4c3d-ac6d-7ba82c770524

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J001
import Definitions.Def_OAIQ247J002
import Definitions.Def_OAIQ247J005
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_actual_biquadratic_rectangle_span_jb247
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_characterField_changeLevel_discr_natAbs_jb247
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_exists_classical_near_one_zero_unique_real_simple_jb247
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_local_bounds_jb247
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_source_given_determinant_finite_lower_of_real_zero_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
/-- Mathlib d13f23b's `Int.sq_emod_four`: an integer square is `0` or `1` mod 4, according to parity. -/
theorem _root_.Int.sq_emod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases h with h | h | h | h <;>
    simp [pow_two, Int.mul_emod, h] <;> omega

/-- Mathlib d13f23b's `Int.squarefree_iff_prime_sq_not_dvd`. -/
theorem _root_.Int.squarefree_iff_prime_sq_not_dvd {n : ℤ} :
    Squarefree n ↔ ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ 2 ∣ n) := by
  rw [← Int.squarefree_natAbs, Nat.squarefree_iff_prime_squarefree]
  refine forall_congr' fun p => imp_congr_right fun hp => not_congr ?_
  rw [pow_two, ← Nat.cast_mul, Int.natCast_dvd]

theorem _root_.Int.isFundamentalDiscr_iff_squarefree {D : ℤ} :
    Int.IsFundamentalDiscr D ↔
      (D % 4 = 1 ∧ Squarefree D) ∨ ∃ d : ℤ, D = 4 * d ∧ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) :=
  Iff.rfl

theorem _root_.Int.isFundamentalDiscr_four_mul {d : ℤ} :
    Int.IsFundamentalDiscr (4 * d) ↔ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) := by
  constructor
  · rintro (⟨h, _⟩ | ⟨e, he, hs, h⟩)
    · omega
    · have : e = d := by omega
      subst this; exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact Or.inr ⟨d, rfl, hs, h⟩

end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_IntegerCharacter
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace WeightedTorusJets

theorem primitive_eighth_root_difference_sq {K : Type*} [Field K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 8) : (ζ - ζ ^ 3) ^ 2 = 2 := by
  have h4 : ζ ^ 4 = -1 := by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    simpa using hζ.pow_of_dvd (by decide : (4 : ℕ) ≠ 0) (by decide : (4 : ℕ) ∣ 8)
  linear_combination (ζ ^ 2 - 2) * h4

end WeightedTorusJets

open scoped Pointwise

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SqrtPairFrobeniusDirections
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField

open scoped NumberField

namespace WeightedTorusJets



theorem not_isSquare_rat_two : ¬ IsSquare (2 : ℚ) := by
  norm_num



theorem real_character_inv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  apply MulChar.ext'
  intro a
  exact Complex.conj_eq_iff_im.mpr (hreal a)

theorem real_character_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  calc
    χ ^ 2 = χ⁻¹ * χ := by rw [pow_two, real_character_inv χ hreal]
    _ = 1 := inv_mul_cancel χ



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero

attribute [local instance] canonicalCyclotomicExtension

attribute [local instance] canonicalCyclotomicNumberField

attribute [local instance] canonicalCyclotomicAbelian



open NumberField IsCyclotomicExtension.Rat

end WeightedTorusJets

open scoped NumberField

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_QuadraticAdjoinBasis
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets

open Module NumberField

theorem trace_norm_quadratic_basis {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.trace ℚ K ((r : K) + s * a) = 2 * r ∧
      Algebra.norm ℚ ((r : K) + s * a) = r ^ 2 - d * s ^ 2 := by
  have hu0 : u 0 = 1 := congrFun hu 0
  have hu1 : u 1 = a := congrFun hu 1
  have hr0 : u.repr 1 = Finsupp.single 0 1 := by rw [← hu0, u.repr_self]
  have hr1 : u.repr a = Finsupp.single 1 1 := by rw [← hu1, u.repr_self]
  have hrc (c : ℚ) : u.repr (c : K) = c • Finsupp.single 0 1 := by
    simpa [Algebra.smul_def, hr0] using u.repr.map_smul c (1 : K)
  have hm0 : ((r : K) + s * a) * 1 = r • (1 : K) + s • a := by
    simp [Algebra.smul_def]
  have hm1 : ((r : K) + s * a) * a = (d * s) • (1 : K) + r • a := by
    calc
      _ = (s : K) * a ^ 2 + r * a := by ring
      _ = _ := by rw [ha]; simp [Algebra.smul_def, mul_comm]
  have hmat : Algebra.leftMulMatrix u ((r : K) + s * a) = !![r, d*s; s,r] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j
    all_goals simp [-Rat.cast_mul, hu0, hu1, hm0, hm1, hrc, hr1]
  rw [Algebra.trace_eq_matrix_trace u, Algebra.norm_eq_matrix_det u, hmat]
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_succ]
  constructor <;> ring

theorem rat_int_of_squarefree_mul_sq_eq_int (d n : ℤ) (hd : Squarefree d)
    (x : ℚ) (hx : (d : ℚ) * x ^ 2 = n) : ∃ m : ℤ, x = m := by
  have heq : d * x.num ^ 2 = n * (x.den : ℤ) ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← x.num_div_den] at hx
    have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    field_simp at hx
    nlinarith [hx]
  have hdiv : (x.den : ℤ) * (x.den : ℤ) ∣ d * x.num ^ 2 := by
    rw [heq, ← pow_two]
    exact dvd_mul_left _ _
  have hden := hd.dvd_of_squarefree_of_mul_dvd_mul_right hdiv
  have hden_nat : x.den ∣ x.num.natAbs ^ 2 := by
    simpa only [Int.natCast_dvd, Int.natAbs_pow] using hden
  have hone : x.den = 1 := Nat.eq_one_of_dvd_coprimes (x.reduced.pow_left 2)
    hden_nat (dvd_refl _)
  exact ⟨x.num, ((Rat.den_eq_one_iff x).mp hone).symm⟩

theorem integral_quadratic_half_coordinates {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ) (r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hx : IsIntegral ℤ ((r : K) + s * a)) :
    ∃ m k : ℤ, 2 * r = m ∧ 2 * s = k ∧ 4 ∣ m ^ 2 - d * k ^ 2 := by
  obtain ⟨ht, hn⟩ := trace_norm_quadratic_basis u a (d : ℚ) r s hu (by simpa using ha)
  have hit : IsIntegral ℤ (2 * r) := ht ▸ Algebra.isIntegral_trace hx
  have hin : IsIntegral ℤ (r ^ 2 - (d : ℚ) * s ^ 2) := hn ▸ Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hit
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hin
  change (m : ℚ) = 2 * r at hm
  change (n : ℚ) = r ^ 2 - (d : ℚ) * s ^ 2 at hn
  have hsq : (d : ℚ) * (2 * s) ^ 2 = (m ^ 2 - 4 * n : ℤ) := by
    push_cast
    rw [hm, hn]
    ring
  obtain ⟨k, hk⟩ := rat_int_of_squarefree_mul_sq_eq_int d (m ^ 2 - 4 * n) hd (2 * s) hsq
  refine ⟨m, k, hm.symm, hk, n, ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, ← hk, hn]
  ring

theorem even_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 2 ∨ d % 4 = 3)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even m ∧ Even k := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four] at heq
  simp only [Int.even_iff]
  rcases hd with hd | hd <;> rw [hd] at heq <;> omega

theorem even_sub_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 1)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even (m - k) := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four, hd] at heq
  simp only [Int.even_iff]
  omega

theorem integral_quadratic_eq_int_add_int_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * a := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨hm2, hk2⟩ := even_coordinates_of_four_dvd d m k hd4 hmk
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp hm2
  obtain ⟨j, hj⟩ := even_iff_two_dvd.mp hk2
  have hri : r = (i : ℚ) := by
    have hi' : (m : ℚ) = 2 * i := by exact_mod_cast hi
    linarith
  have hsj : s = (j : ℚ) := by
    have hj' : (k : ℚ) = 2 * j := by exact_mod_cast hj
    linarith
  refine ⟨i, j, ?_⟩
  rw [← hrep, hri, hsj]
  norm_cast

theorem integral_quadratic_eq_int_add_int_mul_half {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * ((1 + a) / 2) := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp (even_sub_coordinates_of_four_dvd d m k hd4 hmk)
  have hri : r = (i : ℚ) + (k : ℚ) / 2 := by
    have hi' : (m : ℚ) - k = 2 * i := by exact_mod_cast hi
    linarith
  have hsk : s = (k : ℚ) / 2 := by linarith
  refine ⟨i, k, ?_⟩
  rw [← hrep, hri, hsk]
  push_cast
  ring

theorem integral_quadratic_half_generator {K : Type*} [Field K] [CharZero K]
    (a : K) (d : ℤ) (ha : a ^ 2 = d) (hd : d % 4 = 1) :
    IsIntegral ℤ ((1 + a) / 2) := by
  have hdv : d = 4 * (d / 4) + 1 := by omega
  refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4)),
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X_add_C]; norm_num), ?_⟩
  change Polynomial.aeval ((1 + a) / 2)
    (Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4))) = 0
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_add, Polynomial.aeval_C]
  have hdK : (d : K) = 4 * ((d / 4 : ℤ) : K) + 1 := by exact_mod_cast hdv
  field_simp
  linear_combination ha + hdK

theorem exists_ringOfIntegers_pair_basis {K : Type*} [Field K] [NumberField K]
    (w : K) (hw : IsIntegral ℤ w) (hdim : Module.finrank ℚ K = 2)
    (hspan : ∀ x : K, IsIntegral ℤ x → ∃ m n : ℤ, x = m + n * w) :
    ∃ B : Basis (Fin 2) ℤ (𝓞 K),
      (fun i => ((B i : 𝓞 K) : K)) = ![1, w] := by
  let W : 𝓞 K := ⟨w, hw⟩
  let v : Fin 2 → 𝓞 K := ![1, W]
  have hs : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x _
    obtain ⟨m, n, hmn⟩ := hspan x x.property
    have hmn' : x = m • (1 : 𝓞 K) + n • W := by
      apply RingOfIntegers.ext
      change (x : K) = algebraMap (𝓞 K) K (m • (1 : 𝓞 K) + n • W)
      rw [map_add, map_zsmul, map_zsmul, map_one]
      change (x : K) = m • (1 : K) + n • w
      simpa [Algebra.smul_def] using hmn
    rw [hmn']
    exact Submodule.add_mem _
      (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩))
  have hc : Fintype.card (Fin 2) = Module.finrank ℤ (𝓞 K) := by
    simpa [RingOfIntegers.rank] using hdim.symm
  let B : Basis (Fin 2) ℤ (𝓞 K) := basisOfTopLeSpanOfCardEqFinrank v hs hc
  refine ⟨B, ?_⟩
  ext i
  fin_cases i <;> simp [B, v, W]
  rfl

theorem discr_quadratic_pair {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.discr ℚ ![1, (r : K) + s * a] = 4 * d * s ^ 2 := by
  have ht := (trace_norm_quadratic_basis u a d r s hu ha).1
  have ht1 : Algebra.trace ℚ K 1 = 2 := by
    simpa using Algebra.trace_algebraMap_of_basis u (1 : ℚ)
  have hww : ((r : K) + s * a) * ((r : K) + s * a) =
      ((r ^ 2 + d * s ^ 2 : ℚ) : K) + ((2 * r * s : ℚ) : K) * a := by
    push_cast
    linear_combination (s : K) ^ 2 * ha
  have htww : Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) =
      2 * (r ^ 2 + d * s ^ 2) := by
    rw [hww]
    exact (trace_norm_quadratic_basis u a d (r ^ 2 + d * s ^ 2) (2 * r * s) hu ha).1
  rw [Algebra.discr_def, Matrix.det_fin_two]
  change Algebra.trace ℚ K (1 * 1) *
      Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) -
    Algebra.trace ℚ K (1 * ((r : K) + s * a)) *
      Algebra.trace ℚ K (((r : K) + s * a) * 1) = _
  rw [one_mul, one_mul, mul_one, ht, ht1, htww]
  ring

theorem coe_discr_eq_pair_of_integer_basis {K : Type*} [Field K] [NumberField K]
    (B : Basis (Fin 2) ℤ (𝓞 K)) (w : K)
    (hB : (fun i => ((B i : 𝓞 K) : K)) = ![1, w]) :
    (NumberField.discr K : ℚ) = Algebra.discr ℚ ![1, w] := by
  rw [← NumberField.discr_eq_discr K B]
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ B) = _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K B]
  congr 1
  funext i
  rw [Basis.localizationLocalization_apply]
  exact congrFun hB i

theorem numberField_discr_quadratic_eq_four_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) : NumberField.discr K = 4 * d := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis a hai hdim
    (integral_quadratic_eq_int_add_int_mul u a d hu ha hd hd4)
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [coe_discr_eq_pair_of_integer_basis B a hB]
  simpa using discr_quadratic_pair u a (d : ℚ) 0 1 hu (by simpa using ha)

theorem numberField_discr_quadratic_eq_self {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) : NumberField.discr K = d := by
  have hwi := integral_quadratic_half_generator a d ha hd4
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis ((1 + a) / 2) hwi hdim
    (integral_quadratic_eq_int_add_int_mul_half u a d hu ha hd hd4)
  have hw : (1 + a) / 2 = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * a := by
    push_cast
    ring
  apply Int.cast_injective (α := ℚ)
  rw [coe_discr_eq_pair_of_integer_basis B ((1 + a) / 2) hB, hw,
    discr_quadratic_pair u a (d : ℚ) (1 / 2) (1 / 2) hu (by simpa using ha)]
  ring

theorem isFundamentalDiscr_quadratic {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    exact Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨hd1, hd⟩)
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    exact Int.isFundamentalDiscr_four_mul.mpr ⟨hd, hd4⟩

theorem isUnramifiedIn_two_iff_radical_mod_four {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1 := by
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K)
    ((Int.prime_iff_natAbs_prime (k := 2)).mpr Nat.prime_two)]
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    have hodd : ¬ (2 : ℤ) ∣ d := by
      rw [Int.dvd_iff_emod_eq_zero]
      omega
    simp [hodd, hd1]
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    have hdiv : (2 : ℤ) ∣ 4 * d := dvd_mul_of_dvd_left (by norm_num) d
    simp [hdiv, hd1]

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SumLogPrimeFactors
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology

namespace WeightedTorusJets



theorem exists_radius_LFunction_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, |β - 1| < ε →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  have hcont : ContinuousAt (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hnonzero : DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ) ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcont.eventually_ne hnonzero)
  refine ⟨ε, hε, fun β hβ => hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hβ

theorem exists_radius_LFunction_ne_zero_fixed_modulus (q : ℕ) [NeZero q] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, |β - 1| < ε → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  classical
  have h : ∀ᶠ β : ℝ in nhds 1, ∀ χ : DirichletCharacter ℂ q,
      χ ≠ 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro χ
    by_cases hχ : χ = 1
    · exact Filter.Eventually.of_forall fun _ hne => (hne hχ).elim
    · obtain ⟨ε, hε, hzero⟩ := exists_radius_LFunction_ne_zero χ hχ
      have hr : ∀ᶠ β : ℝ in nhds 1, |β - 1| < ε := by
        filter_upwards [Metric.ball_mem_nhds (1 : ℝ) hε] with β hβ
        simpa [Metric.mem_ball, Real.dist_eq] using hβ
      exact hr.mono fun β hβ _ => hzero β hβ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨ε, hε, fun χ hχ β hβ => hball ?_ χ hχ⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hβ

theorem exists_gap_fixed_modulus (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) → c ≤ (1 - β) * Real.log (q : ℝ) := by
  obtain ⟨ε, hε, hne⟩ := exists_radius_LFunction_ne_zero_fixed_modulus q
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  refine ⟨ε * Real.log (q : ℝ), mul_pos hε hlog, ?_⟩
  intro χ hχ β hβ
  apply mul_le_mul_of_nonneg_right _ hlog.le
  by_contra! hlt
  have habs : |β - 1| = 1 - β := by
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hβ.2.1)]
  exact hne χ hχ β (by simpa [habs] using hlt) hβ.2.2

theorem exists_gap_bounded_moduli (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≤ Q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) → c ≤ (1 - β) * Real.log (q : ℝ) := by
  induction Q with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro q _ hq hQ
    omega
  | succ Q ih =>
    obtain ⟨c, hc, hbound⟩ := ih
    by_cases hQ : 3 ≤ Q + 1
    · let : NeZero (Q + 1) := ⟨by omega⟩
      obtain ⟨d, hd, hlast⟩ := exists_gap_fixed_modulus (Q + 1) hQ
      refine ⟨min c d, lt_min hc hd, ?_⟩
      intro q _ hq hqQ χ hχ β hβ
      rcases Nat.lt_or_eq_of_le hqQ with hlt | rfl
      · exact (min_le_left _ _).trans (hbound q hq (by omega) χ hχ β hβ)
      · exact (min_le_right _ _).trans (hlast χ hχ β hβ)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro q _ hq hqQ
      omega

theorem exists_small_gap_large_modulus (hnot : ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
          (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
            (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
              c ≤ (1 - β) * Real.log (q : ℝ)))
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ hq : NeZero q, 3 ≤ q ∧ Q < q ∧
      ∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧ χ ≠ 1 ∧ (∀ a : ZMod q, (χ a).im = 0) ∧
        ∃ β : ℝ, (0 < β ∧ β < 1 ∧ @DirichletCharacter.LFunction q hq χ (β : ℂ) = 0) ∧
          (1 - β) * Real.log (q : ℝ) < ε := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_gap_bounded_moduli Q
  have hfail : ¬ (∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            min c ε ≤ (1 - β) * Real.log (q : ℝ)) := fun h =>
    hnot ⟨min c ε, lt_min hc hε, h⟩
  push Not at hfail
  obtain ⟨q, hq0, hq, χ, hprim, hχ, hreal, β, hβ, hsmall⟩ := hfail
  let := hq0
  have hQ : Q < q := by
    by_contra! hle
    exact (not_lt_of_ge (hbound q hq hle χ hχ β hβ))
      (hsmall.trans_le (min_le_left _ _))
  exact ⟨q, hq0, hq, hQ, χ, hprim, hχ, hreal, β, hβ,
    hsmall.trans_le (min_le_right _ _)⟩

theorem exists_contrary_sequence (hnot : ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
          (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
            (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
              c ≤ (1 - β) * Real.log (q : ℝ))) :
    ∃ q : ℕ → ℕ, ∃ hq : ∀ n, NeZero (q n),
      ∃ χ : ∀ n, DirichletCharacter ℂ (q n), ∃ β : ℕ → ℝ,
        (∀ n, 3 ≤ q n ∧ (χ n).IsPrimitive ∧ χ n ≠ 1 ∧ (∀ a : ZMod (q n), (χ n a).im = 0) ∧
          (0 < β n ∧ β n < 1 ∧ @DirichletCharacter.LFunction (q n) (hq n) (χ n) (β n : ℂ) = 0)) ∧
        Filter.Tendsto q Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => (1 - β n) * Real.log (q n : ℝ))
          Filter.atTop (nhds 0) := by
  classical
  have hex (n : ℕ) := exists_small_gap_large_modulus hnot n
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose q hq hq3 hn χ hprim hχ hreal β hβ hsmall using hex
  refine ⟨q, hq, χ, β, fun n => ⟨hq3 n, hprim n, hχ n, hreal n, hβ n⟩,
    Filter.tendsto_atTop_mono (fun n => (hn n).le) Filter.tendsto_id, ?_⟩
  refine squeeze_zero (fun n => ?_) (fun n => (hsmall n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact mul_nonneg (sub_nonneg.mpr (hβ n).2.1.le) (Real.log_natCast_nonneg (q n))

end WeightedTorusJets

end AnalyticAssemblyScope

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SqrtTwoField
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField

namespace WeightedTorusJets

open NumberField

theorem quadraticAdjoin_discriminant {L : Type*} [Field L] [NumberField L]
    (a : L) (d : ℤ) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hns : ¬ IsSquare (d : ℚ)) :
    NumberField.discr (IntermediateField.adjoin ℚ {a}) =
      (if d % 4 = 1 then d else 4 * d) ∧
    Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
    (Algebra.IsUnramifiedIn (𝓞 (IntermediateField.adjoin ℚ {a}))
      (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1) := by
  let F := IntermediateField.adjoin ℚ {a}
  let A : F := IntermediateField.AdjoinSimple.gen ℚ a
  have hroot : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hi : IsIntegral ℚ a := IsIntegral.of_pow (by decide : 0 < 2)
    (hroot ▸ isIntegral_algebraMap)
  have hdim := finrank_adjoin_sqrt a (d : ℚ) hroot hns
  let u : Module.Basis (Fin 2) ℚ F := quadraticAdjoinBasis a hi hdim
  have hu : (u : Fin 2 → F) = ![1, A] := by
    funext i
    exact quadraticAdjoinBasis_apply a hi hdim i
  have hA : A ^ 2 = (d : F) := by
    apply Subtype.ext
    exact ha
  refine ⟨?_, isFundamentalDiscr_quadratic u A d hu hA hd,
    isUnramifiedIn_two_iff_radical_mod_four u A d hu hA hd⟩
  by_cases hd1 : d % 4 = 1
  · simp only [ite_eq_left hd1]
    exact numberField_discr_quadratic_eq_self u A d hu hA hd hd1
  · simp only [ite_eq_right hd1]
    have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    exact numberField_discr_quadratic_eq_four_mul u A d hu hA hd (by omega)



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

end WeightedTorusJets

namespace WeightedTorusJets

open IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem sourceSqrtTwoField_root_sq (q : ℕ) [NeZero (8 * q)]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L] :
    let ζ := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
    (ζ - ζ ^ 3) ^ 2 = 2 := by
  have h8m : 8 ∣ 8 * q := dvd_mul_right 8 q
  exact primitive_eighth_root_difference_sq
    ((zeta_spec (8 * q) ℚ L).pow (NeZero.pos (8 * q)) (Nat.div_mul_cancel h8m).symm)

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GreedyPivots
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
namespace WeightedTorusJets

theorem pivot_floor_square_bound {t : ℝ} (ht : 1 ≤ t) :
    ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2 ≤ 97 ^ 2 * t ^ 2 := by
  have hf := Nat.floor_le (show 0 ≤ 96 * t by positivity)
  have hupper : ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ≤ 97 * t := by
    push_cast
    linarith
  nlinarith [sq_nonneg (((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) - 97 * t)]

theorem pivot_second_sum_bound {ι : Type*} (s : Finset ι) (b c : ι → ℕ)
    {t : ℝ} (hb : ∀ i ∈ s, (b i : ℝ) ≤ 96 * t)
    (hc : ∀ i ∈ s, (c i : ℝ) ≤ 96 * t) :
    ∑ i ∈ s, ((b i : ℝ) + c i) ≤ 192 * s.card * t := by
  calc
    ∑ i ∈ s, ((b i : ℝ) + c i) ≤ ∑ _i ∈ s, (192 * t) :=
      Finset.sum_le_sum fun i hi => by linarith [hb i hi, hc i hi]
    _ = 192 * s.card * t := by simp <;> ring

theorem pivot_lower_bound_quarter {M Q S : ℝ} (hQ : 0 < Q) (hM : 2 * Q ≤ M)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) : M ^ 2 / (4 * Q) ≤ S := by
  have hnonneg : 0 ≤ M * (M - 2 * Q) := mul_nonneg (by linarith) (by linarith)
  have h : M ^ 2 / (4 * Q) ≤ M ^ 2 / (2 * Q) - M / 2 := by
    apply (div_le_iff₀ (show 0 < 4 * Q by positivity)).mpr
    field_simp
    nlinarith
  exact h.trans hS

theorem pivot_lower_constant {M Q H t S : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (hH : 0 < H) (hM : M = H * t ^ 3) (hMQ : 2 * Q ≤ M)
    (hQt : Q ≤ 97 ^ 2 * t ^ 2)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) :
    M * H * t / (4 * 97 ^ 2) ≤ S := by
  have hquarter := pivot_lower_bound_quarter hQ hMQ hS
  have hlower : M * H * t / (4 * 97 ^ 2) ≤ M ^ 2 / (4 * Q) := by
    apply (le_div_iff₀ (show 0 < 4 * Q by positivity)).mpr
    have hnonneg : 0 ≤ M * H * t := by rw [hM]; positivity
    have h := mul_le_mul_of_nonneg_left hQt hnonneg
    rw [hM] at h ⊢
    nlinarith
  exact hlower.trans hquarter

theorem pivot_scale_ge_one {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    1 ≤ H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ) := by
  have hHpos : 0 < H := by linarith
  calc
    1 ≤ H := hH
    _ = H ^ (-(1 / 3 : ℝ)) * H ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_add hHpos]
      norm_num
    _ ≤ H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hHpos.le _)
      exact Real.rpow_le_rpow hHpos.le hHN (by norm_num)

theorem pivot_dimension_eq_cube {N : ℝ} (hN : 0 ≤ N) :
    (N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
  norm_num

theorem pivot_scale_cube {H N : ℝ} (hH : 0 < H) (hN : 0 ≤ N) :
    H * (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
  rw [mul_pow, pivot_dimension_eq_cube hN, ← Real.rpow_natCast,
    ← Real.rpow_mul hH.le]
  norm_num
  rw [Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hH.ne']
  simp

theorem pivot_primary_scale {H U : ℝ} (hH : 0 < H) :
    H * (H ^ (-(1 / 3 : ℝ)) * U) = H ^ (2 / 3 : ℝ) * U := by
  rw [← mul_assoc]
  have hp := Real.rpow_add hH (1 : ℝ) (-(1 / 3 : ℝ))
  norm_num at hp
  rw [← hp]

theorem pivot_count_threshold {H t Q : ℝ} (hQ : Q ≤ 97 ^ 2 * t ^ 2)
    (hscale : 2 * 97 ^ 2 ≤ H * t) : 2 * Q ≤ H * t ^ 3 := by
  nlinarith [mul_le_mul_of_nonneg_right hscale (sq_nonneg t)]

theorem pivot_primary_scale_ge_N {H N : ℝ} (hH : 1 ≤ H) (hN : 1 ≤ N) :
    N ≤ H ^ (2 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
  have hHp : 1 ≤ H ^ (2 / 3 : ℝ) := Real.one_le_rpow hH (by norm_num)
  have hNp : N ≤ N ^ (4 / 3 : ℝ) := Real.self_le_rpow_of_one_le hN (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hHp (show 0 ≤ N ^ (4 / 3 : ℝ) by positivity)
  simp only [one_mul] at hprod
  exact hNp.trans hprod

theorem pivot_floor_count_eventually {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (hN : 18818 ≤ N) :
    2 * (((⌊96 * (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ))⌋₊ + 1 : ℕ) : ℝ) ^ 2)
      ≤ N ^ 4 := by
  have hHpos : 0 < H := by linarith
  have hNnonneg : 0 ≤ N := by linarith
  rw [← pivot_scale_cube hHpos hNnonneg]
  apply pivot_count_threshold (pivot_floor_square_bound (pivot_scale_ge_one hH hHN))
  rw [pivot_primary_scale hHpos]
  have h := pivot_primary_scale_ge_N hH (show 1 ≤ N by linarith)
  norm_num
  linarith

theorem pivot_coordinates_of_weight {H U : ℝ} (hH : 0 < H) (a b c : ℕ)
    (hw : (a : ℝ) + H * b + H * c ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    (b : ℝ) ≤ 96 * (H ^ (-(1 / 3 : ℝ)) * U) ∧
      (c : ℝ) ≤ 96 * (H ^ (-(1 / 3 : ℝ)) * U) := by
  have hs := pivot_primary_scale (U := U) hH
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : 0 ≤ H * b := mul_nonneg hH.le (Nat.cast_nonneg b)
  have hc : 0 ≤ H * c := mul_nonneg hH.le (Nat.cast_nonneg c)
  constructor
  · apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith

theorem pivot_weight_of_rectangle {H U : ℝ} (hH : 0 < H) (a b c : ℕ)
    (ha : (a : ℝ) ≤ 32 * H ^ (2 / 3 : ℝ) * U)
    (hb : (b : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U)
    (hc : (c : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U) :
    (a : ℝ) + H * b + H * c ≤ 96 * H ^ (2 / 3 : ℝ) * U := by
  have hs := pivot_primary_scale (U := U) hH
  have hbH := mul_le_mul_of_nonneg_left hb hH.le
  have hcH := mul_le_mul_of_nonneg_left hc hH.le
  nlinarith

end WeightedTorusJets

open scoped BigOperators

namespace WeightedTorusJets

theorem card_filter_lt_le_mul {ι : Type*} (s : Finset ι) (a : ι → ℕ) (Q t : ℕ)
    (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    (s.filter fun i => a i < t).card ≤ Q * t := by
  classical
  have h := Finset.card_le_mul_card_image_of_maps_to
    (s := s.filter fun i => a i < t) (t := Finset.range t) (f := a)
    (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2) Q
    (fun k _ => le_trans (Finset.card_le_card (by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1,
          (Finset.mem_filter.mp hi).2⟩)) (hQ k))
  simpa using h

theorem card_sq_le_twice_mul_sum_add {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (Q : ℕ) (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    s.card * s.card ≤ 2 * Q * (∑ i ∈ s, a i) + Q * s.card := by
  classical
  have hswap :
      (∑ i ∈ s, (s.filter fun j => a i < a j).card) =
        ∑ i ∈ s, (s.filter fun j => a j < a i).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hsplit : s.card * s.card =
      2 * (∑ i ∈ s, (s.filter fun j => a j < a i).card) +
        ∑ i ∈ s, (s.filter fun j => a j = a i).card := by
    calc
      s.card * s.card = ∑ i ∈ s, ∑ j ∈ s, (1 : ℕ) := by simp
      _ = ∑ i ∈ s, ∑ j ∈ s,
          ((if a j < a i then 1 else 0) + (if a i < a j then 1 else 0) +
            (if a j = a i then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> omega
      _ = (∑ i ∈ s, (s.filter fun j => a j < a i).card) +
          (∑ i ∈ s, (s.filter fun j => a i < a j).card) +
          ∑ i ∈ s, (s.filter fun j => a j = a i).card := by
        simp only [Finset.sum_add_distrib, ← Finset.card_filter]
      _ = _ := by rw [hswap]; omega
  have hlt : (∑ i ∈ s, (s.filter fun j => a j < a i).card) ≤
      Q * (∑ i ∈ s, a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => card_filter_lt_le_mul s a Q (a i) hQ
  have heq : (∑ i ∈ s, (s.filter fun j => a j = a i).card) ≤ Q * s.card := by
    calc
      _ ≤ ∑ i ∈ s, Q := Finset.sum_le_sum fun i _ => hQ (a i)
      _ = _ := by simp [mul_comm]
  nlinarith

theorem sum_lower_of_bounded_multiplicity {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (Q : ℕ) (hQpos : 0 < Q)
    (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    (s.card : ℝ) ^ 2 / (2 * Q) - s.card / 2 ≤ ∑ i ∈ s, (a i : ℝ) := by
  have h : (s.card : ℝ) * s.card ≤
      2 * (Q : ℝ) * (∑ i ∈ s, (a i : ℝ)) + (Q : ℝ) * s.card := by
    exact_mod_cast card_sq_le_twice_mul_sum_add s a Q hQ
  have hQpos' : (0 : ℝ) < Q := by exact_mod_cast hQpos
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Q)]
  nlinarith

theorem coordinate_fiber_card_le (s : Finset (Fin 3 → ℕ)) (B k : ℕ)
    (hB : ∀ a ∈ s, a 1 ≤ B ∧ a 2 ≤ B) :
    (s.filter fun a => a 0 = k).card ≤ (B + 1) ^ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn (s := s.filter fun a => a 0 = k)
    (t := Finset.range (B + 1) ×ˢ Finset.range (B + 1))
    (fun a => (a 1, a 2)) ?_ ?_
  · simpa [pow_two] using h
  · intro a ha
    have ha' := (Finset.mem_filter.mp ha).1
    obtain ⟨h1, h2⟩ := hB a ha'
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show a 1 < B + 1 by omega),
      Finset.mem_range.mpr (show a 2 < B + 1 by omega)⟩
  · intro a ha b hb hab
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    have ha1 := congrArg Prod.fst hab
    have ha2 := congrArg Prod.snd hab
    funext i
    fin_cases i <;> simp_all

theorem first_coordinate_sum_lower (s : Finset (Fin 3 → ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, a 1 ≤ B ∧ a 2 ≤ B) :
    (s.card : ℝ) ^ 2 / (2 * ((B + 1 : ℕ) : ℝ) ^ 2) - s.card / 2 ≤
      ∑ a ∈ s, (a 0 : ℝ) := by
  have h := sum_lower_of_bounded_multiplicity s (fun a => a 0) ((B + 1)^2)
    (by positivity) (coordinate_fiber_card_le s B · hB)
  simpa using h



theorem weighted_pivot_bounds (P : Finset (Fin 3 → ℕ)) (H N : ℕ)
    (hH : 0 < H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hcard : P.card = N ^ 4)
    (hw : ∀ a ∈ P, (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  let t : ℝ := (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNreal : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hNreal : (18818 : ℝ) ≤ N := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have htone : 1 ≤ t := pivot_scale_ge_one hHone hHNreal
  have htpos : 0 < t := by linarith
  have hcardreal : (P.card : ℝ) = (N : ℝ) ^ 4 := by exact_mod_cast hcard
  have hcoords : ∀ a ∈ P, (a 1 : ℝ) ≤ 96 * t ∧ (a 2 : ℝ) ≤ 96 * t := by
    intro a ha
    exact pivot_coordinates_of_weight hHpos (a 0) (a 1) (a 2) (hw a ha)
  have hcoordsNat : ∀ a ∈ P, a 1 ≤ ⌊96 * t⌋₊ ∧ a 2 ≤ ⌊96 * t⌋₊ := by
    intro a ha
    exact ⟨Nat.le_floor (hcoords a ha).1, Nat.le_floor (hcoords a ha).2⟩
  have hlower := first_coordinate_sum_lower P ⌊96 * t⌋₊ hcoordsNat
  have hlarge : 2 * (((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2) ≤ P.card := by
    rw [hcardreal]
    exact pivot_floor_count_eventually hHone hHNreal hNreal
  have hscale : (P.card : ℝ) = (H : ℝ) * t ^ 3 := by
    rw [hcardreal]
    exact (pivot_scale_cube hHpos hNnonneg).symm
  have hfirst := pivot_lower_constant
    (show 0 < ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2 by positivity)
    htpos hHpos hscale hlarge (pivot_floor_square_bound htone) hlower
  constructor
  · have hs := pivot_primary_scale (U := (N : ℝ) ^ (4 / 3 : ℝ)) hHpos
    change (H : ℝ) * t = _ at hs
    rw [hcardreal] at hfirst
    simpa only [mul_assoc, hs] using hfirst
  · have hsecond := pivot_second_sum_bound P (fun a => a 1) (fun a => a 2)
      (fun a ha => (hcoords a ha).1) (fun a ha => (hcoords a ha).2)
    rw [hcardreal] at hsecond
    simpa [t, mul_assoc] using hsecond



open Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem greedyPivots_subset_range (v : ℕ → V) (n : ℕ) :
    greedyPivots K v n ⊆ Finset.range n := by
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs
      · exact ih.trans (Finset.range_mono (Nat.le_succ n))
      · exact Finset.insert_subset (Finset.mem_range.mpr (Nat.lt_succ_self n))
          (ih.trans (Finset.range_mono (Nat.le_succ n)))

theorem span_greedyPivots (v : ℕ → V) (n : ℕ) :
    span K (v '' (greedyPivots K v n : Set ℕ)) =
      span K (v '' (Finset.range n : Set ℕ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs with h
      · rw [Finset.range_add_one, Finset.coe_insert, Set.image_insert_eq,
          span_insert_eq_span (ih ▸ h), ih]
      · rw [Finset.coe_insert, Finset.range_add_one, Finset.coe_insert,
          Set.image_insert_eq, Set.image_insert_eq, span_insert, span_insert, ih]

theorem mem_greedyPivots_succ_self (v : ℕ → V) (n : ℕ) :
    n ∈ greedyPivots K v (n + 1) ↔
      v n ∉ span K (v '' (Finset.range n : Set ℕ)) := by
  classical
  have hn : n ∉ greedyPivots K v n := fun h =>
    (Nat.lt_irrefl n) (Finset.mem_range.mp (greedyPivots_subset_range v n h))
  rw [greedyPivots, span_greedyPivots]
  split_ifs with h
  · exact iff_of_false hn (not_not_intro h)
  · exact iff_of_true (Finset.mem_insert_self _ _) h

theorem mem_greedyPivots_iff (v : ℕ → V) (i n : ℕ) :
    i ∈ greedyPivots K v n ↔
      i < n ∧ v i ∉ span K (v '' (Finset.range i : Set ℕ)) := by
  classical
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      by_cases hin : i < n
      · have hne : i ≠ n := Nat.ne_of_lt hin
        rw [greedyPivots]
        split_ifs
        · simpa only [hin, Nat.lt_succ_of_lt hin, true_and] using ih
        · simpa only [Finset.mem_insert, hne, false_or, hin,
            Nat.lt_succ_of_lt hin, true_and] using ih
      · by_cases hieq : i = n
        · subst i
          simpa only [Nat.lt_succ_self, true_and] using mem_greedyPivots_succ_self v n
        · have hnle : n + 1 ≤ i := by omega
          have hi : i ∉ greedyPivots K v (n + 1) := fun h =>
            (Nat.not_lt.mpr hnle)
              (Finset.mem_range.mp (greedyPivots_subset_range v (n + 1) h))
          exact iff_of_false hi (fun h => Nat.not_lt.mpr hnle h.1)

end WeightedTorusJets

namespace WeightedTorusJets

theorem monotone_extendFiniteFamily {α : Type*} [Preorder α] {n : ℕ}
    (f : Fin n → α) (fallback : α) (hf : Monotone f) (hb : ∀ i, f i ≤ fallback) :
    Monotone (extendFiniteFamily f fallback) := by
  intro i j hij
  simp only [extendFiniteFamily]
  split_ifs with hi hj hj
  · exact hf hij
  · exact hb _
  · exact (hi (lt_of_le_of_lt hij hj)).elim
  · exact le_rfl

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_WeightedJetIndices
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets

theorem mem_weightedJetIndices_iff {H B : ℕ} (hH : 0 < H) (α : Fin 3 → ℕ) :
    α ∈ weightedJetIndices H B ↔ α 0 + H * α 1 + H * α 2 ≤ B := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h1 : α 1 ≤ H * α 1 := Nat.le_mul_of_pos_left _ hH
    have h2 : α 2 ≤ H * α 2 := Nat.le_mul_of_pos_left _ hH
    fin_cases i
    · change α 0 < B + 1
      omega
    · change α 1 < B + 1
      omega
    · change α 2 < B + 1
      omega



theorem weightedJetIndices_real_weight {H : ℕ} (hH : 0 < H) {W : ℝ}
    (hW : 0 ≤ W) {a : Fin 3 → ℕ} (ha : a ∈ weightedJetIndices H ⌊W⌋₊) :
    (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤ W := by
  have hnat := (mem_weightedJetIndices_iff hH a).mp ha
  have hreal : (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤ (⌊W⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans (Nat.floor_le hW)



theorem mem_weightedJetIndices_of_rectangle {H : ℕ} {U : ℝ} (hH : 0 < H)
    (a : Fin 3 → ℕ)
    (ha₀ : (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U)
    (ha₁ : (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U)
    (ha₂ : (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U) :
    a ∈ weightedJetIndices H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ := by
  apply (mem_weightedJetIndices_iff hH a).mpr
  apply Nat.le_floor
  push_cast
  exact pivot_weight_of_rectangle (by exact_mod_cast hH) (a 0) (a 1) (a 2) ha₀ ha₁ ha₂

theorem span_cutoff_eq_top_of_rectangle {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {H : ℕ} {U : ℝ} (hH : 0 < H)
    (R : (Fin 3 → ℕ) → V)
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U}) = ⊤) :
    Submodule.span K (R '' (weightedJetIndices H
      ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ : Set (Fin 3 → ℕ))) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  apply Set.image_mono
  intro a ha
  exact mem_weightedJetIndices_of_rectangle hH a ha.1 ha.2.1 ha.2.2



end WeightedTorusJets

open Module
open scoped BigOperators

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RestrictWeightSortedEquiv
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators

open scoped BigOperators
open Module

namespace WeightedTorusJets

theorem greedyPivots_congr_prefix {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v v' : ℕ → V) (n : ℕ)
    (h : ∀ i < n, v i = v' i) : greedyPivots K v n = greedyPivots K v' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      classical
      have hprevious := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have hlast := h n (Nat.lt_succ_self n)
      have himage : v '' (greedyPivots K v' n : Set ℕ) =
          v' '' (greedyPivots K v' n : Set ℕ) := by
        apply Set.image_congr
        intro i hi
        exact h i (Nat.lt_succ_of_lt
          (Finset.mem_range.mp (greedyPivots_subset_range v' n hi)))
      simp only [greedyPivots, hprevious, hlast, himage]



theorem restrictWeightSortedEquiv_apply {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (i : Fin s.card) :
    (restrictWeightSortedEquiv s w B hs e he i : α) = e i := rfl

theorem restrictWeightSortedEquiv_monotone {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) :
    Monotone (fun i => w (restrictWeightSortedEquiv s w B hs e he i)) := by
  intro i j hij
  exact he hij

theorem extend_restrictWeightSortedEquiv_eq {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (fallback : α)
    (i : ℕ) (hi : i < s.card) :
    extendFiniteFamily (fun j => (restrictWeightSortedEquiv s w B hs e he j : α))
      fallback i = e i := by
  simp only [extendFiniteFamily, dite_eq_left hi, restrictWeightSortedEquiv_apply]

theorem greedyPivots_restrictWeightSortedEquiv {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    greedyPivots K
      (R ∘ extendFiniteFamily
        (fun j => (restrictWeightSortedEquiv s w B hs e he j : α)) fallback) s.card =
      greedyPivots K (R ∘ e) s.card := by
  apply greedyPivots_congr_prefix
  intro i hi
  exact congrArg R (extend_restrictWeightSortedEquiv_eq s w B hs e he fallback i hi)



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

end WeightedTorusJets

open scoped BigOperators
open InnerProductSpace

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormSqReal
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open InnerProductSpace

open scoped BigOperators NumberField

namespace WeightedTorusJets

open scoped BigOperators NumberField

theorem three_le_level_of_nonprincipal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : 3 ≤ q := by
  by_contra hq
  have hq0 : q ≠ 0 := NeZero.ne q
  have hsmall : q = 1 ∨ q = 2 := by omega
  rcases hsmall with rfl | rfl
  · exact hne (DirichletCharacter.level_one χ)
  · apply hne
    apply MulChar.eq_one_iff.mpr
    intro u
    rw [(by decide : ∀ u : (ZMod 2)ˣ, u = 1) u]
    simp

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CharacterGlobalGreedyDeterminantFullLocalBounds
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open InnerProductSpace
open scoped BigOperators NumberField
namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_global_greedy_determinant_full_local_bounds :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧ ∃ CH : ℕ → ℝ,
    ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)),
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    (∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ) ∧
                    ∀ β : ℝ, 0 < β → β < 1 →
                      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                    ∀ U : ℝ, 0 ≤ U →
                      (∑ i, (α i 0 : ℝ)) *
                          (Real.log U - C * Real.log q -
                            C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH H) -
                        C * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| := by
  classical
  obtain ⟨C, hC, hC4, hfinite⟩ := source_given_determinant_finite_lower_of_real_zero_jb247
  choose CH hCH using hfinite
  refine ⟨C, hC, hC4, CH, ?_⟩
  intro q _ χ hreal hprim hne hfield
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_global_greedy_determinant_local_bounds_jb247 q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
      harch, hdiv, hraw⟩ := hsource N H hH hHN n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
    harch, hdiv, hraw, ?_⟩
  intro β hβ0 hβ1 hzero U hU
  simpa only [Nat.cast_pow] using hCH H q χ hprim hne hreal β hβ0 hβ1 hzero
    _ hdegree (N ^ 4) Δ hneΔ α hdiv U hU

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GreedyPivotsWeightLowSpan
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

open Submodule

theorem greedyPivots_weight_le_of_low_span {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : ℕ → V) (wt : ℕ → ℕ) (hwt : Monotone wt)
    (T B : ℕ) (hspan : span K (v '' {j : ℕ | j < T ∧ wt j ≤ B}) = ⊤) :
    ∀ i ∈ greedyPivots K v T, wt i ≤ B := by
  intro i hi
  by_contra h
  have hiweight : B < wt i := Nat.lt_of_not_ge h
  have hprevious : span K (v '' (Finset.range i : Set ℕ)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply span_mono
    apply Set.image_mono
    intro j hj
    apply Finset.mem_range.mpr
    exact lt_of_not_ge (fun hij => (not_le_of_gt (hj.2.trans_lt hiweight)) (hwt hij))
  have hnot := ((mem_greedyPivots_iff v i T).mp hi).2
  apply hnot
  rw [hprevious]
  exact mem_top

theorem span_low_sequence_eq_top_of_coverage {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : ℕ → V) (wt : ℕ → ℕ)
    (R : α → V) (w : α → ℕ) (T B : ℕ)
    (hcover : ∀ a, w a ≤ B → ∃ j < T, wt j = w a ∧ v j = R a)
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    span K (v '' {j : ℕ | j < T ∧ wt j ≤ B}) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply span_mono
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨j, hj, hjw, hjv⟩ := hcover a ha
  exact ⟨j, ⟨hj, hjw.trans_le ha⟩, hjv⟩

end WeightedTorusJets

namespace WeightedTorusJets

open Submodule

theorem finite_sorted_greedy_weight_le_of_spanning_cutoff
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B₀ B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B₀)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    ∀ i ∈ greedyPivots K (R ∘ a) s.card, w (a i) ≤ B := by
  classical
  dsimp only
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  change ∀ i ∈ greedyPivots K v s.card, w (a i) ≤ B
  by_cases hB₀B : B₀ ≤ B
  · intro i hi
    have hiT : i < s.card := Finset.mem_range.mp (greedyPivots_subset_range v s.card hi)
    change w (extendFiniteFamily (fun i => (e i : α)) fallback i) ≤ B
    simp only [extendFiniteFamily, dite_eq_left hiT]
    exact ((hs _).mp (e ⟨i, hiT⟩).property).trans hB₀B
  · have hBB₀ : B ≤ B₀ := Nat.le_of_lt (Nat.lt_of_not_ge hB₀B)
    let wt := extendFiniteFamily (fun i => w (e i)) B₀
    have hwt : Monotone wt :=
      monotone_extendFiniteFamily _ _ hsort (fun i => (hs _).mp (e i).property)
    have hcover : ∀ b, w b ≤ B → ∃ j < s.card, wt j = w b ∧ v j = R b := by
      intro b hb
      let j : Fin s.card := e.symm ⟨b, (hs b).mpr (hb.trans hBB₀)⟩
      refine ⟨j, j.isLt, ?_, ?_⟩
      · simp [wt, extendFiniteFamily, j.isLt, j]
      · simp [v, a, extendFiniteFamily, j.isLt, j]
    have hlow := span_low_sequence_eq_top_of_coverage v wt R w s.card B hcover hspan
    intro i hi
    have hiT : i < s.card := Finset.mem_range.mp (greedyPivots_subset_range v s.card hi)
    have hbound := greedyPivots_weight_le_of_low_span v wt hwt s.card B hlow i hi
    simpa [wt, a, extendFiniteFamily, hiT] using hbound

theorem finiteGreedyPivots_weight_le_of_spanning_cutoff
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B₀ B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B₀)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    ∀ b ∈ finiteGreedyPivots K s R e fallback, w b ≤ B := by
  classical
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  exact finite_sorted_greedy_weight_le_of_spanning_cutoff
    s R e fallback w B₀ B hs hsort hspan i hi

end WeightedTorusJets

namespace WeightedTorusJets

theorem fixed_first_greedy_rectangle_weight_bound {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (H N : ℕ) (hH : 0 < H)
    (R : (Fin 3 → ℕ) → V)
    (e : Fin (weightedJetIndices H (N ^ 4 - 1)).card ≃ weightedJetIndices H (N ^ 4 - 1))
    (hsort : Monotone (fun i => (e i).1 0 + H * (e i).1 1 + H * (e i).1 2))
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    ∀ a ∈ finiteGreedyPivots K (weightedJetIndices H (N ^ 4 - 1)) R e 0,
      (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  let w := fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2
  let B := ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊
  have hsets : (weightedJetIndices H B : Set (Fin 3 → ℕ)) = {a | w a ≤ B} := by
    ext a
    exact mem_weightedJetIndices_iff hH a
  have hlow : Submodule.span K (R '' {a : Fin 3 → ℕ | w a ≤ B}) = ⊤ := by
    rw [← hsets]
    exact span_cutoff_eq_top_of_rectangle hH R hspan
  have hbound := finiteGreedyPivots_weight_le_of_spanning_cutoff
    (weightedJetIndices H (N ^ 4 - 1)) R e 0 w (N ^ 4 - 1) B
    (mem_weightedJetIndices_iff hH) hsort hlow
  intro a ha
  exact weightedJetIndices_real_weight hH (by positivity)
    ((mem_weightedJetIndices_iff hH a).mpr (hbound a ha))



theorem finiteGreedyPivots_restrictWeightSortedEquiv_map
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    finiteGreedyPivots K s R (restrictWeightSortedEquiv s w B hs e he) fallback =
      (greedyPivots K (R ∘ e) s.card).map e.toEmbedding := by
  classical
  unfold finiteGreedyPivots
  dsimp only
  rw [greedyPivots_restrictWeightSortedEquiv s R w B hs e he fallback,
    Finset.map_eq_image]
  apply Finset.image_congr
  intro i hi
  exact extend_restrictWeightSortedEquiv_eq s w B hs e he fallback i
    (Finset.mem_range.mp (greedyPivots_subset_range (R ∘ e) s.card hi))

theorem finiteGreedyPivots_restrictWeightSortedEquiv
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [DecidableEq α]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    finiteGreedyPivots K s R (restrictWeightSortedEquiv s w B hs e he) fallback =
      (greedyPivots K (R ∘ e) s.card).image e := by
  rw [finiteGreedyPivots_restrictWeightSortedEquiv_map, Finset.map_eq_image]
  rfl



theorem sum_embedding_eq_sum_finset_of_range {ι α A : Type*} [Fintype ι]
    [AddCommMonoid A] (p : ι ↪ α) (s : Finset α)
    (hp : Set.range p = (s : Set α)) (f : α → A) :
    ∑ i, f (p i) = ∑ a ∈ s, f a := by
  classical
  have hs : Finset.univ.map p = s := by
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact hp
  rw [← hs, Finset.sum_map]

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GlobalRectanglePivotBounds
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

open scoped BigOperators

theorem global_source_rectangle_pivot_bounds {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (H N : ℕ) (hH : 0 < H)
    (hHN : H ≤ N) (hN : 18818 ≤ N) (R : (Fin 3 → ℕ) → V)
    (e : ℕ ≃ (Fin 3 → ℕ))
    (he : Monotone (fun i => (e i) 0 + H * (e i) 1 + H * (e i) 2))
    (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ))
    (hα : Set.range α =
      ((greedyPivots K (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e :
        Set (Fin 3 → ℕ)))
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    let P := (greedyPivots K (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e
    (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  dsimp only
  let s := weightedJetIndices H (N ^ 4 - 1)
  let w := fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2
  let P := (greedyPivots K (R ∘ e) s.card).image e
  have hs : ∀ a, a ∈ s ↔ w a ≤ N ^ 4 - 1 := mem_weightedJetIndices_iff hH
  let e₀ := restrictWeightSortedEquiv s w (N ^ 4 - 1) hs e he
  have hmap : Finset.univ.map α = P := by
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact hα
  have hcard : P.card = N ^ 4 := by rw [← hmap]; simp
  have hfinite := finiteGreedyPivots_restrictWeightSortedEquiv
    (K := K) s R w (N ^ 4 - 1) hs e he 0
  change finiteGreedyPivots K s R e₀ 0 = P at hfinite
  apply weighted_pivot_bounds P H N hH hHN hN hcard
  intro a ha
  apply fixed_first_greedy_rectangle_weight_bound H N hH R e₀
    (restrictWeightSortedEquiv_monotone s w (N ^ 4 - 1) hs e he) hspan a
  rw [hfinite]
  exact ha

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormalizedMasterBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets.FinalComparison

theorem normalized_master_bound
    {L S₁ S₂ M U ℓ logN logU logM δ C C_H : ℝ}
    (hS₁ : 0 < S₁) (hlogU : 0 < logU) (hℓ : 0 < ℓ)
    (hN : logN = 3 / 4 * logU)
    (harch : L ≤ M / 2 * logM + (S₁ + S₂) * (logN + 1 / 2 * ℓ + Real.log 8))
    (hlower : S₁ * (logU - C * ℓ - C * δ * logU ^ 2 / ℓ - C_H) - C * M * U ≤ L) :
    1 ≤ 3 / 4 * (1 + S₂ / S₁) +
      (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / logU) + C * δ * (logU / ℓ) +
      (C_H + (1 + S₂ / S₁) * Real.log 8) / logU +
      (C * M * U + 1 / 2 * M * logM) / (S₁ * logU) := by
  apply (mul_le_mul_iff_left₀ (mul_pos hS₁ hlogU)).mp
  have hEq : S₁ * logU *
      (3 / 4 * (1 + S₂ / S₁) +
        (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / logU) + C * δ * (logU / ℓ) +
        (C_H + (1 + S₂ / S₁) * Real.log 8) / logU +
        (C * M * U + 1 / 2 * M * logM) / (S₁ * logU)) =
      M / 2 * logM + (S₁ + S₂) * (logN + 1 / 2 * ℓ + Real.log 8) +
        S₁ * (C * ℓ + C * δ * logU ^ 2 / ℓ + C_H) + C * M * U := by
    rw [hN]
    field_simp
    ring
  conv_rhs => rw [mul_comm]
  rw [hEq, one_mul]
  linarith

end WeightedTorusJets.FinalComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CharacterGlobalGreedyDeterminantMasterBounds
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_global_greedy_determinant_master_bounds :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧ ∃ CH : ℕ → ℝ,
    ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)),
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    (∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ) ∧
                    (∀ β : ℝ, 0 < β → β < 1 →
                      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                    ∀ U : ℝ, 0 ≤ U →
                      (∑ i, (α i 0 : ℝ)) *
                          (Real.log U - C * Real.log q -
                            C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH H) -
                        C * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ) ∧
                    (18818 ≤ N →
                      let P := (greedyPivots B (R ∘ e) s.card).image e
                      let S₁ := ∑ a ∈ P, (a 0 : ℝ)
                      let S₂ := ∑ a ∈ P, ((a 1 : ℝ) + a 2)
                      let M := (N : ℝ) ^ 4
                      let U := (N : ℝ) ^ (4 / 3 : ℝ)
                      M * (H : ℝ) ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁ ∧
                      S₂ ≤ 192 * M * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U ∧
                      0 < S₁ ∧
                      ∀ β : ℝ, 0 < β → β < 1 →
                        DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                        1 ≤ 3 / 4 * (1 + S₂ / S₁) +
                          (C + 1 / 2 * (1 + S₂ / S₁)) * (Real.log q / Real.log U) +
                          C * ((1 - β) * Real.log q) * (Real.log U / Real.log q) +
                          (CH H + (1 + S₂ / S₁) * Real.log 8) / Real.log U +
                          (C * M * U + 1 / 2 * M * Real.log M) / (S₁ * Real.log U)) := by
  classical
  obtain ⟨C, hC, hC4, CH, hlocal⟩ :=
    source_character_global_greedy_determinant_full_local_bounds
  refine ⟨C, hC, hC4, CH, ?_⟩
  intro q _ χ hreal hprim hne hfield
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    hlocal q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
      harch, hdiv, hraw, hfinite⟩ := hsource N H hH hHN n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
    harch, hdiv, hraw, hfinite, ?_⟩
  intro hN
  let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  let R := fun a : Fin 3 → ℕ => fun j =>
    θ j ^ a 0 * σ (θ j) ^ a 1 * (σ * τ) (θ j) ^ a 2
  let P := (greedyPivots B (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e
  let U := (N : ℝ) ^ (4 / 3 : ℝ)
  have hninj : Function.Injective (fun j i => (n j i : ℕ)) := by
    intro j k h
    apply n.injective
    funext i
    exact Fin.ext (congrFun h i)
  have hspan := actual_biquadratic_rectangle_span_jb247 a' b' v hv σ τ
    hσa hσb hτa hτb H N hH hHN (fun j i => (n j i : ℕ)) hninj
    (fun j i => (n j i).isLt)
  have hpivots := global_source_rectangle_pivot_bounds H N hH hHN hN R e he α hrange hspan
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hH.trans_le hHN
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hS₁ : 0 < ∑ a ∈ P, (a 0 : ℝ) := lt_of_lt_of_le (by positivity) hpivots.1
  refine ⟨hpivots.1, hpivots.2, hS₁, ?_⟩
  intro β hβ0 hβ1 hzero
  have hUone : 1 < U := by
    exact Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hS₁eq := sum_embedding_eq_sum_finset_of_range α P hrange (fun a => (a 0 : ℝ))
  have hS₂eq := sum_embedding_eq_sum_finset_of_range α P hrange (fun a => ((a 1 : ℝ) + a 2))
  have hlower := hfinite β hβ0 hβ1 hzero U (le_of_lt (zero_lt_one.trans hUone))
  rw [hS₁eq, hS₂eq] at harch
  rw [hS₁eq] at hlower
  have hlogN : Real.log (N : ℝ) = 3 / 4 * Real.log U := by
    dsimp only [U]
    rw [Real.log_rpow hNpos]
    ring
  have hq : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q from lt_of_lt_of_le (by decide) (three_le_level_of_nonprincipal χ hne))
  exact FinalComparison.normalized_master_bound hS₁ (Real.log_pos hUone)
    (Real.log_pos hq) hlogN harch hlower

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_QuadraticEigencharacter
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField

open scoped NumberField

namespace WeightedTorusJets

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem characterField_ne_sourceSqrtTwoField_of_ne_eight (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hne : χ ≠ 1) (hq8 : q ≠ 8) :
    characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ) := by
  intro hfield
  have hdiscr := characterField_changeLevel_discr_natAbs_jb247
    (L := CyclotomicField (8 * q) ℚ) (dvd_mul_left q 8) χ hquad hprim hne
  have htwo := (quadraticAdjoin_discriminant _ 2
    (sourceSqrtTwoField_root_sq q (CyclotomicField (8 * q) ℚ))
    (Int.squarefree_natAbs.mp Nat.prime_two.squarefree) not_isSquare_rat_two).1
  change NumberField.discr (sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) = _ at htwo
  norm_num at htwo
  rw [hfield, htwo] at hdiscr
  exact hq8 (by simpa using hdiscr.symm)

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GlobalWeightSortedJetEquiv
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

theorem exists_weight_sorted_equiv {α : Type*} [Infinite α] [Encodable α]
    (w : α → ℕ) (hfinite : ∀ B : ℕ, {a : α | w a ≤ B}.Finite) :
    ∃ e : ℕ ≃ α, Monotone (w ∘ e) := by
  classical
  let pred : α → α → Prop := fun a b =>
    w a < w b ∨ (w a = w b ∧ Encodable.encode a < Encodable.encode b)
  let F : α → Finset α := fun b => (hfinite (w b)).toFinset.filter (fun a => pred a b)
  have hmem : ∀ a b, a ∈ F b ↔ pred a b := by
    intro a b
    simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, pred]
    omega
  let rank : α → ℕ := fun a => (F a).card
  have hrank (a b : α) (hab : pred a b) : rank a < rank b := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro c hc
      apply (hmem c b).mpr
      have hca := (hmem c a).mp hc
      dsimp only [pred] at *
      omega
    · intro hEq
      have ha : a ∈ F b := (hmem a b).mpr hab
      rw [← hEq] at ha
      have h := (hmem a a).mp ha
      simp only [pred, lt_self_iff_false, and_false, or_self] at h
  have hinj : Function.Injective rank := by
    intro a b hab
    by_contra hne
    have hcode : Encodable.encode a ≠ Encodable.encode b := fun h =>
      hne (Encodable.encode_injective h)
    have horder : pred a b ∨ pred b a := by
      dsimp only [pred]
      omega
    rcases horder with h | h
    · have := hrank a b h
      omega
    · have := hrank b a h
      omega
  have hweight (a b : α) (hab : rank a ≤ rank b) : w a ≤ w b := by
    by_contra h
    have hlt := hrank b a (Or.inl (Nat.lt_of_not_ge h))
    omega
  let : Infinite (Set.range rank) := (Set.infinite_range_of_injective hinj).to_subtype
  let o : ℕ ≃o Set.range rank := Nat.Subtype.orderIsoOfNat (Set.range rank)
  let r : α ≃ Set.range rank := Equiv.ofInjective rank hinj
  let e : ℕ ≃ α := o.toEquiv.trans r.symm
  have he (i : ℕ) : rank (e i) = (o i : ℕ) :=
    congrArg Subtype.val (r.apply_symm_apply (o i))
  refine ⟨e, ?_⟩
  intro i j hij
  apply hweight
  rw [he, he]
  exact o.monotone hij

theorem exists_global_weight_sorted_jet_equiv (H : ℕ) (hH : 0 < H) :
    ∃ e : ℕ ≃ (Fin 3 → ℕ),
      Monotone (fun i => (e i) 0 + H * (e i) 1 + H * (e i) 2) := by
  let : Infinite (Fin 3 → ℕ) := Infinite.of_injective
    (fun n : ℕ => fun _ : Fin 3 => n) (fun _ _ h => congrFun h 0)
  apply exists_weight_sorted_equiv (fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2)
  intro B
  apply (Set.Finite.pi' (fun _ : Fin 3 => Set.finite_Iic B)).subset
  intro a ha i
  change a 0 + H * a 1 + H * a 2 ≤ B at ha
  have h1 : a 1 ≤ H * a 1 := Nat.le_mul_of_pos_left _ hH
  have h2 : a 2 ≤ H * a 2 := Nat.le_mul_of_pos_left _ hH
  change a i ≤ B
  fin_cases i <;> dsimp <;> omega

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NotEventuallyMaster
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open _root_.Filter Topology

namespace WeightedTorusJets.FinalComparison

theorem not_eventually_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    {r x e : ι → ℝ} {C A : ℝ}
    (hA : 0 < A) (hchoice : (C + 13 / 24) / A ≤ 1 / 16)
    (hr : ∀ᶠ n in l, r n ≤ 1 / 12)
    (hx : Tendsto x l (𝓝 A)) (he : Tendsto e l (𝓝 0)) :
    ¬ (∀ᶠ n in l,
      1 ≤ 3 / 4 * (1 + r n) + (C + 1 / 2 * (1 + r n)) / x n + e n) := by
  intro hmaster
  have hxpos : ∀ᶠ n in l, 0 < x n := hx.eventually (eventually_gt_nhds hA)
  have hlim : Tendsto
      (fun n ↦ 13 / 16 + (C + 13 / 24) / x n + e n) l
      (𝓝 (13 / 16 + (C + 13 / 24) / A)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.div hx hA.ne')).add he
  have hle : 1 ≤ 13 / 16 + (C + 13 / 24) / A := ge_of_tendsto hlim (by
    filter_upwards [hr, hxpos, hmaster] with n hrn hxn hn
    have hfirst : 3 / 4 * (1 + r n) ≤ (13 : ℝ) / 16 := by linarith
    have hsecond : (C + 1 / 2 * (1 + r n)) / x n ≤ (C + 13 / 24) / x n :=
      (div_le_div_iff_of_pos_right hxn).mpr (by linarith)
    linarith)
  linarith

end WeightedTorusJets.FinalComparison

end

section
open _root_.Filter _root_.Real
open scoped Topology

namespace WeightedTorusJets

theorem tendsto_log_natCeil_rpow_div_log {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ log (⌈q ^ γ⌉₊ : ℝ) / log q) atTop (𝓝 γ) := by
  have hpow := tendsto_rpow_atTop hγ
  have hratio : Tendsto (fun q : ℝ ↦ (⌈q ^ γ⌉₊ : ℝ) / q ^ γ) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hpow
  have hlog : Tendsto (fun q : ℝ ↦ log ((⌈q ^ γ⌉₊ : ℝ) / q ^ γ)) atTop (𝓝 0) := by
    simpa using hratio.log one_ne_zero
  have herr := hlog.div_atTop tendsto_log_atTop
  have hsum := herr.add_const γ
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with q hq
  have hq₀ : 0 < q := lt_trans zero_lt_one hq
  have hqp : 0 < q ^ γ := rpow_pos_of_pos hq₀ γ
  have hceil : 0 < (⌈q ^ γ⌉₊ : ℝ) := lt_of_lt_of_le hqp (Nat.le_ceil _)
  rw [log_div hceil.ne' hqp.ne', log_rpow hq₀]
  field_simp [(log_pos hq).ne']
  ring

theorem tendsto_log_scale_natCeil_rpow_div_log {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ log ((⌈q ^ γ⌉₊ : ℝ) ^ (4 / 3 : ℝ)) / log q)
      atTop (𝓝 (4 * γ / 3)) := by
  have h := (tendsto_log_natCeil_rpow_div_log hγ).const_mul (4 / 3 : ℝ)
  have heq : (4 / 3 : ℝ) * γ = 4 * γ / 3 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  have hceil : 0 < (⌈q ^ γ⌉₊ : ℝ) :=
    lt_of_lt_of_le (rpow_pos_of_pos hq γ) (Nat.le_ceil _)
  rw [log_rpow hceil]
  ring

theorem tendsto_natCeil_rpow_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ ⌈q ^ γ⌉₊) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (tendsto_rpow_atTop hγ)

theorem tendsto_scale_natCeil_rpow_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ (⌈q ^ γ⌉₊ : ℝ) ^ (4 / 3 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 3)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_natCeil_rpow_atTop hγ))

theorem exists_gamma_second_term_bound (C : ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ (C + 13 / 24) / (4 * γ / 3) < 1 / 16 := by
  refine ⟨12 * (|C| + 1), by positivity, ?_⟩
  have hC : C ≤ |C| := le_abs_self C
  rw [div_lt_iff₀ (by positivity : 0 < 4 * (12 * (|C| + 1)) / 3)]
  linarith

theorem log_degree_four_eq_three_log_scale {N : ℝ} (hN : 0 < N) :
    log (N ^ (4 : ℕ)) = 3 * log (N ^ (4 / 3 : ℝ)) := by
  rw [log_pow, log_rpow hN]
  ring

theorem log_eq_three_quarters_log_scale {N : ℝ} (hN : 0 < N) :
    log N = (3 / 4 : ℝ) * log (N ^ (4 / 3 : ℝ)) := by
  rw [log_rpow hN]
  ring

end WeightedTorusJets

end

section
namespace WeightedTorusJets

theorem weight_rpow_shift {H : ℝ} (hH : 0 < H) :
    H ^ (-1 / 3 : ℝ) * H = H ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_add_one hH.ne']
  norm_num

theorem pivot_ratio_le {H M U S₁ S₂ : ℝ} (hH : 0 < H) (hM : 0 < M)
    (hU : 0 < U)
    (hS₁ : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U) :
    S₂ / S₁ ≤ 7226112 / H := by
  have hpow : 0 < H ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hH _
  have hS₁pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  rw [div_le_div_iff₀ hS₁pos hH]
  have hmul := mul_le_mul_of_nonneg_right hS₂ hH.le
  have hlower := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4 * 97 ^ 2)).mp hS₁
  calc
    S₂ * H ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U * H := hmul
    _ = 192 * (M * H ^ (2 / 3 : ℝ) * U) := by rw [← weight_rpow_shift hH]; ring
    _ ≤ 7226112 * S₁ := by nlinarith

theorem pivot_ratio_le_one_twelfth {H M U S₁ S₂ : ℝ} (hH : 86713344 ≤ H)
    (hM : 0 < M) (hU : 0 < U)
    (hS₁ : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U) :
    S₂ / S₁ ≤ 1 / 12 := by
  have hHpos : 0 < H := by linarith
  exact (pivot_ratio_le hHpos hM hU hS₁ hS₂).trans
    ((div_le_iff₀ hHpos).mpr (by linarith))

end WeightedTorusJets

end

section
open _root_.Filter
open scoped Topology

namespace WeightedTorusJets

theorem normalized_error_component_bounds {M U S A : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hA : 0 < A)
    (hS : A * M * U ≤ S) (hlog : Real.log M = 3 * Real.log U) :
    M * U / (S * Real.log U) ≤ 1 / (A * Real.log U) ∧
      M * Real.log M / (S * Real.log U) ≤ 3 / (A * U) := by
  have hU0 : 0 < U := lt_trans zero_lt_one hU
  have hL : 0 < Real.log U := Real.log_pos hU
  have hden : 0 < A * M * U * Real.log U := by positivity
  have hden_le : A * M * U * Real.log U ≤ S * Real.log U :=
    mul_le_mul_of_nonneg_right hS hL.le
  constructor
  · calc
      M * U / (S * Real.log U) ≤ M * U / (A * M * U * Real.log U) :=
        div_le_div_of_nonneg_left (by positivity) hden hden_le
      _ = _ := by field_simp
  · have hnum : 0 ≤ M * Real.log M := by rw [hlog]; positivity
    calc
      M * Real.log M / (S * Real.log U) ≤
          M * Real.log M / (A * M * U * Real.log U) :=
        div_le_div_of_nonneg_left hnum hden hden_le
      _ = _ := by rw [hlog]; field_simp

theorem determinant_error_le {M U S A C : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hA : 0 < A) (hC : 0 ≤ C)
    (hS : A * M * U ≤ S) (hlog : Real.log M = 3 * Real.log U) :
    (C * M * U + (1 / 2 : ℝ) * M * Real.log M) / (S * Real.log U) ≤
      C / (A * Real.log U) + 3 / (2 * A * U) := by
  obtain ⟨hfirst, hsecond⟩ := normalized_error_component_bounds hM hU hA hS hlog
  calc
    _ = C * (M * U / (S * Real.log U)) +
        (1 / 2 : ℝ) * (M * Real.log M / (S * Real.log U)) := by ring
    _ ≤ C * (1 / (A * Real.log U)) + (1 / 2 : ℝ) * (3 / (A * U)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hC)
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = _ := by ring

end WeightedTorusJets

end

section
namespace WeightedTorusJets.FinalComparison

theorem uniform_master_bound {L M U ℓ S₁ S₂ δ C C_H D : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hℓ : 0 < ℓ) (hD : 0 < D) (hC : 0 ≤ C)
    (hS₁ : D * M * U ≤ S₁) (hr : S₂ / S₁ ≤ 1 / 12)
    (hlogM : Real.log M = 3 * Real.log U)
    (hupper : L ≤ M / 2 * Real.log M +
      (S₁ + S₂) * (3 / 4 * Real.log U + 1 / 2 * ℓ + Real.log 8))
    (hlower : S₁ * (Real.log U - C * ℓ - C * δ * Real.log U ^ 2 / ℓ - C_H) -
      C * M * U ≤ L) :
    1 ≤ 13 / 16 + (C + 13 / 24) * (ℓ / Real.log U) +
      C * δ * (Real.log U / ℓ) + (C_H + 13 / 12 * Real.log 8) / Real.log U +
      C / (D * Real.log U) + 3 / (2 * D * U) := by
  have hUpos : 0 < U := zero_lt_one.trans hU
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hS₁pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  have hmaster := normalized_master_bound hS₁pos hlogU hℓ rfl hupper hlower
  have hfirst : 3 / 4 * (1 + S₂ / S₁) ≤ (13 : ℝ) / 16 := by linarith
  have hsecond : (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / Real.log U) ≤
      (C + 13 / 24) * (ℓ / Real.log U) :=
    mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hℓ.le hlogU.le)
  have hfixed : (C_H + (1 + S₂ / S₁) * Real.log 8) / Real.log U ≤
      (C_H + 13 / 12 * Real.log 8) / Real.log U := by
    apply (div_le_div_iff_of_pos_right hlogU).mpr
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have := mul_le_mul_of_nonneg_right (by linarith : 1 + S₂ / S₁ ≤ 13 / 12) hlog8
    linarith
  have hdet := WeightedTorusJets.determinant_error_le hM hU hD hC hS₁ hlogM
  linarith

end WeightedTorusJets.FinalComparison

end

section
namespace WeightedTorusJets

open _root_.Filter Topology

theorem exists_fixed_parameters_not_eventually_uniform_bound (C : ℝ) :
    ∃ H : ℕ, 86713344 ≤ H ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ (q δ : ℕ → ℝ) (C_H : ℝ),
        Tendsto q atTop atTop → Tendsto δ atTop (𝓝 0) →
        let N : ℕ → ℝ := fun k ↦ (⌈q k ^ γ⌉₊ : ℝ)
        let U : ℕ → ℝ := fun k ↦ N k ^ (4 / 3 : ℝ)
        let D : ℝ := (H : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)
        ¬ (∀ᶠ k in atTop,
          1 ≤ 13 / 16 + (C + 13 / 24) * (Real.log (q k) / Real.log (U k)) +
            C * δ k * (Real.log (U k) / Real.log (q k)) +
            (C_H + 13 / 12 * Real.log 8) / Real.log (U k) +
            C / (D * Real.log (U k)) + 3 / (2 * D * U k)) := by
  obtain ⟨γ, hγ, hchoice⟩ := exists_gamma_second_term_bound C
  refine ⟨86713344, le_rfl, γ, hγ, ?_⟩
  intro q δ C_H hq hδ N U D hbound
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hU : Tendsto U atTop atTop := (tendsto_scale_natCeil_rpow_atTop hγ).comp hq
  have hlogU := Real.tendsto_log_atTop.comp hU
  have hratio : Tendsto (fun k ↦ Real.log (U k) / Real.log (q k))
      atTop (𝓝 (4 * γ / 3)) := (tendsto_log_scale_natCeil_rpow_div_log hγ).comp hq
  have hδterm : Tendsto (fun k ↦ C * δ k * (Real.log (U k) / Real.log (q k)))
      atTop (𝓝 0) := by simpa using (hδ.const_mul C).mul hratio
  have hfixed := (tendsto_const_nhds (x := C_H + 13 / 12 * Real.log 8)).div_atTop hlogU
  have hdet₁ := (tendsto_const_nhds (x := C)).div_atTop (hlogU.const_mul_atTop hD)
  have hdet₂ := (tendsto_const_nhds (x := (3 : ℝ))).div_atTop
    (hU.const_mul_atTop (by positivity : 0 < 2 * D))
  have herror : Tendsto (fun k ↦ C * δ k * (Real.log (U k) / Real.log (q k)) +
      (C_H + 13 / 12 * Real.log 8) / Real.log (U k) + C / (D * Real.log (U k)) +
      3 / (2 * D * U k)) atTop (𝓝 0) := by
    simpa using ((hδterm.add hfixed).add hdet₁).add hdet₂
  apply FinalComparison.not_eventually_master (r := fun _ ↦ (1 / 12 : ℝ))
    (by positivity) hchoice.le (.of_forall fun _ ↦ le_rfl) hratio herror
  filter_upwards [hbound] with k hk
  simpa only [show (3 / 4 : ℝ) * (1 + 1 / 12) = 13 / 16 by norm_num,
    show (1 / 2 : ℝ) * (1 + 1 / 12) = 13 / 24 by norm_num,
    div_div_eq_mul_div, mul_div_assoc, add_assoc] using hk

end WeightedTorusJets

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RealZeroUniformMasterBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

open scoped BigOperators NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_real_zero_uniform_master_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 86713344 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≠ 8 →
      ∀ χ : DirichletCharacter ℂ q,
        (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
      ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      ∀ N : ℕ, H ≤ N → 18818 ≤ N →
      let U : ℝ := (N : ℝ) ^ (4 / 3 : ℝ)
      let D : ℝ := (H : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)
      1 ≤ 13 / 16 + (C + 13 / 24) * (Real.log (q : ℝ) / Real.log U) +
        C * ((1 - β) * Real.log (q : ℝ)) * (Real.log U / Real.log (q : ℝ)) +
        (CH + 13 / 12 * Real.log 8) / Real.log U +
        C / (D * Real.log U) + 3 / (2 * D * U) := by
  classical
  obtain ⟨C, hC, _hC4, CH, hsource⟩ :=
    source_character_global_greedy_determinant_master_bounds
  refine ⟨C, hC, ?_⟩
  intro H hH
  have hHnat : 0 < H := by omega
  obtain ⟨e, he⟩ := exists_global_weight_sorted_jet_equiv H hHnat
  refine ⟨CH H, ?_⟩
  intro q _ hq hq8 χ hreal hprim hne
  have hfield := characterField_ne_sourceSqrtTwoField_of_ne_eight q χ hprim
    (real_character_isQuadratic χ hreal) hne hq8
  obtain ⟨d, a, b, _hd, _hdsize, _hddiv, _hdns, _ha, _hb, _hfield, _hdisc,
    _hfund, _hformula, v, _hv, _hint, _hdegree, σ, τ, _hσa, _hσb, _hτa, _hτb,
    _hcard, _hall, _hcomm, hdata⟩ := hsource q χ hreal hprim hne hfield
  intro β hβ0 hβ1 hzero N hHN hN U D
  let n : Fin (N ^ 4) ≃ (Fin 4 → Fin N) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin 4 → Fin N) = N ^ 4)).symm
  obtain ⟨g, α, _hg, _hα, hrange, _hmono, _hweight, _hstable,
    Δ, _hΔ, _hΔne, harch, _hdiv, _hraw, hfinite, hlarge⟩ := hdata N H hHnat hHN n e he
  obtain ⟨hpivot₁, hpivot₂, _hSpos, _hmaster⟩ := hlarge hN
  have hS₁eq := sum_embedding_eq_sum_finset_of_range α _ hrange (fun a => (a 0 : ℝ))
  have hS₂eq := sum_embedding_eq_sum_finset_of_range α _ hrange
    (fun a => ((a 1 : ℝ) + a 2))
  rw [← hS₁eq] at hpivot₁
  rw [← hS₂eq] at hpivot₂
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hHnat.trans_le hHN
  have hM : 0 < (N : ℝ) ^ 4 := pow_pos hNpos _
  have hUone : 1 < U := Real.one_lt_rpow
    (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hS₁ : D * (N : ℝ) ^ 4 * U ≤ ∑ i, (α i 0 : ℝ) := by
    convert hpivot₁ using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [D, U]
    ring
  have hratio : (∑ i, ((α i 1 : ℝ) + α i 2)) / (∑ i, (α i 0 : ℝ)) ≤ 1 / 12 :=
    pivot_ratio_le_one_twelfth (H := (H : ℝ)) (M := (N : ℝ) ^ 4) (U := U)
      (by exact_mod_cast hH) hM (zero_lt_one.trans hUone)
      (by simpa only [U] using hpivot₁)
      (by simpa only [U, neg_div] using hpivot₂)
  have hlower := hfinite β hβ0 hβ1 hzero U (zero_lt_one.trans hUone).le
  have hlogM : Real.log ((N : ℝ) ^ 4) = 3 * Real.log U :=
    log_degree_four_eq_three_log_scale hNpos
  have hlogN : Real.log (N : ℝ) = 3 / 4 * Real.log U :=
    log_eq_three_quarters_log_scale hNpos
  apply FinalComparison.uniform_master_bound hM hUone
    (Real.log_pos (by exact_mod_cast (show 1 < q by omega))) hD hC.le hS₁ hratio hlogM
    ?_ hlower
  simpa only [hlogN] using harch

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DirichletRealZeroBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

open _root_.Filter Topology

theorem dirichlet_real_zero_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  by_contra hnot
  obtain ⟨q, hq, χ, β, hadm, hqtop, hgap⟩ := exists_contrary_sequence hnot
  obtain ⟨C, _hC, hsource⟩ := source_real_zero_uniform_master_bound
  obtain ⟨H, hH, γ, hγ, hno⟩ := exists_fixed_parameters_not_eventually_uniform_bound C
  obtain ⟨CH, hCH⟩ := hsource H hH
  have hqreal : Tendsto (fun n => (q n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqtop
  apply hno (fun n => (q n : ℝ)) (fun n => (1 - β n) * Real.log (q n : ℝ)) CH hqreal hgap
  have hNtop : Tendsto (fun n => ⌈(q n : ℝ) ^ γ⌉₊) atTop atTop :=
    (tendsto_natCeil_rpow_atTop hγ).comp hqreal
  filter_upwards [hNtop.eventually_ge_atTop H, hNtop.eventually_ge_atTop 18818,
    hqtop.eventually_ne_atTop 8] with n hnH hnN hn8
  let := hq n
  exact hCH (q n) (hadm n).1 hn8 (χ n) (hadm n).2.2.2.1
    (hadm n).2.1 (hadm n).2.2.1 (β n) (hadm n).2.2.2.2.1
    (hadm n).2.2.2.2.2.1 (hadm n).2.2.2.2.2.2
    ⌈(q n : ℝ) ^ γ⌉₊ hnH hnN

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DirichletRealZeroBoundProof
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
theorem WeightedTorusJets.dirichletRealZeroBound_proof :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  exact WeightedTorusJets.dirichlet_real_zero_bound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PrimitiveTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz

theorem exists_primitive_real_zero_free_disk_jb247_oai :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive → chi ≠ 1 →
      (∀ a : ZMod q, (chi a).im = 0) → ∀ z : ℂ,
      ‖z - 1‖ ≤ c / Real.log (q : ℝ) → DirichletCharacter.LFunction chi z ≠ 0 := by
  obtain ⟨ce, hce, hexceptional⟩ :=
    WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple_jb247
  obtain ⟨cg, hcg, hgap⟩ := WeightedTorusJets.dirichletRealZeroBound_proof
  let c : ℝ := min ce (min (cg / 2) (1 / 4))
  have hc : 0 < c := lt_min hce (lt_min (by positivity) (by norm_num))
  have hce' : c ≤ ce := min_le_left _ _
  have hcg' : c ≤ cg / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc4 : c ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro q _ hq chi hprim hchi hreal z hz hzero
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 1 < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hlogpos : 0 < Real.log (q : ℝ) := by linarith
  have hz' : ‖z - 1‖ ≤ ce / Real.log (q : ℝ) :=
    hz.trans (div_le_div_of_nonneg_right hce' hlogpos.le)
  have him : z.im = 0 := (hexceptional q hq chi hprim hchi hreal z hz' hzero).1
  have hrad : c / Real.log (q : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hlogpos).mpr
    nlinarith
  have hre : |z.re - 1| ≤ c / Real.log (q : ℝ) := by
    have h := Complex.abs_re_le_norm (z - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    exact h.trans hz
  have hrep : 0 < z.re := by
    have h := (abs_le.mp (hre.trans hrad)).1
    linarith
  have hrelt : z.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hzero
  have hrealz : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  have hzeroR : DirichletCharacter.LFunction chi (z.re : ℂ) = 0 := by
    rw [hrealz]
    exact hzero
  have hlower := hgap q hq chi hprim hchi hreal z.re ⟨hrep, hrelt, hzeroR⟩
  have hupper : (1 - z.re) * Real.log (q : ℝ) ≤ c := by
    apply (le_div_iff₀ hlogpos).mp
    have h := (abs_le.mp hre).1
    linarith
  linarith





open scoped BigOperators

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247_oai := @OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247_oai
