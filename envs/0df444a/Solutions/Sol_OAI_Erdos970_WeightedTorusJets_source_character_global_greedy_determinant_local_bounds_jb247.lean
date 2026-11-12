-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:51:05.774204+00:00
-- url     : https://prove2.me/submissions/7d4af129-01f4-481c-9101-062e33edbb00

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J001
import Definitions.Def_OAIQ247J005
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_source_biquadratic_arithmetic_of_field_ne_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_BiquadraticBasis
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
namespace WeightedTorusJets

theorem biquadratic_monomials_integral {E : Type*} [CommRing E] [Algebra ℤ E]
    (a b : E) (d e : ℤ) (ha : a ^ 2 = d) (hb : b ^ 2 = e) :
    IsIntegral ℤ (1 : E) ∧ IsIntegral ℤ a ∧ IsIntegral ℤ b ∧ IsIntegral ℤ (a * b) := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hbi : IsIntegral ℤ b := IsIntegral.of_pow (by decide : 0 < 2)
    (hb ▸ isIntegral_intCast e)
  exact ⟨isIntegral_one, hai, hbi, hai.mul hbi⟩



open Module

end WeightedTorusJets

open scoped NumberField

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

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_biquadratic_arithmetic_canonical_of_field_ne (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    let L := CyclotomicField (8 * q) ℚ
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
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
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  exact source_biquadratic_arithmetic_of_field_ne_jb247 q (CyclotomicField (8 * q) ℚ)
    χ hreal hprim hne hfield

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_BiquadraticArithmeticFull
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

namespace WeightedTorusJets

theorem exists_lower_triangular_replacement
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A B : Matrix ι ι K)
    (hspan : ∀ i, B i - A i ∈ Submodule.span K (A '' {j | j < i})) :
    ∃ L : Matrix ι ι K, L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧ B = L * A := by
  classical
  have hcoeff (i : ι) : ∃ c : ι → K,
      ∑ j ∈ Finset.univ.filter (fun j => j < i), c j • A j = B i - A i := by
    apply (Submodule.mem_span_image_finset_iff_exists_fun' K).mp
    simpa using hspan i
  choose c hc using hcoeff
  refine ⟨Matrix.of (fun i j =>
    (if j < i then c i j else 0) + (if i = j then 1 else 0)),
    ?_, ?_, ?_⟩
  · intro i j hij
    change i < j at hij
    simp [not_lt_of_ge hij.le, hij.ne]
  · intro i
    simp
  · apply Matrix.ext
    intro i k
    have hi := congrFun (hc i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi
    simpa only [Matrix.mul_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      ite_mul, zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
      Finset.sum_filter] using (eq_sub_iff_add_eq.mp hi).symm

theorem determinant_dvd_of_earlier_row_replacement
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (A B : Matrix ι ι R)
    (hspan : ∀ i, f.mapMatrix B i - f.mapMatrix A i ∈
      Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (p : R) (e : ι → ℕ) (hdiv : ∀ i j, p ^ e i ∣ B i j) :
    p ^ (∑ i, e i) ∣ A.det := by
  classical
  obtain ⟨L, hL, hdiag, hreplace⟩ :=
    exists_lower_triangular_replacement (f.mapMatrix A) (f.mapMatrix B) hspan
  have hdet : B.det = A.det := hf <| by
    rw [f.map_det, f.map_det, hreplace, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular L hL]
    simp [hdiag]
  choose C hC using hdiv
  have hB : B = Matrix.of (fun i j => p ^ e i * (Matrix.of C) i j) := by
    ext i j
    exact hC i j
  rw [← hdet, hB, Matrix.det_mul_column (fun i => p ^ e i) (Matrix.of C),
    Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _

theorem replacement_row_expansion {K ι : Type*} [CommRing K]
    (x y z : ι → K) (p k r b c : ℕ) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c =
      ∑ m ∈ Finset.range (k + 1),
        (((-1) ^ m * (k.choose m : K)) •
          (x ^ (p * (k - m) + r) * y ^ (b + m) * z ^ c)) := by
  rw [sub_eq_add_neg, add_comm (x ^ p), add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
    Pi.natCast_apply, pow_add, pow_mul]
  rw [neg_pow]
  ring

theorem replacement_row_sub_mem {K ι : Type*} [CommRing K]
    (x y z : ι → K) (W : Submodule K (ι → K)) (H p k r b c : ℕ) (hp : H < p)
    (hspan : ∀ a b' c', a + H * b' + H * c' < p * k + r + H * b + H * c →
      x ^ a * y ^ b' * z ^ c' ∈ W) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c -
      x ^ (p * k + r) * y ^ b * z ^ c ∈ W := by
  rw [replacement_row_expansion, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul,
    Nat.sub_zero, Nat.add_zero, add_sub_cancel_right]
  apply W.sum_mem
  intro m hm
  apply W.smul_mem
  apply hspan
  have hmle : m + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hm)
  have hprod : H * (m + 1) < p * (m + 1) :=
    Nat.mul_lt_mul_of_pos_right hp (Nat.succ_pos m)
  have hdecomp : p * k = p * (k - (m + 1)) + p * (m + 1) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hmle]
  simp only [Nat.mul_add, Nat.mul_one] at hprod hdecomp ⊢
  omega

theorem weighted_interpolation_determinant_dvd
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (a b c : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i n, A i n = x n ^ a i * y n ^ b i * z n ^ c i)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (f ∘ x) ^ a' * (f ∘ y) ^ b' * (f ∘ z) ^ c' ∈
        Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (hFrob : ∀ n, (p : R) ∣ x n ^ p - y n) :
    (p : R) ^ (∑ i, a i / p) ∣ A.det := by
  classical
  let B : Matrix ι ι R := Matrix.of fun i n =>
    x n ^ (a i % p) * (x n ^ p - y n) ^ (a i / p) * y n ^ b i * z n ^ c i
  apply determinant_dvd_of_earlier_row_replacement f hf A B
  · intro i
    have h := replacement_row_sub_mem (f ∘ x) (f ∘ y) (f ∘ z)
      (Submodule.span K (f.mapMatrix A '' {j | j < i}))
      H p (a i / p) (a i % p) (b i) (c i) hp (by
        intro a' b' c' hw
        apply hspan i a' b' c'
        simpa only [Nat.div_add_mod] using hw)
    have heq : f.mapMatrix B i - f.mapMatrix A i =
        (f ∘ x) ^ (a i % p) * ((f ∘ x) ^ p - f ∘ y) ^ (a i / p) *
          (f ∘ y) ^ b i * (f ∘ z) ^ c i -
          (f ∘ x) ^ a i * (f ∘ y) ^ b i * (f ∘ z) ^ c i := by
      ext n
      simp [B, hA, map_mul, map_pow, map_sub]
    rw [heq]
    simpa only [Nat.div_add_mod] using h
  · intro i n
    exact (((pow_dvd_pow_of_dvd (hFrob n) (a i / p)).mul_left
      (x n ^ (a i % p))).mul_right (y n ^ b i)).mul_right (z n ^ c i)

theorem weighted_interpolation_determinant_dvd_of_frobenius_choice
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (a b c : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i n, A i n = x n ^ a i * y n ^ b i * z n ^ c i)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (f ∘ x) ^ a' * (f ∘ y) ^ b' * (f ∘ z) ^ c' ∈
        Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (hFrob : (∀ n, (p : R) ∣ x n ^ p - y n) ∨
      (∀ n, (p : R) ∣ x n ^ p - z n)) :
    (p : R) ^ (∑ i, a i / p) ∣ A.det := by
  rcases hFrob with hFrob | hFrob
  · exact weighted_interpolation_determinant_dvd f hf x y z a b c A hA H p hp
      hspan hFrob
  · apply weighted_interpolation_determinant_dvd f hf x z y a c b A
      (fun i n => by rw [hA]; ring) H p hp _ hFrob
    intro i a' c' b' hw
    have h := hspan i a' b' c' (by omega)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

open NumberField

theorem galois_derivative_determinant_mem_prime_power
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (θ : ι → 𝓞 K) (ν₂ ν₃ : K →+* K) (a b c : ι → ℕ)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (fun n => (θ n : K) ^ a' * ν₂ (θ n) ^ b' * ν₃ (θ n) ^ c') ∈
        Submodule.span K ((fun i n =>
          (θ n : K) ^ a i * ν₂ (θ n) ^ b i * ν₃ (θ n) ^ c i) '' {j | j < i}))
    (hFrob : (∀ n, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (θ n ^ p) =
      Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom ν₂ (θ n))) ∨
      (∀ n, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (θ n ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom ν₃ (θ n)))) :
    (Matrix.of (fun i n => θ n ^ a i * (RingOfIntegers.mapRingHom ν₂ (θ n)) ^ b i *
      (RingOfIntegers.mapRingHom ν₃ (θ n)) ^ c i)).det ∈
      (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, a i / p) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  apply weighted_interpolation_determinant_dvd_of_frobenius_choice (algebraMap (𝓞 K) K)
    RingOfIntegers.coe_injective θ
    ((RingOfIntegers.mapRingHom ν₂) ∘ θ) ((RingOfIntegers.mapRingHom ν₃) ∘ θ)
    a b c _ (fun _ _ => rfl) H p hp
  · intro i a' b' c' hw
    convert hspan i a' b' c' hw using 1
    · apply congrArg (Submodule.span K)
      apply congrArg (fun f : ι → ι → K => f '' {j | j < i})
      ext j n
      change algebraMap (𝓞 K) K (_ * _ * _) = _
      simp
    · funext n
      rfl
  · rcases hFrob with hFrob | hFrob
    · exact Or.inl fun n => Ideal.mem_span_singleton.mp
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hFrob n))
    · exact Or.inr fun n => Ideal.mem_span_singleton.mp
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hFrob n))

theorem integral_jet_matrix_lift {K : Type*} [Field K]
    (σ τ : K →+* K) {a b : K} {d : ℤ} {m : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (n : Fin m → Fin 4 → ℕ) (α : Fin m → Fin 3 → ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    ∃ θ₀ : Fin m → 𝓞 K,
      (∀ j, (θ₀ j : K) = θ j) ∧
      let A₀ := Matrix.of fun i j => θ₀ j ^ α i 0 *
        NumberField.RingOfIntegers.mapRingHom σ (θ₀ j) ^ α i 1 *
        NumberField.RingOfIntegers.mapRingHom (σ.comp τ) (θ₀ j) ^ α i 2
      A₀.map (algebraMap (𝓞 K) K) = A ∧
        (A₀.det : K) = A.det ∧ (A.det ≠ 0 → A₀.det ≠ 0) := by
  let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
  obtain ⟨h1, hai, hbi, hab⟩ :=
    biquadratic_monomials_integral a b d 2 ha (by simpa using hb)
  have hθ (j : Fin m) : IsIntegral ℤ (θ j) := by
    apply IsIntegral.sum
    intro i _
    apply (isIntegral_natCast _).mul
    fin_cases i <;> assumption
  let θ₀ : Fin m → 𝓞 K := fun j => ⟨θ j, hθ j⟩
  refine ⟨θ₀, fun _ => rfl, ?_⟩
  dsimp only
  have hmap :
      (Matrix.of fun i j => θ₀ j ^ α i 0 *
        NumberField.RingOfIntegers.mapRingHom σ (θ₀ j) ^ α i 1 *
        NumberField.RingOfIntegers.mapRingHom (σ.comp τ) (θ₀ j) ^ α i 2).map
          (algebraMap (𝓞 K) K) =
      Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
        (σ.comp τ) (θ j) ^ α i 2 := by
    ext i j
    change algebraMap (𝓞 K) K (_ * _ * _) = _
    simp only [map_mul, map_pow]
    rfl
  refine ⟨hmap, ?_⟩
  have hdet := congrArg Matrix.det hmap
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
  exact ⟨hdet, fun h => NumberField.RingOfIntegers.coe_ne_zero_iff.mp (hdet.symm ▸ h)⟩

theorem exists_integral_jet_determinant_divisible
    {K : Type*} [Field K]
    (σ τ : K →+* K) {a b : K} {d : ℤ} {m : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (n : Fin m → Fin 4 → ℕ) (α : Fin m → Fin 3 → ℕ) (H : ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    (∀ i a' b' c', a' + H * b' + H * c' < α i 0 + H * α i 1 + H * α i 2 →
      (fun j => θ j ^ a' * σ (θ j) ^ b' * (σ.comp τ) (θ j) ^ c') ∈
        Submodule.span K (A '' {j | j < i})) →
    A.det ≠ 0 →
    ∃ Δ : 𝓞 K, (Δ : K) = A.det ∧ Δ ≠ 0 ∧
      ∀ p : ℕ, H < p →
        ((∀ t : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (t ^ p) =
            Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom σ t)) ∨
          (∀ t : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (t ^ p) =
            Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
              (RingOfIntegers.mapRingHom (σ.comp τ) t))) →
        Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p) := by
  dsimp only
  intro hspan hnonzero
  obtain ⟨θ₀, hθ₀, _hmap, hdet, hne⟩ := integral_jet_matrix_lift σ τ ha hb n α
  refine ⟨_, hdet, hne hnonzero, ?_⟩
  intro p hp hFrob
  apply galois_derivative_determinant_mem_prime_power θ₀ σ (σ.comp τ)
    (fun i => α i 0) (fun i => α i 1) (fun i => α i 2) H p hp
  · intro i a' b' c' hw
    convert hspan i a' b' c' hw using 1
    · apply congrArg (Submodule.span K)
      apply congrArg (fun f : Fin m → Fin m → K => f '' {j | j < i})
      ext k j
      simp only [Matrix.of_apply, hθ₀]
    · funext j
      simp only [hθ₀]
  · rcases hFrob with hFrob | hFrob
    · exact Or.inl fun j => hFrob (θ₀ j)
    · exact Or.inr fun j => hFrob (θ₀ j)

end WeightedTorusJets

open scoped NumberField

namespace WeightedTorusJets

theorem frobenius_action_choice_iff_mapRingHom
    {K : Type*} [Field K] [NumberField K] (σ τ : K ≃ₐ[ℚ] K) (p : ℕ) :
    ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) ↔
    ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p -
        NumberField.RingOfIntegers.mapRingHom σ.toRingHom x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p -
        NumberField.RingOfIntegers.mapRingHom (σ.toRingHom.comp τ.toRingHom) x)) := by
  rfl

theorem frobenius_action_choice_quotient
    {K : Type*} [Field K] [NumberField K] (σ τ : K ≃ₐ[ℚ] K) (p : ℕ)
    (hFrob : (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) :
    ((∀ x : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (x ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
          (NumberField.RingOfIntegers.mapRingHom σ.toRingHom x)) ∨
      (∀ x : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (x ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
          (NumberField.RingOfIntegers.mapRingHom (σ.toRingHom.comp τ.toRingHom) x))) := by
  rcases (frobenius_action_choice_iff_mapRingHom σ τ p).mp hFrob with h | h
  · exact Or.inl fun x => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h x))
  · exact Or.inr fun x => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h x))

end WeightedTorusJets

open scoped BigOperators

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

open scoped BigOperators

namespace WeightedTorusJets



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

theorem greedyPivots_linearIndepOn (v : ℕ → V) (n : ℕ) :
    LinearIndepOn K v (greedyPivots K v n : Set ℕ) := by
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs with h
      · exact ih
      · simpa only [Finset.coe_insert] using ih.insert h

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

theorem greedyPivots_mono (v : ℕ → V) : Monotone (greedyPivots K v) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  simp only [greedyPivots]
  split_ifs
  · rfl
  · exact Finset.subset_insert _ _

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

theorem card_greedyPivots (v : ℕ → V) (n : ℕ) :
    (greedyPivots K v n).card =
      Module.finrank K (span K (v '' (Finset.range n : Set ℕ))) := by
  classical
  have h := finrank_span_eq_card (greedyPivots_linearIndepOn (K := K) v n)
  rw [← Set.image_eq_range, span_greedyPivots] at h
  rw [Fintype.card_of_finset' (greedyPivots K v n) (fun _ => Iff.rfl)] at h
  exact h.symm

theorem earlier_row_mem_span_greedyPivots (v : ℕ → V) {i n : ℕ} (hi : i < n) :
    v i ∈ span K (v '' (greedyPivots K v n : Set ℕ)) := by
  rw [span_greedyPivots]
  exact subset_span ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem smaller_weight_row_mem_span_greedyPivots (v : ℕ → V) (w : ℕ → ℕ)
    (hw : Monotone w) {i n : ℕ} (hi : w i < w n) :
    v i ∈ span K (v '' (greedyPivots K v n : Set ℕ)) := by
  apply earlier_row_mem_span_greedyPivots
  exact lt_of_not_ge (fun h => (not_le_of_gt hi) (hw h))

theorem card_greedyPivots_of_span_eq_top (v : ℕ → V) (n : ℕ)
    (hspan : span K (v '' (Finset.range n : Set ℕ)) = ⊤) :
    (greedyPivots K v n).card = Module.finrank K V := by
  rw [card_greedyPivots, hspan, finrank_top]

theorem greedyPivots_eq_of_span_eq_top (v : ℕ → V) {n m : ℕ} (hnm : n ≤ m)
    (hspan : span K (v '' (Finset.range n : Set ℕ)) = ⊤) :
    greedyPivots K v n = greedyPivots K v m := by
  have hspanm : span K (v '' (Finset.range m : Set ℕ)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact span_mono (Set.image_mono (Finset.range_mono hnm))
  apply Finset.eq_of_subset_of_card_le (greedyPivots_mono v hnm)
  rw [card_greedyPivots_of_span_eq_top v n hspan,
    card_greedyPivots_of_span_eq_top v m hspanm]

end WeightedTorusJets

namespace WeightedTorusJets

theorem image_extendFiniteFamily_range {α : Type*} {n : ℕ} (f : Fin n → α)
    (fallback : α) :
    extendFiniteFamily f fallback '' (Finset.range n : Set ℕ) = Set.range f := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i < n := Finset.mem_range.mp hi
    exact ⟨⟨i, hin⟩, by simp [extendFiniteFamily, hin]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_range.mpr i.isLt, by simp [extendFiniteFamily, i.isLt]⟩

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



theorem extendFiniteFamily_injOn_range {α : Type*} {n : ℕ} (f : Fin n → α)
    (hf : Function.Injective f) (fallback : α) :
    Set.InjOn (extendFiniteFamily f fallback) (Finset.range n : Set ℕ) := by
  intro i hi j hj hij
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have heq : f ⟨i, hi'⟩ = f ⟨j, hj'⟩ := by
    simpa [extendFiniteFamily, hi', hj'] using hij
  exact congrArg Fin.val (hf heq)

theorem finiteGreedyPivots_spec {K α V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (s : Finset α) (R : α → V)
    (e : Fin s.card ≃ s) (fallback : α)
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    finiteGreedyPivots K s R e fallback ⊆ s ∧
      (finiteGreedyPivots K s R e fallback).card = Module.finrank K V ∧
      LinearIndepOn K R (finiteGreedyPivots K s R e fallback : Set α) ∧
      Submodule.span K (R '' (finiteGreedyPivots K s R e fallback : Set α)) = ⊤ := by
  classical
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  let I := greedyPivots K v s.card
  have hI : I ⊆ Finset.range s.card := greedyPivots_subset_range v s.card
  have hainj : Set.InjOn a (Finset.range s.card : Set ℕ) :=
    extendFiniteFamily_injOn_range _ (Subtype.val_injective.comp e.injective) fallback
  have haimage : a '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
    rw [show a = extendFiniteFamily (fun i => (e i : α)) fallback from rfl,
      image_extendFiniteFamily_range]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  have hvimage : v '' (Finset.range s.card : Set ℕ) = R '' (s : Set α) := by
    rw [show v = R ∘ a from rfl, Set.image_comp, haimage]
  have hvspan : Submodule.span K (v '' (Finset.range s.card : Set ℕ)) = ⊤ := by
    rw [hvimage, hspan]
  change I.image a ⊆ s ∧ (I.image a).card = _ ∧
    LinearIndepOn K R (I.image a : Set α) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    change a i ∈ (s : Set α)
    rw [← haimage]
    exact Set.mem_image_of_mem a (hI hi)
  · rw [Finset.card_image_of_injOn (hainj.mono hI)]
    exact card_greedyPivots_of_span_eq_top v s.card hvspan
  · rw [Finset.coe_image]
    exact LinearIndepOn.image_of_comp a R (greedyPivots_linearIndepOn v s.card)
  · change Submodule.span K (R '' (I.image a : Set α)) = ⊤
    rw [Finset.coe_image, ← Set.image_comp]
    exact (span_greedyPivots v s.card).trans hvspan

theorem finiteGreedyPivots_sum {K α V β : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommMonoid β]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α) (f : α → β) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    ∑ x ∈ finiteGreedyPivots K s R e fallback, f x =
      ∑ i ∈ greedyPivots K (R ∘ a) s.card, f (a i) := by
  classical
  dsimp only [finiteGreedyPivots]
  apply Finset.sum_image
  have hinj := extendFiniteFamily_injOn_range (fun i => (e i : α))
    (Subtype.val_injective.comp e.injective) fallback
  exact hinj.mono (greedyPivots_subset_range _ _)

theorem sum_embedding_eq_sum_of_range {β : Type*} [AddCommMonoid β]
    (I : Finset ℕ) (m : ℕ) (e : Fin m ↪ ℕ) (he : Set.range e = (I : Set ℕ))
    (f : ℕ → β) : (∑ i : Fin m, f (e i)) = ∑ i ∈ I, f i := by
  apply Finset.sum_bij (fun i _ => e i)
  · intro i _
    change e i ∈ (I : Set ℕ)
    rw [← he]
    exact Set.mem_range_self i
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    have hj' : j ∈ Set.range e := he ▸ hj
    obtain ⟨i, rfl⟩ := hj'
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    rfl

end WeightedTorusJets

open Module
open scoped BigOperators

namespace WeightedTorusJets

theorem det_ne_zero_of_linearIndepOn_rows
    {K ι n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (s : Finset ι) (R : ι → n → K) (e : n ≃ s)
    (hlin : LinearIndepOn K R (s : Set ι)) :
    Matrix.det (fun i j => R (e i) j) ≠ 0 := by
  classical
  have hrows : LinearIndependent K (fun i j => R (e i) j) :=
    hlin.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero


theorem finite_weighted_greedy_package {K α : Type*} [Field K] {M : ℕ}
    (s : Finset α) (R : α → Fin M → K) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    let v := R ∘ a
    let wt := extendFiniteFamily (fun i => w (e i)) B
    let P := finiteGreedyPivots K s R e fallback
    ∃ (g : Fin M ↪o ℕ) (p : Fin M ↪ α),
      Set.range g = (greedyPivots K v s.card : Set ℕ) ∧
      (∀ i, p i = a (g i)) ∧ Set.range p = (P : Set α) ∧
      Monotone wt ∧ Monotone (fun i => w (p i)) ∧
      (∀ i, g i < s.card) ∧
      (∀ r < s.card, wt r = w (a r)) ∧
      (∀ i, v (g i) = R (p i) ∧ wt (g i) = w (p i) ∧ w (p i) ≤ B) ∧
      (∀ b, w b ≤ B → ∃ r < s.card, a r = b ∧ wt r = w b ∧ v r = R b) ∧
      Matrix.det (fun i j => R (p i) j) ≠ 0 ∧ P.card = M ∧
      (∀ (β : Type) [AddCommMonoid β] (F : α → β),
        (∑ i, F (p i)) = ∑ b ∈ P, F b) := by
  classical
  dsimp only
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  let G := greedyPivots K v s.card
  have haimage : a '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
    rw [show a = extendFiniteFamily (fun i => (e i : α)) fallback from rfl,
      image_extendFiniteFamily_range]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  have hvspan : Submodule.span K (v '' (Finset.range s.card : Set ℕ)) = ⊤ := by
    rw [show v = R ∘ a from rfl, Set.image_comp, haimage, hspan]
  have hcard : G.card = M := by
    simpa [G] using card_greedyPivots_of_span_eq_top v s.card hvspan
  let g := G.orderEmbOfFin hcard
  have hg : Set.range g = (G : Set ℕ) := G.range_orderEmbOfFin hcard
  have hgT : ∀ i, g i < s.card := fun i =>
    Finset.mem_range.mp (greedyPivots_subset_range v s.card
      (G.orderEmbOfFin_mem hcard i))
  have hainj : Set.InjOn a (Finset.range s.card : Set ℕ) :=
    extendFiniteFamily_injOn_range _ (Subtype.val_injective.comp e.injective) fallback
  let p : Fin M ↪ α := ⟨a ∘ g, fun i j hij => g.injective
    (hainj (Finset.mem_range.mpr (hgT i)) (Finset.mem_range.mpr (hgT j)) hij)⟩
  have hpe : ∀ i, p i = (e ⟨g i, hgT i⟩ : α) := by
    intro i
    change a (g i) = _
    simp only [a, extendFiniteFamily, dite_eq_left (hgT i)]
  have hpbound : ∀ i, w (p i) ≤ B := by
    intro i
    rw [hpe i]
    exact (hs _).mp (e ⟨g i, hgT i⟩).property
  have hpmono : Monotone (fun i => w (p i)) := by
    intro i j hij
    change w (p i) ≤ w (p j)
    rw [hpe i, hpe j]
    exact hsort (show (⟨g i, hgT i⟩ : Fin s.card) ≤ ⟨g j, hgT j⟩ from g.monotone hij)
  refine ⟨g, p, hg, fun _ => rfl, ?_, ?_, hpmono, hgT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Set.range (a ∘ g) = ((greedyPivots K v s.card).image a : Set α)
    rw [Set.range_comp, hg, Finset.coe_image]
  · exact monotone_extendFiniteFamily _ _ hsort (fun i => (hs _).mp (e i).property)
  · intro r hr
    simp [extendFiniteFamily, hr]
  · intro i
    refine ⟨rfl, ?_, hpbound i⟩
    rw [hpe i]
    simp only [extendFiniteFamily, dite_eq_left (hgT i)]
  · intro b hb
    let r : Fin s.card := e.symm ⟨b, (hs b).mpr hb⟩
    refine ⟨r, r.isLt, ?_, ?_, ?_⟩
    · simp [extendFiniteFamily, r.isLt, r]
    · simp [extendFiniteFamily, r.isLt, r]
    · simp [extendFiniteFamily, r.isLt, r]
  · exact det_ne_zero_of_linearIndepOn_rows G v (G.orderIsoOfFin hcard).toEquiv
      (greedyPivots_linearIndepOn v s.card)
  · simpa using (finiteGreedyPivots_spec s R e fallback hspan).2.1
  · intro β _ F
    rw [finiteGreedyPivots_sum]
    exact sum_embedding_eq_sum_of_range G M g.toEmbedding hg (F ∘ a)



open Submodule
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem greedyPivots_filter_lt (v : ℕ → V) (n r : ℕ) (hrn : r ≤ n) :
    (greedyPivots K v n).filter (fun j => j < r) = greedyPivots K v r := by
  classical
  ext j
  simp only [Finset.mem_filter, mem_greedyPivots_iff]
  constructor
  · rintro ⟨⟨_, hind⟩, hjr⟩
    exact ⟨hjr, hind⟩
  · rintro ⟨hjr, hind⟩
    exact ⟨⟨hjr.trans_le hrn, hind⟩, hjr⟩

theorem span_greedyPivots_eq_span_earlier_rows {ι : Type*} [LinearOrder ι]
    (v : ℕ → V) (n : ℕ) (e : ι ↪o ℕ)
    (he : Set.range e = (greedyPivots K v n : Set ℕ)) (i : ι) :
    span K (v '' (greedyPivots K v (e i) : Set ℕ)) =
      span K ((v ∘ e) '' {j | j < i}) := by
  have hei : e i ∈ greedyPivots K v n := by
    change e i ∈ (greedyPivots K v n : Set ℕ)
    rw [← he]
    exact Set.mem_range_self i
  have hein : e i ≤ n :=
    (Finset.mem_range.mp (greedyPivots_subset_range v n hei)).le
  rw [← greedyPivots_filter_lt v n (e i) hein]
  congr 1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hr, hri⟩ := Finset.mem_filter.mp hr
    have hrange : r ∈ Set.range e := by rwa [he]
    obtain ⟨j, rfl⟩ := hrange
    exact ⟨j, e.lt_iff_lt.mp hri, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨e j, Finset.mem_filter.mpr ⟨?_, e.strictMono hj⟩, rfl⟩
    change e j ∈ (greedyPivots K v n : Set ℕ)
    rw [← he]
    exact Set.mem_range_self j

theorem smaller_weight_mem_span_earlier_retained_rows {ι : Type*} [LinearOrder ι]
    (v : ℕ → V) (w : ℕ → ℕ) (hw : Monotone w) (n : ℕ) (e : ι ↪o ℕ)
    (he : Set.range e = (greedyPivots K v n : Set ℕ))
    (rows : ι → V) (hrows : rows = v ∘ e) (i : ι) (r : ℕ)
    (hr : w r < w (e i)) :
    v r ∈ span K (rows '' {j | j < i}) := by
  rw [hrows, ← span_greedyPivots_eq_span_earlier_rows v n e he i]
  exact smaller_weight_row_mem_span_greedyPivots v w hw hr

end WeightedTorusJets

namespace WeightedTorusJets

theorem jet_weight_ball_span_eq_top {K : Type*} [Field K] {M : ℕ}
    (θ y z : Fin M → K) (hθ : Function.Injective θ) (H : ℕ) (hH : 0 < H) :
    Submodule.span K
      ((fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2) ''
        (weightedJetIndices H (M - 1) : Set (Fin 3 → ℕ))) = ⊤ := by
  classical
  let V : Matrix (Fin M) (Fin M) K := (Matrix.vandermonde θ).transpose
  have hdet : V.det ≠ 0 := by
    simpa only [V, Matrix.det_transpose] using
      (Matrix.det_vandermonde_ne_zero_iff.mpr hθ)
  have hspan : Submodule.span K (Set.range V) = ⊤ :=
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet).span_eq_top_of_card_eq_finrank'
      (by simp)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  refine ⟨![k.val, 0, 0], ?_, ?_⟩
  · apply (mem_weightedJetIndices_iff hH _).mpr
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Nat.mul_zero, Nat.add_zero]
    omega
  · funext j
    simp [V, Matrix.vandermonde_apply]

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RestrictWeightSortedEquiv
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

namespace WeightedTorusJets

theorem basis_nat_sum_injective {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) :
    Function.Injective (fun n : ι → ℕ => ∑ i, (n i : ℚ) • b i) := by
  intro n m h
  funext i
  have hi := congrArg (fun v => b.repr v i) h
  simp only [Basis.repr_sum_self] at hi
  exact_mod_cast hi

theorem basis_nat_sum_mul_injective {ι K : Type*} [Fintype ι]
    [CommRing K] [Algebra ℚ K] (b : Basis ι ℚ K) :
    Function.Injective (fun n : ι → ℕ => ∑ i, (n i : K) * b i) := by
  have h : (fun n : ι → ℕ => ∑ i, (n i : ℚ) • b i) =
      (fun n : ι → ℕ => ∑ i, (n i : K) * b i) := by
    funext n
    simp [Algebra.smul_def]
  rw [← h]
  exact basis_nat_sum_injective b

theorem basis_fin_sum_mul_injective {ι K : Type*} [Fintype ι]
    [CommRing K] [Algebra ℚ K] (b : Basis ι ℚ K) (N : ℕ) :
    Function.Injective (fun n : ι → Fin N => ∑ i, ((n i : ℕ) : K) * b i) := by
  intro n m h
  have hcoords := basis_nat_sum_mul_injective b h
  funext i
  exact Fin.ext (congrFun hcoords i)



theorem exists_first_greedy_jet_rows_of_sorted_enumeration {K : Type*} [Field K] {M : ℕ}
    (θ y z : Fin M → K) (hθ : Function.Injective θ) (H : ℕ) (hH : 0 < H) :
    let s := weightedJetIndices H (M - 1)
    let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
    let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
    ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
      let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
      ∃ (g : Fin M ↪o ℕ) (α : Fin M ↪ (Fin 3 → ℕ)),
        Set.range g = (greedyPivots K (R ∘ β) s.card : Set ℕ) ∧
        (∀ i, α i = β (g i)) ∧
        Set.range α = (finiteGreedyPivots K s R e 0 : Set (Fin 3 → ℕ)) ∧
        Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ M - 1) ∧
        (∀ i a b c, a + H * b + H * c < w (α i) →
          (fun j => θ j ^ a * y j ^ b * z j ^ c) ∈
            Submodule.span K ((R ∘ α) '' {j | j < i})) ∧
        Matrix.det (fun i j => R (α i) j) ≠ 0 := by
  classical
  dsimp only
  let s := weightedJetIndices H (M - 1)
  let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
  let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
  intro e he
  have hs : ∀ α, α ∈ s ↔ w α ≤ M - 1 := mem_weightedJetIndices_iff hH
  obtain ⟨g, α, hg, hα, hrange, hmono, hαmono, hlt, hprefix,
    hselected, hcoverage, hdet, hcard, hsum⟩ :=
    finite_weighted_greedy_package s R e 0 w (M - 1) hs he
      (jet_weight_ball_span_eq_top θ y z hθ H hH)
  refine ⟨g, α, hg, hα, hrange, hαmono,
    fun i => (hselected i).2.2, ?_, hdet⟩
  intro i a b c hweight
  have habc : w ![a, b, c] ≤ M - 1 :=
    Nat.le_trans (Nat.le_of_lt hweight) (hselected i).2.2
  obtain ⟨r, _, _, hwr, hvr⟩ := hcoverage ![a, b, c] habc
  have hrows : R ∘ α = (R ∘ extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0) ∘ g := by
    funext j
    exact (hselected j).1.symm
  have hstrict : (extendFiniteFamily (fun j => w (e j)) (M - 1)) r <
      (extendFiniteFamily (fun j => w (e j)) (M - 1)) (g i) := by
    rw [hwr, (hselected i).2.1]
    exact hweight
  have hmem := smaller_weight_mem_span_earlier_retained_rows _ _ hmono s.card g hg
    (R ∘ α) hrows i r hstrict
  rw [hvr] at hmem
  simpa only [R, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] using hmem



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_fixed_greedy_determinant_divisibility_of_field_ne (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
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
          ∀ N H : ℕ, 0 < H →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
                let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ β) s.card : Set ℕ) ∧
                  (∀ i, α i = β (g i)) ∧
                  Set.range α = (finiteGreedyPivots B s R e 0 : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hFrob⟩ :=
    source_biquadratic_arithmetic_canonical_of_field_ne q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH n
  dsimp only
  intro e he
  let L := CyclotomicField (8 * q) ℚ
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  have hθ : Function.Injective θ := by
    have hinj := (basis_fin_sum_mul_injective v N).comp n.injective
    simpa only [Function.comp_def, hv, θ, a', b'] using hinj
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hspan, hdet⟩ :=
    exists_first_greedy_jet_rows_of_sorted_enumeration
      θ (σ ∘ θ) ((σ * τ) ∘ θ) hθ H hH e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, ?_⟩
  have ha' : a' ^ 2 = (d : B) := by
    apply Subtype.ext
    exact ha
  have hb' : b' ^ 2 = (2 : B) := by
    apply Subtype.ext
    exact hb
  obtain ⟨Δ, hΔ, hneΔ, hdiv⟩ := exists_integral_jet_determinant_divisible
    σ.toRingHom τ.toRingHom ha' hb' (fun j i => (n j i : ℕ)) α H hspan hdet
  refine ⟨Δ, hΔ, hneΔ, ?_⟩
  intro p hp hHp hpq hχp
  exact hdiv p hHp (frobenius_action_choice_quotient σ τ p (hFrob p hp hpq hχp))

end WeightedTorusJets

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



theorem weight_sorted_equiv_image_range {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) :
    e '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
  ext a
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (weight_sorted_equiv_mem_iff_lt_card s w B hs e he i).mpr
      (Finset.mem_range.mp hi)
  · intro ha
    refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    apply Finset.mem_range.mpr
    apply (weight_sorted_equiv_mem_iff_lt_card s w B hs e he (e.symm a)).mp
    simpa using ha

theorem span_global_weight_cutoff_eq_top {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i)))
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    Submodule.span K ((R ∘ e) '' (Finset.range s.card : Set ℕ)) = ⊤ := by
  rw [Set.image_comp, weight_sorted_equiv_image_range s w B hs e he]
  exact hspan



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_global_greedy_determinant_divisibility (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
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
          ∀ N H : ℕ, 0 < H →
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
                    ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_fixed_greedy_determinant_divisibility_of_field_ne
      q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH n
  dsimp only
  intro e he
  let L := CyclotomicField (8 * q) ℚ
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  let R := fun α : Fin 3 → ℕ => fun j =>
    θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
  let s := weightedJetIndices H (N ^ 4 - 1)
  let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
  have hs : ∀ α, α ∈ s ↔ w α ≤ N ^ 4 - 1 := mem_weightedJetIndices_iff hH
  let e₀ := restrictWeightSortedEquiv s w (N ^ 4 - 1) hs e he
  have he₀ : Monotone (fun i => w (e₀ i)) :=
    restrictWeightSortedEquiv_monotone s w (N ^ 4 - 1) hs e he
  obtain ⟨g, α, hg, hα, _, hmono, hweight, Δ, hΔ, hneΔ, hdiv⟩ :=
    hsource N H hH n e₀ he₀
  have hgGlobal : Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) :=
    hg.trans (congrArg (fun t : Finset ℕ => (t : Set ℕ))
      (greedyPivots_restrictWeightSortedEquiv s R w (N ^ 4 - 1) hs e he 0))
  have hαGlobal : ∀ i, α i = e (g i) := by
    intro i
    have hi : g i ∈ greedyPivots B (R ∘ e) s.card := by
      change g i ∈ (greedyPivots B (R ∘ e) s.card : Set ℕ)
      rw [← hgGlobal]
      exact Set.mem_range_self i
    have hiT := Finset.mem_range.mp (greedyPivots_subset_range (R ∘ e) s.card hi)
    exact (hα i).trans
      (extend_restrictWeightSortedEquiv_eq s w (N ^ 4 - 1) hs e he 0 (g i) hiT)
  have hθ : Function.Injective θ := by
    have hinj := (basis_fin_sum_mul_injective v N).comp n.injective
    simpa only [Function.comp_def, hv, θ, a', b'] using hinj
  have hball : Submodule.span B (R '' (s : Set (Fin 3 → ℕ))) = ⊤ :=
    jet_weight_ball_span_eq_top θ (σ ∘ θ) ((σ * τ) ∘ θ) hθ H hH
  have hspan : Submodule.span B ((R ∘ e) '' (Finset.range s.card : Set ℕ)) = ⊤ :=
    span_global_weight_cutoff_eq_top s R w (N ^ 4 - 1) hs e he hball
  refine ⟨g, α, hgGlobal, hαGlobal, ?_, hmono, hweight, ?_, Δ, hΔ, hneΔ, hdiv⟩
  · rw [show (α : Fin (N ^ 4) → Fin 3 → ℕ) = e ∘ g from funext hαGlobal,
      Set.range_comp, hgGlobal, Finset.coe_image]
  · intro t ht
    exact hgGlobal.trans (congrArg (fun u : Finset ℕ => (u : Set ℕ))
      (greedyPivots_eq_of_span_eq_top (R ∘ e) ht hspan))

end WeightedTorusJets

open scoped BigOperators
open InnerProductSpace

namespace SiegelJets

theorem norm_det_le_prod_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (A i)
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let b := gramSchmidtOrthonormalBasis hdim v
  have hchange : e.toBasis.det v = e.toBasis.det b * b.toBasis.det v := by
    have h := congrArg (fun f : (EuclideanSpace ℂ (Fin n)) [⋀^Fin n]→ₗ[ℂ] ℂ => f v)
      (e.toBasis.det.eq_smul_basis_det b.toBasis)
    simpa using h
  have hnorm : ‖e.toBasis.det v‖ = ‖b.toBasis.det v‖ := by
    rw [hchange, norm_mul, e.det_to_matrix_orthonormalBasis b, one_mul]
  have hdet : e.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
    congr
  rw [← hdet, hnorm]
  change ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖
  rw [show b.toBasis.det v = ∏ i, inner ℂ (b i) (v i) from
    gramSchmidtOrthonormalBasis_det hdim v, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => by
    simpa using norm_inner_le_norm (b i) (v i)

theorem norm_det_le_of_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B ^ d i) :
    ‖A.det‖ ≤ (Real.sqrt n) ^ n * B ^ (∑ i, d i) := by
  have hrow (i : Fin n) :
      ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ ≤
        Real.sqrt n * B ^ d i := by
    rw [EuclideanSpace.norm_eq]
    calc
      Real.sqrt (∑ j, ‖A i j‖ ^ 2) ≤ Real.sqrt (∑ _ : Fin n, (B ^ d i) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
      _ = Real.sqrt n * B ^ d i := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (pow_nonneg hB _)]
  calc
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ :=
      norm_det_le_prod_norm A
    _ ≤ ∏ i, (Real.sqrt n * B ^ d i) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hrow i)
    _ = (Real.sqrt n) ^ n * B ^ (∑ i, d i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp

theorem log_norm_det_le_of_entry_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hdet : A.det ≠ 0)
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 < B)
    (hA : ∀ i j, ‖A i j‖ ≤ B ^ d i) :
    Real.log ‖A.det‖ ≤ (n : ℝ) / 2 * Real.log n + (∑ i, d i : ℕ) * Real.log B := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc
    Real.log ‖A.det‖ ≤ Real.log ((Real.sqrt n) ^ n * B ^ (∑ i, d i)) :=
      Real.log_le_log (norm_pos_iff.mpr hdet) (norm_det_le_of_entry_bound A d hB.le hA)
    _ = (n : ℝ) / 2 * Real.log n + (∑ i, d i : ℕ) * Real.log B := by
      rw [Real.log_mul (pow_ne_zero _ (Real.sqrt_pos.mpr hn').ne')
        (pow_ne_zero _ hB.ne'), Real.log_pow, Real.log_pow,
        Real.log_sqrt hn'.le]
      ring

theorem log_norm_det_archimedean {m N q : ℕ} (hm : 0 < m) (hN : 0 < N) (hq : 0 < q)
    (A : Matrix (Fin m) (Fin m) ℂ) (hdet : A.det ≠ 0)
    (d : Fin m → ℕ)
    (hA : ∀ i j, ‖A i j‖ ≤ (8 * N * Real.sqrt q) ^ d i) :
    Real.log ‖A.det‖ ≤ (m : ℝ) / 2 * Real.log m +
      (∑ i, d i : ℕ) * (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hB : (0 : ℝ) < 8 * N * Real.sqrt q := by positivity
  have hlog : Real.log (8 * N * Real.sqrt q) =
      Real.log N + 1 / 2 * Real.log q + Real.log 8 := by
    rw [Real.log_mul (mul_pos (by norm_num) hN').ne' (Real.sqrt_pos.mpr hq').ne',
      Real.log_mul (by norm_num) hN'.ne', Real.log_sqrt hq'.le]
    ring
  simpa only [hlog] using log_norm_det_le_of_entry_bound hm A hdet d hB hA

theorem log_norm_map_det_archimedean {K : Type*} [Field K] {m N q : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hq : 0 < q)
    (ν : K →+* ℂ) (A : Matrix (Fin m) (Fin m) K) (hdet : A.det ≠ 0)
    (d : Fin m → ℕ)
    (hA : ∀ i j, ‖ν (A i j)‖ ≤ (8 * N * Real.sqrt q) ^ d i) :
    Real.log ‖ν A.det‖ ≤ (m : ℝ) / 2 * Real.log m +
      (∑ i, d i : ℕ) * (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  have hmapped : (ν.mapMatrix A).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero ν).mpr hdet
  simpa only [← RingHom.map_det] using
    log_norm_det_archimedean hm hN hq (ν.mapMatrix A) hmapped d hA

end SiegelJets

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
namespace WeightedTorusJets

theorem norm_of_sq_eq_real {z : ℂ} {r : ℝ} (hz : z ^ 2 = (r : ℂ)) :
    ‖z‖ = Real.sqrt |r| := by
  rw [← Real.sqrt_sq (norm_nonneg z), ← norm_pow, hz, Complex.norm_real, Real.norm_eq_abs]

theorem norm_biquadratic_box_le {a b : ℂ} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n₁ n₂ n₃ n₄ : ℕ) (hn₁ : n₁ ≤ N) (hn₂ : n₂ ≤ N)
    (hn₃ : n₃ ≤ N) (hn₄ : n₄ ≤ N) :
    ‖(n₁ : ℂ) + n₂ * a + n₃ * b + n₄ * (a * b)‖ ≤
      8 * N * Real.sqrt q := by
  have hna : ‖a‖ ≤ Real.sqrt q := by
    rw [norm_of_sq_eq_real (r := (d : ℝ)) (by simpa using ha)]
    exact Real.sqrt_le_sqrt hd
  have hnb : ‖b‖ ≤ 2 := by
    rw [norm_of_sq_eq_real (r := 2) (by simpa using hb), Real.sqrt_le_iff]
    norm_num
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsq : 1 ≤ Real.sqrt q := (Real.one_le_sqrt).mpr hq'
  have hnN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hab : ‖a * b‖ ≤ 2 * Real.sqrt q := by
    simpa only [mul_comm] using norm_mul_le_of_le hna hnb
  calc
    ‖(n₁ : ℂ) + n₂ * a + n₃ * b + n₄ * (a * b)‖ ≤
        ‖(n₁ : ℂ)‖ + ‖(n₂ : ℂ) * a‖ + ‖(n₃ : ℂ) * b‖ +
          ‖(n₄ : ℂ) * (a * b)‖ := norm_add₄_le
    _ = n₁ + n₂ * ‖a‖ + n₃ * ‖b‖ + n₄ * ‖a * b‖ := by simp
    _ ≤ N + N * Real.sqrt q + N * 2 + N * (2 * Real.sqrt q) := by
      gcongr
    _ ≤ 8 * N * Real.sqrt q := by nlinarith [mul_le_mul_of_nonneg_left hsq hnN]

theorem norm_embedding_biquadratic_box_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) :
    ‖ν ((n 0 : K) + n 1 * a + n 2 * b + n 3 * (a * b))‖ ≤
      8 * N * Real.sqrt q := by
  simp only [map_add, map_mul, map_natCast]
  refine norm_biquadratic_box_le ?_ ?_ hd hq _ _ _ _
    (hn 0).le (hn 1).le (hn 2).le (hn 3).le
  · simpa using congrArg ν ha
  · simpa only [map_pow, map_ofNat] using congrArg ν hb

theorem norm_three_powers_le {x y z : ℂ} {B : ℝ}
    (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) (hz : ‖z‖ ≤ B)
    (i j k : ℕ) : ‖x ^ i * y ^ j * z ^ k‖ ≤ B ^ (i + j + k) := by
  have hB : 0 ≤ B := (norm_nonneg x).trans hx
  simp only [norm_mul, norm_pow, pow_add]
  gcongr

theorem norm_embedding_basis_sum_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) :
    ‖ν (∑ i : Fin 4, (n i : K) * ![1, a, b, a * b] i)‖ ≤
      8 * N * Real.sqrt q := by
  simpa [Fin.sum_univ_succ, add_assoc] using
    norm_embedding_biquadratic_box_le ν ha hb hd hq n hn

theorem norm_embedding_derivative_entry_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) (α : Fin 3 → ℕ) :
    let θ := ∑ i : Fin 4, (n i : K) * ![1, a, b, a * b] i
    ‖ν (θ ^ (α 0) * σ θ ^ (α 1) * (σ.comp τ) θ ^ (α 2))‖ ≤
      (8 * N * Real.sqrt q) ^ (α 0 + α 1 + α 2) := by
  dsimp only
  simp only [map_mul, map_pow]
  apply norm_three_powers_le
  · exact norm_embedding_basis_sum_le ν ha hb hd hq n hn
  · exact norm_embedding_basis_sum_le (ν.comp σ) ha hb hd hq n hn
  · exact norm_embedding_basis_sum_le (ν.comp (σ.comp τ)) ha hb hd hq n hn

end WeightedTorusJets


namespace WeightedTorusJets

variable {K : Type*} [Field K] [NumberField K]

theorem abs_field_norm_eq_prod_embeddings (a : K) :
    |(Algebra.norm ℚ a : ℝ)| = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ a‖ := by
  simpa only [eq_ratCast, Complex.norm_ratCast, norm_prod] using
    congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)

theorem log_abs_field_norm_eq_sum_embeddings {a : K} (ha : a ≠ 0) :
    Real.log |(Algebra.norm ℚ a : ℝ)| =
      ∑ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ a‖ := by
  rw [abs_field_norm_eq_prod_embeddings, Real.log_prod]
  simp [ha]

theorem quarter_log_field_norm_le_of_embeddings {a : K} (ha : a ≠ 0)
    (hdegree : Module.finrank ℚ K = 4) {B : ℝ}
    (hbound : ∀ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ a‖ ≤ B) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ a : ℝ)| ≤ B := by
  rw [log_abs_field_norm_eq_sum_embeddings ha]
  have hsum := Finset.sum_le_card_nsmul Finset.univ _ B (fun σ _ ↦ hbound σ)
  simp only [Finset.card_univ, AlgHom.card, hdegree, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  linarith

end WeightedTorusJets

namespace WeightedTorusJets

theorem archimedean_jet_determinant_bound {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q) (hN : 0 < N)
    (n : Fin (N ^ 4) → Fin 4 → ℕ) (hn : ∀ j i, n j i < N)
    (α : Fin (N ^ 4) → Fin 3 → ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    A.det ≠ 0 →
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ A.det : ℝ)| ≤
      ((N ^ 4 : ℕ) : ℝ) / 2 * Real.log (N ^ 4 : ℕ) +
        ((∑ i, α i 0 : ℕ) + (∑ i, (α i 1 + α i 2) : ℕ)) *
          (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  dsimp only
  intro hdet
  apply quarter_log_field_norm_le_of_embeddings hdet hdegree
  intro ν
  convert SiegelJets.log_norm_map_det_archimedean (pow_pos hN 4) hN
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hq) ν.toRingHom _ hdet
    (fun i => α i 0 + α i 1 + α i 2)
    (fun i j => norm_embedding_derivative_entry_le ν.toRingHom σ τ ha hb hd hq
      (n j) (hn j) (α i)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_add_distrib, Nat.cast_add, add_assoc]



open scoped NumberField BigOperators

theorem archimedean_bound_of_integral_jet_determinant {K : Type*}
    [Field K] [NumberField K] (hdegree : Module.finrank ℚ K = 4)
    (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q) (hN : 0 < N)
    (n : Fin (N ^ 4) → Fin 4 → ℕ) (hn : ∀ j i, n j i < N)
    (α : Fin (N ^ 4) → Fin 3 → ℕ) (Δ : 𝓞 K) (hne : Δ ≠ 0)
    (hΔ : (Δ : K) =
      Matrix.det (fun i j =>
        (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 0 *
        σ (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 1 *
        (σ.comp τ) (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 2)) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| ≤
      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
          (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
  let A : Matrix (Fin (N ^ 4)) (Fin (N ^ 4)) K :=
    Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 * (σ.comp τ) (θ j) ^ α i 2
  change (Δ : K) = A.det at hΔ
  have hcast : (Δ : K) ≠ 0 := fun h => hne (Subtype.ext h)
  have hdet : A.det ≠ 0 := hΔ ▸ hcast
  have hbound := archimedean_jet_determinant_bound hdegree σ τ ha hb hd hq hN n hn α hdet
  change (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ A.det : ℝ)| ≤ _ at hbound
  rw [← hΔ] at hbound
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_add] using hbound

end WeightedTorusJets

open scoped BigOperators NumberField

namespace WeightedTorusJets

theorem quarter_log_field_norm_lower {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) (x : 𝓞 K) (hx : x ≠ 0)
    (P : Finset ℕ) (E : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hdvd : ∀ p ∈ P, (p : 𝓞 K) ^ E p ∣ x) :
    ∑ p ∈ P, (E p : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (x : K) : ℝ)| := by
  have hd : (∏ p ∈ P, (p : ℤ) ^ (4 * E p)) ∣ Algebra.norm ℤ x := by
    apply Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hpm q hqm hpq
      exact ((Nat.coprime_primes (hp p hpm) (hp q hqm)).mpr hpq).isCoprime.pow
    · intro p hpm
      simpa [map_pow, Algebra.norm_natCast, NumberField.RingOfIntegers.rank,
        hdegree, ← pow_mul] using map_dvd (Algebra.norm ℤ) (hdvd p hpm)
  have hle : (∏ p ∈ P, p ^ (4 * E p)) ≤ (Algebra.norm ℤ x).natAbs := by
    simpa only [← Nat.cast_pow, ← Nat.cast_prod, Int.natAbs_natCast] using
      Int.natAbs_le_of_dvd_ne_zero hd (Algebra.norm_ne_zero_iff.mpr hx)
  have hpos : (0 : ℝ) < ∏ p ∈ P, (p : ℝ) ^ (4 * E p) :=
    Finset.prod_pos fun p hpm => pow_pos (by exact_mod_cast (hp p hpm).pos) _
  have hlog := Real.log_le_log (y := ((Algebra.norm ℤ x).natAbs : ℝ)) hpos
    (by exact_mod_cast hle)
  rw [Real.log_prod (fun p hpm => pow_ne_zero _
    (by exact_mod_cast (hp p hpm).ne_zero))] at hlog
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    ← Finset.mul_sum] at hlog
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
  linarith

theorem prime_floor_sum_lower_raw {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (U : ℝ) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE ⌊U⌋₊) :
    (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
      ∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p := by
  have hlog : (∑ p ∈ P, Real.log p) ≤ ∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => Real.log_natCast_nonneg p)
  calc
    _ ≤ (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ P, Real.log p) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s.card)) _
    _ = ∑ p ∈ P, ((∑ i ∈ s, (a i : ℝ)) / p - s.card) * Real.log p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
      have h := Finset.sum_le_sum (s := s)
        (fun i _ => (Nat.sub_one_lt_floor ((a i : ℝ) / p)).le)
      simpa [Finset.sum_sub_distrib, ← Finset.sum_div, Nat.floor_div_eq_div] using h

theorem finite_place_raw_norm_bounds {K ι : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (s : Finset ι) (a : ι → ℕ) (U : ℝ) (P : Finset ℕ)
    (hP : P ⊆ Nat.primesLE ⌊U⌋₊)
    (hdiv : ∀ p ∈ P, (p : 𝓞 K) ^ (∑ i ∈ s, a i / p) ∣ Δ) :
    (∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) ∧
    ((∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
      ∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p) :=
  ⟨quarter_log_field_norm_lower hdegree Δ hΔ P (fun p => ∑ i ∈ s, a i / p)
      (fun _ hp => Nat.prime_of_mem_primesLE (hP hp)) hdiv,
    prime_floor_sum_lower_raw s a U P hP⟩



theorem prime_floor_sum_lower {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {U : ℝ} (hU : 0 ≤ U) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE ⌊U⌋₊) :
    (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        Real.log 4 * s.card * U ≤
      ∑ p ∈ P, (∑ i ∈ s, ((a i / p : ℕ) : ℝ)) * Real.log p := by
  have hlog : (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤ Real.log 4 * U := by
    rw [← Chebyshev.theta_eq_sum_primesLE]
    exact Chebyshev.theta_le_log4_mul_x hU
  have hraw := prime_floor_sum_lower_raw s a U P hP
  simp only [Nat.cast_sum] at hraw
  apply le_trans _ hraw
  apply sub_le_sub_left
  convert mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s.card) using 1
  all_goals try with_reducible_and_instances rfl
  ring



open scoped BigOperators NumberField

theorem finite_place_bounds_of_source_determinant {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) {m : ℕ}
    (Δ : 𝓞 K) (hΔ : Δ ≠ 0) (α : Fin m → Fin 3 → ℕ)
    (q H : ℕ) (χ : ℕ → ℂ)
    (hdiv : ∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ p = -1 →
      Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p))
    (U : ℝ) (hU : 0 ≤ U) :
    let P := (Nat.primesLE ⌊U⌋₊).filter
      (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
    let E := fun p => ∑ i, α i 0 / p
    let S₁ := ∑ i, (α i 0 : ℝ)
    (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) ∧
    (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
      (m : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
        ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
    (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) - Real.log 4 * m * U ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) := by
  dsimp only
  let P := (Nat.primesLE ⌊U⌋₊).filter
    (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
  have hdiv' (p : ℕ) (hp : p ∈ P) : (p : 𝓞 K) ^ (∑ i, α i 0 / p) ∣ Δ := by
    obtain ⟨hpprime, hH, hpq, hχ⟩ := Finset.mem_filter.mp hp
    simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using
      hdiv p (Nat.prime_of_mem_primesLE hpprime) hH hpq hχ
  have hraw := finite_place_raw_norm_bounds hdegree Δ hΔ Finset.univ
    (fun i => α i 0) U P (Finset.filter_subset _ _) hdiv'
  simp only [Finset.card_univ, Fintype.card_fin] at hraw
  refine ⟨hraw.1, hraw.2, ?_⟩
  have hcheb := prime_floor_sum_lower Finset.univ (fun i => α i 0)
    hU P (Finset.filter_subset _ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hcheb
  exact hcheb.trans (by simpa only [Nat.cast_sum] using hraw.1)

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_global_greedy_determinant_local_bounds_jb247_oai (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
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
                    ∀ U : ℝ, 0 ≤ U →
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
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) := by
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_global_greedy_determinant_divisibility q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ, hdiv⟩ :=
    hsource N H hH n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ, ?_, hdiv, ?_⟩
  · let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
    have hb' : b' ^ 2 = (2 : B) := by apply Subtype.ext; exact hb
    have hdreal : |(d : ℝ)| ≤ q := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using
        (show (d.natAbs : ℝ) ≤ q from Nat.cast_le.mpr hbound)
    exact archimedean_bound_of_integral_jet_determinant hdegree σ.toRingHom τ.toRingHom
      ha' hb' hdreal (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (hH.trans_le hHN)
      (fun j i => (n j i : ℕ)) (fun j i => (n j i).isLt) α Δ hneΔ hΔ

  · intro U hU
    simpa only [Nat.cast_pow] using finite_place_bounds_of_source_determinant hdegree
      Δ hneΔ α q H (fun p => χ p) hdiv U hU

end WeightedTorusJets

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247_oai := @OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247_oai
