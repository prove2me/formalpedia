-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:28:33.422534+00:00
-- url     : https://prove2.me/submissions/18471391-d079-4605-a9e7-2f6c8be87d8b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousKernelDensity_zero_off_box_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem matrixSupCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : κ → ℝ) : matrixSupCLM A x = A.mulVec x := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedIntegerColumns_mulVec (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (hT : ∀ j, T j ≠ 0) (y : J → ℤ) :
    normalizedIntegerColumns B T P *ᵥ (fun j => (y j : ℝ) / T j) =
      fun i => ((B *ᵥ y) i : ℝ) / P i := by
  have hc : Matrix.diagonal T *ᵥ (fun j => (y j : ℝ) / T j) = fun j => (y j : ℝ) := by
    funext j
    simp only [Matrix.mulVec_diagonal]
    field_simp [hT j]
  unfold normalizedIntegerColumns
  rw [← Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  funext i
  simp only [Matrix.mulVec_diagonal]
  have hcast : ((B *ᵥ y) i : ℝ) = (B.map (Int.castRingHom ℝ) *ᵥ fun j => (y j : ℝ)) i :=
    (Int.castRingHom ℝ).map_mulVec B y i
  rw [← hcast, div_eq_mul_inv]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ (Fintype.card α : ℝ) + 1 := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ 1 + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = 1 + t.card := by simp
    _ ≤ (Fintype.card α : ℝ) + 1 := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      linarith

theorem real_monomial_eval_abs_le {K : Type*} (e : K →₀ ℕ) (x : K → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hx : ∀ k, |x k| ≤ C) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    |MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ))| ≤ C ^ h := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  change |∏ k ∈ e.support, x k ^ e k| ≤ _
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ k ∈ e.support, C ^ e k := by
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _
    _ = C ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ C ^ h := pow_le_pow_right₀ hC he

theorem boundedDegreeRealJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (realAffineCube_abs_le root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI


namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelJetAllowances
namespace OAI

section

namespace Erdos3

theorem kernelJetEntryAllowance_pos (q h : ℕ) : 0 < kernelJetEntryAllowance q h := by
  unfold kernelJetEntryAllowance
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem coefficientPMF_apply {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (z : J → ℤ) :
    (coefficientPMF f hf S hS hsupport hZ z).toReal = coefficientWeight f S z / coefficientWeightSum f S :=
  realWeightPMF_apply _ _ _ _ z

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JetOutputRadiusLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem jetOutputRadiusLog_nonneg (q n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ jetOutputRadiusLog q n d P := by unfold jetOutputRadiusLog; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoefficientGridRate
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem mem_rectangularWeightIndices_zero_of_norm_le {I : Type*} [Fintype I]
    (P : I → ℝ) (hP : ∀ i, 0 < P i) {T : ℝ} (v : I → ℤ)
    (hv : ‖fun i => (v i : ℝ) / P i‖ ≤ T) :
    v ∈ rectangularWeightIndices (fun _ => 0) P T := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi : |(v i : ℝ) / P i| ≤ T :=
    (norm_le_pi_norm (fun j => (v j : ℝ) / P j) i).trans hv
  obtain ⟨hlo, hhi⟩ := abs_le.mp hi
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith [(le_div_iff₀ (hP i)).mp hlo]),
    Int.le_floor.mpr (by nlinarith [(div_le_iff₀ (hP i)).mp hhi])⟩

theorem coefficientImagePMF_zero_off_box {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {R T : ℝ}
    (hs : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (hbox : ‖matrixSupCLM (normalizedIntegerColumns A S P)‖ * R ≤ T)
    (v : I → ℤ) (hv : v ∉ rectangularWeightIndices (fun _ => 0) P T) :
    coefficientImagePMF A f hf0 S hS hs hZ v = 0 := by
  apply (PMF.apply_eq_zero_iff _ v).mpr
  intro hm
  obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  have hzn : ‖fun j => (z j : ℝ) / S j‖ ≤ R := by
    by_contra! hn
    have hzero := hs _ hn
    have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hz)
      (PMF.apply_ne_top _ _)
    rw [coefficientPMF_apply] at hpos
    change 0 < f (fun j => (z j : ℝ) / S j) / coefficientWeightSum f S at hpos
    rw [hzero, zero_div] at hpos
    exact (lt_irrefl 0) hpos
  apply hv
  apply mem_rectangularWeightIndices_zero_of_norm_le P hP
  rw [← normalizedIntegerColumns_mulVec A S P (fun j => (hS j).ne') z,
    ← matrixSupCLM_apply]
  exact ((matrixSupCLM (normalizedIntegerColumns A S P)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hzn (norm_nonneg _)).trans hbox)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialCoefficientControl
namespace OAI

section

namespace Erdos3

theorem normalizedAffineMonomialJetMatrix_eq {α V O N : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (root : V → ℤ) (difference : α → V → ℤ) (e : N → V →₀ ℕ) (rows : O → Finset α)
    (T : V → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerAffineCube root difference) rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H) =
    realJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
      (realAffineCube (fun v => (root v : ℝ) / T v) (fun i v => (difference i v : ℝ) / T v)) rows := by
  have hv : (fun t v => (integerAffineCube root difference t v : ℝ) / T v) =
      realAffineCube (fun v => (root v : ℝ) / T v) (fun i v => (difference i v : ℝ) / T v) := by
    funext t v
    exact (realAffineCube_normalized_integer root difference T t v).symm
  have he := normalizedIntegerMonomialJetMatrix_eq e (integerAffineCube root difference) rows T hH
  rwa [hv] at he

theorem normalizedAffineMonomialJetMatrix_bound {α V O N : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (root : V → ℤ) (difference : α → V → ℤ) (e : N → V →₀ ℕ) (rows : O → Finset α)
    (T : V → ℝ) {h : ℕ} (he : ∀ n, (e n).sum (fun _ d => d) ≤ h)
    (hroot : ∀ v, |(root v : ℝ) / T v| ≤ 1)
    (hdiff : ∀ i v, |(difference i v : ℝ) / T v| ≤ 1) {H : ℝ} (hH : H ≠ 0) :
    ∀ o n, |normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerAffineCube root difference) rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H) o n| ≤
        kernelJetEntryAllowance (Fintype.card α) h := by
  intro o n
  rw [normalizedAffineMonomialJetMatrix_eq root difference e rows T hH]
  exact boundedDegreeRealJetMatrix_entry_bound _ _ hroot hdiff h rows o ⟨e n, he n⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

theorem principalTupleNormalized_norm_le {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (y : PrincipalIntegerTuples B h α L) : ‖principalTupleNormalized L y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro a
  exact (norm_le_pi_norm (fun i => (y ⟨a.1, a.2.1, a.2.2.1⟩ i : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩) a.2.2.2).trans
    (integerScalarCubeBox_normalized_norm_le (hL _) (y _))

theorem mappedPrincipal_normalized_bound {Z K D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1) (T : K → ℝ)
    (y : PrincipalIntegerTuples B h α L)
    (hn : ∀ k a, ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
      Sum.elim zr (principalTupleNormalized L y) (input k a)) :
    ∀ k a, |((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k| ≤ 1 := by
  intro k a
  rw [hn]
  cases input k a with
  | inl j => exact hz j
  | inr j =>
    exact (norm_le_pi_norm (principalTupleNormalized L y) j).trans
      (principalTupleNormalized_norm_le B h L hL y)

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_normalized (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (zi : Z → ℤ) (zr : Z → ℝ) (T : G → ℝ)
    (hfixed : ∀ g a, (zi (extra g a) : ℝ)/T g = zr (extra g a))
    (L : PrincipalTupleIndex B h → ℕ)
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    ((Sum.elim (Sum.elim zi (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) : ℤ) : ℝ) /
        Sum.elim T (fun j => (L j : ℝ)) k =
      Sum.elim (Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u))
        (principalTupleNormalized (principalAxisLength (fun d => ¬P d) L) v)
        (partitionedPrincipalInput P extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · exact hfixed g a
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, principalTupleNormalized, principalAxisLength, hp]

theorem partitionedPrincipalInput_frozen_bound [Fintype D] [∀ d, Fintype (B d)]
    [Fintype α] [DecidableEq α] (P : D → Prop) [DecidablePred P]
    (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (u : PrincipalAxisTuples (α := α) P L)
    (j : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) :
    |Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u) j| ≤ 1 := by
  cases j with
  | inl j => exact hz j
  | inr j =>
    have hb : ‖principalTupleNormalized (principalAxisLength P L) u‖ ≤ 1 :=
      principalTupleNormalized_norm_le
        (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun k => hL ⟨k.1.val, k.2⟩) u
    exact (norm_le_pi_norm (principalTupleNormalized (principalAxisLength P L) u) j).trans hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : I j)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

omit [Fintype α] [DecidableEq α] in
theorem allocatedPartitionedInput_normalized
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (k : LayerSamplerVariables G I n B) (a : Option α) :
    ((Sum.elim fixedInteger (principalTupleIntegers v) (input k a) : ℤ) : ℝ) /
      layerSamplerBox B U basis S k =
      Sum.elim fixedReal (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
        (input k a) := by
  have hbox : layerSamplerBox B U basis S =
      Sum.elim (fun _ : G => (S.value : ℝ)) (fun d => (sides d : ℝ)) := by
    funext k
    cases k <;> rfl
  rw [hbox]
  exact partitionedPrincipalInput_normalized grid (fun g a => (g, a))
    (fun ga : G × Option α => (x ga.1 ga.2 : ℤ))
    (fun ga : G × Option α => ((x ga.1 ga.2 : ℤ) : ℝ) / (S.value : ℝ))
    (fun _ => (S.value : ℝ)) (fun _ _ => rfl) sides u v k a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

theorem allocatedPartitionedInput_frozen_bound (t) : |fixedReal t| ≤ 1 := by
  apply partitionedPrincipalInput_frozen_bound grid _ _ sides (allocatedPrincipalSides_pos B U basis S) u t
  intro ga
  have h := (norm_le_pi_norm (fun a => ((x ga.1 a : ℤ) : ℝ)/(S.value : ℝ)) ga.2).trans
    (integerScalarCubeBox_normalized_norm_le S.positive (x ga.1))
  simpa only [Real.norm_eq_abs] using h

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

theorem kernelJetEntryAllowance_le_exp (q h : ℕ) :
    kernelJetEntryAllowance q h ≤ Real.exp ((q : ℝ) * (h + 1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq := Real.add_one_le_exp (q : ℝ)
  unfold kernelJetEntryAllowance
  calc
    _ ≤ (Real.exp 1) ^ q * (Real.exp q) ^ h := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem kernelGeometryLog_bounds (q n j k d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelGeometryLog q n j k d p ∧ p ≤ kernelGeometryLog q n j k d p ∧
    kernelInverseLog q n j d p ≤ kernelGeometryLog q n j k d p ∧
    (j : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p ∧
    (k : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p := by
  have hi : 0 ≤ kernelInverseLog q n j d p := by unfold kernelInverseLog; positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have he : 0 ≤ (q : ℝ) * (d + 1) := by positivity
  unfold kernelGeometryLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem nat_mul_kernelEntry_le_exp (a q d : ℕ) :
    (a : ℝ) * kernelJetEntryAllowance q d ≤ Real.exp ((a : ℝ) + (q : ℝ) * (d + 1)) := by
  have ha : (a : ℝ) ≤ Real.exp a := by linarith [Real.add_one_le_exp (a : ℝ)]
  calc
    _ ≤ Real.exp a * Real.exp ((q : ℝ) * (d + 1)) :=
      mul_le_mul ha (kernelJetEntryAllowance_le_exp q d) (kernelJetEntryAllowance_pos q d).le (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem kernelRowOutputLog_nonneg (q n j k u d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelRowOutputLog q n j k u d p := by
  have hP := (kernelGeometryLog_bounds q n j k d hp).1
  have hf := affineProfileLogBound_nonneg k hp
  have hr := jetOutputRadiusLog_nonneg q u d hP
  unfold kernelRowOutputLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))

theorem allocatedPartitionedInput_bound
    (u : PrincipalAxisTuples (α := α) grid sides)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    ∀ k a, |((Sum.elim
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (principalTupleIntegers v) (input k a) : ℤ) : ℝ) / layerSamplerBox B U basis S k| ≤ 1 := by
  exact mappedPrincipal_normalized_bound
    (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val)
    (principalAxisLength (fun a => ¬grid a) sides)
    (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (Sum.elim (fun ga : G × Option α => ((x ga.1 ga.2 : ℤ) : ℝ)/S.value)
      (principalTupleNormalized (principalAxisLength grid sides) u))
    (allocatedPartitionedInput_frozen_bound B U basis S x u) (layerSamplerBox B U basis S) v
    (allocatedPartitionedInput_normalized B U basis S x u v)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelComparisonScales
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem kernelFamilyOutputLog_nonneg {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ)
    {p : ℝ} (hp : 0 ≤ p) : 0 ≤ kernelFamilyOutputLog (α := α) (J := J) O N degree p := by
  unfold kernelFamilyOutputLog
  exact add_nonneg zero_le_one (Finset.sum_nonneg (fun q _ => kernelRowOutputLog_nonneg _ _ _ _ _ _ hp))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedDensityLog_bounds (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    let K := kernelFamilyOutputLog (α := α) (J := G) O
      (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8))
    0 ≤ allocatedDensityLog (G := G) B α O P ∧
      K ≤ allocatedDensityLog (G := G) B α O P ∧
      ∀ j, K + allocatedDensityColumnLog (G := G) B α j + P ≤
        allocatedDensityLog (G := G) B α O P := by
  dsimp only
  have hK := kernelFamilyOutputLog_nonneg (α := α) (J := G) O
    (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1)
    (show 0 ≤ 4*(P+8) by positivity)
  have hj (j : Fin m) : 0 ≤ allocatedDensityColumnLog (G := G) B α j := by
    unfold allocatedDensityColumnLog
    positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  unfold allocatedDensityLog
  refine ⟨by positivity, by linarith, ?_⟩
  intro j
  have h := Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ j)
  linarith

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedJetSupportBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedJetSupportLog_bounds (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedJetSupportLog (G := G) B α O P ∧
      allocatedDensityLog (G := G) B α O P ≤ allocatedJetSupportLog (G := G) B α O P ∧
      ∀ j : Fin m,
        (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
          (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) + P ≤ allocatedJetSupportLog (G := G) B α O P := by
  have hQ := (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hj (j : Fin m) : 0 ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) := by positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  unfold allocatedJetSupportLog
  refine ⟨by positivity, by linarith, ?_⟩
  intro j
  have he := Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ j)
  linarith

theorem allocatedJetSupport_budget (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P R : ℝ} (hP : 0 ≤ P)
    (hR : R ≤ Real.exp P) (j : Fin m) :
    Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) *
      kernelJetEntryAllowance (Fintype.card α) (j.val+1) * R ≤
        Real.exp (allocatedJetSupportLog (G := G) B α O P) := by
  calc
    _ ≤ Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) *
        kernelJetEntryAllowance (Fintype.card α) (j.val+1) * Real.exp P :=
      mul_le_mul_of_nonneg_left hR (mul_nonneg (Nat.cast_nonneg _) (kernelJetEntryAllowance_pos _ _).le)
    _ ≤ Real.exp ((Fintype.card
        (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1)) * Real.exp P :=
      mul_le_mul_of_nonneg_right (nat_mul_kernelEntry_le_exp _ _ _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr ((allocatedJetSupportLog_bounds (G := G) B α O hP).2.2 j)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixed" => Sum.elim (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ))
  (principalTupleIntegers u)

theorem allocatedPartitionedJet_normalized_bound (j : Fin m) {H : ℝ} (hH : H ≠ 0) :
    ∀ o d, |normalizedIntegerColumns (allocatedPartitionedJetMatrix B U basis S x u v rows j)
      (fun d => H / monomialScale (layerSamplerBox B U basis S) d.val) (fun _ => H) o d| ≤
        kernelJetEntryAllowance (Fintype.card α) (j.val+1) := by
  have hn := allocatedPartitionedInput_bound B U basis S x u v
  simpa only [allocatedPartitionedJetMatrix, integerMappedJetMatrix, integerMappedCubeTuple] using
    normalizedAffineMonomialJetMatrix_bound
      (fun k => Sum.elim fixed (principalTupleIntegers v) (input k none))
      (fun a k => Sum.elim fixed (principalTupleIntegers v) (input k (some a)))
      (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (rows j) (layerSamplerBox B U basis S) (fun d => d.property)
      (fun k => hn k none) (fun a k => hn k (some a)) hH

theorem allocatedPartitionedJet_radius_bound (j : Fin m) (i : Fin (n j))
    {P : ℝ} (hP : 0 ≤ P) (hR0 : 0 ≤ R j) (hRP : R j ≤ Real.exp P) :
    ‖matrixSupCLM (normalizedIntegerColumns (allocatedPartitionedJetMatrix B U basis S x u v rows j)
      (allocatedIntegerProfileScales B U basis S j i) (fun _ => (basisAxisScale (basis j) i : ℝ)))‖ * R j ≤
        Real.exp (allocatedJetSupportLog (G := G) B α O P) := by
  have hm := matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos (Fintype.card α) (j.val+1)).le
    (allocatedPartitionedJet_normalized_bound B U basis S x u v rows j
      (Nat.cast_ne_zero.mpr (basisAxisScale_pos (basis j) i).ne'))
  exact (mul_le_mul_of_nonneg_right hm hR0).trans (allocatedJetSupport_budget (G := G) B α O hP hRP j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedIntegerKernelPMF_zero_off_box (j : Fin m) (i : Fin (n j))
    (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)
    {P : ℝ} (hP : 0 ≤ P) (hRP : R j ≤ Real.exp P) (z : O j → ℤ)
    (hz : z ∉ rectangularWeightIndices (fun _ => 0) (fun _ => (basisAxisScale (basis j) i : ℝ))
      (Real.exp (allocatedJetSupportLog (G := G) B α O P))) :
    allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous z = 0 := by
  exact coefficientImagePMF_zero_off_box (allocatedPartitionedJetMatrix B U basis S x u v rows j)
    (allocatedIntegerProfileScales B U basis S j i) (fun _ => (basisAxisScale (basis j) i : ℝ))
    (allocatedIntegerProfileScales_pos B U basis S j i)
    (fun _ => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    (affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i))
    (affineProductProfile_nonneg _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i))
    (allocatedIntegerProfile_support B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)
    (allocatedPartitionedJet_radius_bound B U basis S x u v rows j i hP (hR j).le hRP) z hz

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedAmbientLongBox
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α] [DecidableEq G]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "T" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "box" => allocatedLongJetBox B U basis S O T

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedLongJetFactor_zero_off_box
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (a : {a // ¬grid a}) (z : CoefficientJetAxisRow O a.val)
    (hz : z ∉ allocatedLongJetRowBox B U basis S O T a) :
    allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z = 0 := by
  have hv : ‖principalTupleNormalized lengths v‖ ≤ 1 :=
    principalTupleNormalized_norm_le (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) lengths
      (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩) v
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change O j → ℝ at z
    apply allocatedContinuousKernelDensity_zero_off_box_s2 B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 j i _ hv z
    change ¬dist z (0 : O j → ℝ) ≤ T at hz
    rw [dist_zero_right] at hz
    exact lt_of_not_ge hz
  | inr i =>
    change (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha) z).toReal = 0
    rw [allocatedIntegerKernelPMF_zero_off_box B U basis hR hσ S x u v rows j i (hσ1 j)
      (Nat.lt_of_not_ge ha) hP (hRP j) z hz, ENNReal.toReal_zero]

theorem allocatedLongJetDensity_zero_off_box_s2_oai
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (z : AllocatedLongJetRows B U basis S O) (hz : z ∉ box) :
    allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z = 0 := by
  have ha : ∃ a, z a ∉ allocatedLongJetRowBox B U basis S O T a := by
    simpa only [allocatedLongJetBox, Set.mem_univ_pi, not_forall] using hz
  obtain ⟨a, ha⟩ := ha
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (allocatedLongJetFactor_zero_off_box B U basis S hR hσ x rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1 v a (z a) ha)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
