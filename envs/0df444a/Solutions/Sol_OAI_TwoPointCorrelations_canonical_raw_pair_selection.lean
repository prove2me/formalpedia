-- Prove2me | solution 1 for OAI.TwoPointCorrelations.canonical_raw_pair_selection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:51:15.006932+00:00
-- url     : https://prove2.me/submissions/7ae332c0-ff7b-4291-90b1-957adb2d6cc7

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_canonical_retained_mass

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]






lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]









lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm




end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}











@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]






end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
namespace OAI

/-! Concrete continuous operators associated with finite matrices. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma matrixOperator_apply (A : ι → ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator A v i = ∑ j, A i j * v j := rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MultiplicativePrimeProducts
namespace OAI

/-! Finite squarefree products of an ordinary multiplicative function,
and the elementary defect inequality used in selecting raw divisors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma Multiplicative.prime_product {f : ℕ → ℂ} (hf : Multiplicative f)
    (hf1 : f 1 = 1) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    f (∏ p ∈ S, p) = ∏ p ∈ S, f p := by
  induction S using Finset.induction_on with
  | empty => simp [hf1]
  | @insert p S hp ih =>
    have hprime : p.Prime := hS p (mem_insert_self _ _)
    have hsub : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hprime (hsub q hq)).mpr (by
        intro he
        exact hp (he ▸ hq))
    rw [prod_insert hp, hf p _ hprime.pos (prod_pos (fun q hq => (hsub q hq).pos)) hcop,
      ih hsub, prod_insert hp]

lemma one_sub_prod_le_sum {ι : Type*} (S : Finset ι) (r : ι → ℝ)
    (h0 : ∀ i ∈ S, 0 ≤ r i) (h1 : ∀ i ∈ S, r i ≤ 1) :
    1 - ∏ i ∈ S, r i ≤ ∑ i ∈ S, (1 - r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hs0 : ∀ j ∈ S, 0 ≤ r j := fun j hj => h0 j (mem_insert_of_mem hj)
    have hs1 : ∀ j ∈ S, r j ≤ 1 := fun j hj => h1 j (mem_insert_of_mem hj)
    have hp := Finset.prod_le_one hs0 hs1
    have hr := h1 i (mem_insert_self _ _)
    have hm := mul_le_of_le_one_left (sub_nonneg.mpr hp) hr
    rw [prod_insert hi, sum_insert hi]
    have hh := ih hs0 hs1
    nlinarith

lemma multiplicative_prime_product_defect {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1)
    (hf : OneBounded f) (hg : OneBounded g)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    1 - ‖f (∏ p ∈ S, p) * g (∏ p ∈ S, p)‖ ≤
      ∑ p ∈ S, (1 - ‖f p * g p‖) := by
  rw [hfm.prime_product hf1 S hS, hgm.prime_product hg1 S hS,
    ← prod_mul_distrib, norm_prod]
  apply one_sub_prod_le_sum
  · intro p _
    positivity
  · intro p hp
    rw [norm_mul]
    exact (mul_le_mul (hf p (hS p hp).pos) (hg p (hS p hp).pos)
      (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma prime_product_pair_defect {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) (p : ℕ) (hp : 0 < p) :
    1 - ‖f p * g p‖ ≤ (1 - ‖f p‖) + (1 - ‖g p‖) := by
  rw [norm_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr (hf p hp)) (sub_nonneg.mpr (hg p hp))]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PhaseSelection
namespace OAI

/-! A numerical subfamily can retain complex mass without cancellation. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

private lemma coordinate_mass_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (φ : ℂ →+ ℝ) (hφ : ∀ x, |φ x| ≤ ‖x‖) :
    (∑ i ∈ s, |φ (z i)|) ≤
      ‖∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), z i‖ +
        ‖∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), z i‖ := by
  have he : (∑ i ∈ s, |φ (z i)|) =
      (∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), φ (z i)) -
        ∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), φ (z i) := by
    simp only [sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ φ (z i)
    · simp [hi, abs_of_nonneg hi]
    · simp [hi, abs_of_neg (lt_of_not_ge hi)]
  rw [he, ← map_sum, ← map_sum]
  have hp := hφ (∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), z i)
  have hn := hφ (∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), z i)
  linarith [le_abs_self (φ (∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), z i)),
    neg_le_abs (φ (∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), z i))]

/-- Four half-plane selections suffice. The selected family depends only
on the numerical coefficients, so it can be used as graph eligibility. -/
theorem exists_subfamily_complex_mass {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ∃ t ⊆ s, (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ t, z i‖ := by
  let rp := s.filter (fun i => 0 ≤ (z i).re)
  let rn := s.filter (fun i => ¬0 ≤ (z i).re)
  let ip := s.filter (fun i => 0 ≤ (z i).im)
  let inn := s.filter (fun i => ¬0 ≤ (z i).im)
  have hr := coordinate_mass_le s z Complex.reAddGroupHom Complex.abs_re_le_norm
  have hi := coordinate_mass_le s z Complex.imAddGroupHom Complex.abs_im_le_norm
  change (∑ i ∈ s, |(z i).re|) ≤ ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ at hr
  change (∑ i ∈ s, |(z i).im|) ≤ ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ at hi
  have ht : (∑ i ∈ s, ‖z i‖) ≤
      ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ + ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    have h := sum_le_sum (fun i (_ : i ∈ s) => Complex.norm_le_abs_re_add_abs_im (z i))
    rw [sum_add_distrib] at h
    dsimp only [rp, rn, ip, inn]
    linarith
  by_contra h
  push Not at h
  have h₁ := h rp (filter_subset _ _)
  have h₂ := h rn (filter_subset _ _)
  have h₃ := h ip (filter_subset _ _)
  have h₄ := h inn (filter_subset _ _)
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeCostTails
namespace OAI

/-! A fixed finite exclusion set makes all later finite prime costs small. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma summable_prime_cost_tail (r : ℕ → ℝ)
    (hr : ∀ p, p.Prime → 0 ≤ r p)
    (hs : Summable (fun p : ℕ => if p.Prime then r p else 0))
    (E₀ : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Finset ℕ, E₀ ⊆ E ∧ ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → Disjoint P E → (∑ p ∈ P, r p) < ε := by
  obtain ⟨S, hS⟩ := summable_iff_vanishing_norm.mp hs ε hε
  refine ⟨E₀ ∪ S, subset_union_left, ?_⟩
  intro P hP hdis
  have hd : Disjoint P S := hdis.mono_right subset_union_right
  have hh := hS P hd
  have he : (∑ p ∈ P, if p.Prime then r p else 0) = ∑ p ∈ P, r p := by
    apply sum_congr rfl
    intro p hp
    rw [if_pos (hP p hp)]
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun p hp => hr p (hP p hp)))] at hh
  exact hh

lemma pair_prime_defect_summable {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (hsf : Summable (fun p : ℕ => if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0))
    (hsg : Summable (fun p : ℕ => if p.Prime then (1 - ‖g p‖) / (p : ℝ) else 0)) :
    Summable (fun p : ℕ => if p.Prime then (1 - ‖f p * g p‖) / (p : ℝ) else 0) := by
  apply Summable.of_nonneg_of_le _ _ (hsf.add hsg)
  · intro p
    split_ifs with hp
    · apply div_nonneg _ (Nat.cast_nonneg p)
      rw [norm_mul]
      exact sub_nonneg.mpr ((mul_le_mul (hf p hp.pos) (hg p hp.pos)
        (norm_nonneg _) zero_le_one).trans (by norm_num))
    · exact le_rfl
  · intro p
    by_cases hp : p.Prime
    · simp only [hp, ite_true]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (prime_product_pair_defect hf hg p hp.pos)
        (Nat.cast_nonneg p)
    · simp only [hp, ite_false, add_zero, le_refl]

lemma exists_prime_defect_exclusion {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (hsf : Summable (fun p : ℕ => if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0))
    (hsg : Summable (fun p : ℕ => if p.Prime then (1 - ‖g p‖) / (p : ℝ) else 0))
    (E₀ : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Finset ℕ, E₀ ⊆ E ∧ ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → Disjoint P E →
      (∑ p ∈ P, (1 - ‖f p * g p‖) / (p : ℝ)) < ε ∧
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) < ε := by
  have hd := pair_prime_defect_summable hf hg hsf hsg
  have hsq : Summable (fun p : ℕ => if p.Prime then 1 / (p : ℝ) ^ 2 else 0) := by
    apply Summable.of_nonneg_of_le (fun p => by positivity) _
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    intro p
    split_ifs <;> first | exact le_rfl | positivity
  obtain ⟨E₁, hE₁, htail₁⟩ := summable_prime_cost_tail
    (fun p => (1 - ‖f p * g p‖) / (p : ℝ)) (fun p hp => by
      apply div_nonneg _ (Nat.cast_nonneg p)
      rw [norm_mul]
      exact sub_nonneg.mpr ((mul_le_mul (hf p hp.pos) (hg p hp.pos)
        (norm_nonneg _) zero_le_one).trans (by norm_num))) hd E₀ ε hε
  obtain ⟨E₂, hE₂, htail₂⟩ := summable_prime_cost_tail
    (fun p => 1 / (p : ℝ) ^ 2) (fun p _ => by positivity) hsq E₁ ε hε
  refine ⟨E₂, hE₁.trans hE₂, ?_⟩
  intro P hP hPE
  exact ⟨htail₁ P hP (hPE.mono_right hE₂), htail₂ P hP hPE⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SelfAdjointPath
namespace OAI

/-!
# Positivity along an invertible self-adjoint path

The resolvent path in manuscript Lemma `q:noncommuting` starts at the
identity and is self-adjoint and invertible throughout a real interval.
Its positivity follows from continuity of the least Rayleigh quotient.
The argument is carried out in finite dimension.
-/

open _root_.Filter

namespace TwoPointCorrelations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]






@[simp] lemma leastRayleigh_id : leastRayleigh (ContinuousLinearMap.id ℂ E) = 1 := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      (ContinuousLinearMap.id ℂ E).rayleighQuotient x = 1 := by
    have hn : ‖(x : E)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr x.property)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.id_apply,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    exact div_self hn
  simp [leastRayleigh, hpoint]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingTilt
namespace OAI

/-! The literal `5^omega` tilt of independent divisibility indicators gives
exactly the prime availability law used in the padding anti-concentration. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingTiltNormalizer_pos (Q : Finset ℕ) : 0 < paddingTiltNormalizer Q := by
  apply prod_pos
  intro p _
  positivity










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformResidueLaw_weight (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) (hx : x.val < p) :
    (uniformResidueLaw B p hp hpB).weight x = (p : ℝ)⁻¹ := by
  simp [uniformResidueLaw, hx]


@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open _root_.Finset










@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]



@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp
























end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open _root_.Finset

namespace TwoPointCorrelations












@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open _root_.Finset





@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimes
namespace OAI

/-! The fixed modulus-five prime-number input used by the manuscript.

Published source: D. Koukoulopoulos, *The Distribution of Prime Numbers*,
AMS, 2019, Theorem 12.1 (Siegel--Walfisz), with modulus 5 fixed. That theorem
is stated for the prime-counting function. `ModFiveThetaInput` is its standard
partial-summation consequence for the logarithmically weighted prime count,
specialized to the two selections needed here. The complementary selection
includes the single prime 5, which changes the error by a bounded amount.
Source: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf

The estimate includes every prime in the selected classes. Removing a finite
exceptional prime set contributes an explicit finite-deletion correction.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology









lemma modFiveTheta_eq_sum (one : Bool) (x : ℝ) :
    modFiveTheta one x = ∑ p ∈ modFivePrimesUpTo one x, Real.log p := by
  simp [modFiveTheta, modFivePrimesUpTo, modFiveLogWeight, sum_filter]





lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

/-- The entire cost of removing a finite exceptional prime set is explicit. -/
lemma deletedModFiveTheta_error (E : Finset ℕ) (one : Bool) (x : ℝ) :
    |deletedModFiveTheta E one x - modFiveTheta one x| ≤
      ∑ p ∈ E, Real.log p := by
  rw [modFiveTheta_eq_sum]
  have he : deletedModFiveTheta E one x -
      (∑ p ∈ modFivePrimesUpTo one x, Real.log p) =
      -(∑ p ∈ modFivePrimesUpTo one x ∩ E, Real.log p) := by
    unfold deletedModFiveTheta deletedModFivePrimes
    have hs := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ))
      (inter_subset_left : modFivePrimesUpTo one x ∩ E ⊆ modFivePrimesUpTo one x)
    rw [sdiff_inter_self_left] at hs
    linarith
  rw [he, abs_neg, abs_of_nonneg (sum_nonneg (fun p _ => log_nat_nonneg p))]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => log_nat_nonneg p)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePartialSummation
namespace OAI

/-! Exact partial summation, with the prime-count error retained inside the
integral. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem centered_partial_summation (c : ℕ → ℝ) (α a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ t in a..b, f t) =
      f b * (partialCoefficientSum c b - α * b) -
      f a * (partialCoefficientSum c a - α * a) -
      ∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t) := by
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hdfi : IntervalIntegrable (deriv f) volume a b :=
    hdf.intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun t => deriv f t * t) volume a b :=
    hdfi.mul_continuousOn continuous_id.continuousOn
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum c t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc c ha
      (hdf.integrableOn_Icc)
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
    f b * partialCoefficientSum c b - f a * partialCoefficientSum c a -
      ∫ t in a..b, deriv f t * partialCoefficientSum c t at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x (_ : x ∈ Set.uIcc a b) => hasDerivAt_id x) hdfi intervalIntegrable_const
  simp only [id_eq] at hparts
  have hsplit : (∫ t in a..b, deriv f t * t + f t * 1) =
      (∫ t in a..b, deriv f t * t) + ∫ t in a..b, f t := by
    simp only [mul_one]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum c t) -
        α * (∫ t in a..b, deriv f t * t) := by
    simp only [mul_sub, show ∀ t, deriv f t * (α * t) = α * (deriv f t * t) by
      intro t; ring]
    rw [intervalIntegral.integral_sub hsum (hdmain.const_mul α),
      intervalIntegral.integral_const_mul]
  rw [herr, hAbel]
  linear_combination -α * hparts


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ThetaLogError
namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exp_neg_sqrt_log_le (c x : ℝ) (hc : 0 < c) (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / (c ^ 4 * Real.log x ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hsq := Real.sq_sqrt hl.le
  have hpow : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    calc
      _ = c ^ 4 * ((Real.sqrt (Real.log x)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have he := Real.pow_div_factorial_le_exp (c * Real.sqrt (Real.log x))
    (mul_nonneg hc.le (Real.sqrt_nonneg (Real.log x))) 4
  norm_num at he
  rw [hpow] at he
  have hmul := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-c * Real.sqrt (Real.log x))).le
  have hexp : Real.exp (c * Real.sqrt (Real.log x)) *
      Real.exp (-c * Real.sqrt (Real.log x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hexp] at hmul
  apply (le_div_iff₀ (by positivity : 0 < c ^ 4 * Real.log x ^ 2)).mpr
  nlinarith [hmul]

lemma log_sq_le_two_mul (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 2 * x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x) (Real.log_nonneg hx) 2
  norm_num at hh
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at hh
  linarith

/-- A single constant controls the logarithmic PNT error for both residue
selections and every real endpoint at least two. -/
theorem ModFiveThetaInput.log_error (hP : ModFiveThetaInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |modFiveTheta one x - modFiveDensity one * x| ≤ K * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, h⟩ := hP
  refine ⟨24 * C / c ^ 4, by positivity, fun one x hx => ?_⟩
  apply (h one x hx).trans
  have hh := mul_le_mul_of_nonneg_left (exp_neg_sqrt_log_le c x hc (by linarith))
    (mul_nonneg hC (by linarith : 0 ≤ x))
  convert (preTransparency := .instances) hh using 1
  ring

theorem ModFiveThetaInput.deleted_log_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |deletedModFiveTheta E one x - modFiveDensity one * x| ≤
        K * x / Real.log x ^ 2 := by
  obtain ⟨K, hK, h⟩ := hP.log_error
  let D : ℝ := ∑ p ∈ E, Real.log p
  have hD : 0 ≤ D := sum_nonneg (fun p _ => log_nat_nonneg p)
  refine ⟨K + 2 * D, by positivity, fun one x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hd : D ≤ 2 * D * x / Real.log x ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hh := mul_le_mul_of_nonneg_left (log_sq_le_two_mul x (by linarith)) hD
    nlinarith [hh]
  calc
    _ ≤ |modFiveTheta one x - modFiveDensity one * x| + D := by
      calc
        _ = |(modFiveTheta one x - modFiveDensity one * x) +
            (deletedModFiveTheta E one x - modFiveTheta one x)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (le_refl _) (deletedModFiveTheta_error E one x)
    _ ≤ K * x / Real.log x ^ 2 + 2 * D * x / Real.log x ^ 2 :=
      add_le_add (h one x hx) hd
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPrimeBands
namespace OAI

/-! Quantitative reciprocal-prime bands from the actual theta error.
Partial summation gives the reciprocal-prime estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt reciprocalLog
      (-(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hh := (hasDerivAt_inv hx0).div (Real.hasDerivAt_log hx0) hl0
  convert (preTransparency := .instances) hh using 1
  · rfl
  · field_simp
    ring

lemma reciprocalLog_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |reciprocalLog x * E| ≤ K / Real.log x := by
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [abs_mul, abs_of_nonneg (by unfold reciprocalLog; positivity)]
  calc
    _ ≤ reciprocalLog x * (K * x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left hE (by unfold reciprocalLog; positivity)
    _ = K / Real.log x ^ 3 := by unfold reciprocalLog; field_simp
    _ ≤ K / Real.log x := by
      apply div_le_div_of_nonneg_left hK hlp
      nlinarith [sq_nonneg (Real.log x - 1)]

lemma reciprocalLog_deriv_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 1 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |deriv reciprocalLog x * E| ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [(reciprocalLog_hasDerivAt hx).deriv, abs_mul, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log x + 1),
    abs_of_pos (by positivity : 0 < x ^ 2 * Real.log x ^ 2)]
  calc
    _ ≤ ((Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) *
        (K * x / Real.log x ^ 2) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
      apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < x * Real.log x ^ 4)).mp
      field_simp
      nlinarith [sq_nonneg (Real.log x - 1), mul_nonneg hK (sq_nonneg (Real.log x - 1))]

/-- A uniform band error. The upper endpoint is arbitrary, so this applies
simultaneously to all the logarithmically spaced supplies in the manuscript. -/
theorem reciprocal_band_error (c : ℕ → ℝ) (α K a b : ℝ) (hK : 0 ≤ K)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog n * c n) -
      α * (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 4 * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hla : 1 ≤ Real.log a := by
    simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ reciprocalLog x :=
    fun x hx => (reciprocalLog_hasDerivAt (hx1 x hx)).differentiableAt
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 :=
    fun x hx => (zero_lt_one.trans (hx1 x hx)).ne'
  have hln : ∀ x ∈ Set.Icc a b, Real.log x ≠ 0 :=
    fun x hx => (Real.log_pos (hx1 x hx)).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hdf : ContinuousOn (deriv reciprocalLog) (Set.Icc a b) := by
    apply ContinuousOn.congr (f := fun x => -(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2))
    · exact (hclog.add continuousOn_const).neg.div
        ((continuousOn_id.pow 2).mul (hclog.pow 2))
        (fun x hx => mul_ne_zero (pow_ne_zero 2 (hxn x hx)) (pow_ne_zero 2 (hln x hx)))
    · intro x hx
      exact (reciprocalLog_hasDerivAt (hx1 x hx)).deriv
  have hAbel := centered_partial_summation c α a b ha0.le hab reciprocalLog hf hdf
  rw [show (∫ t in a..b, reciprocalLog t) =
      Real.log (Real.log b) - Real.log (Real.log a) from
    integral_inv_div_log ha1 hb1] at hAbel
  have hg : IntervalIntegrable (fun x : ℝ => 2 * K * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ hxn).div (hclog.pow 2)
      (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (2 * K)
  have hi : |∫ x in a..b, deriv reciprocalLog x * (partialCoefficientSum c x - α * x)| ≤
      2 * K / Real.log a := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact reciprocalLog_deriv_error_le K x _ hK (hx1 x ⟨hx.1.le, hx.2⟩)
          (hlx x ⟨hx.1.le, hx.2⟩) (hE x ⟨hx.1.le, hx.2⟩))) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hbound
    apply hbound.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * K) hbnonneg]
  have hA := reciprocalLog_error_le K a _ hK ha0 hla (hE a ⟨le_rfl, hab⟩)
  have hB := reciprocalLog_error_le K b _ hK (zero_lt_one.trans hb1)
    (hlx b ⟨hab, le_rfl⟩) (hE b ⟨hab, le_rfl⟩)
  have hBA : K / Real.log b ≤ K / Real.log a :=
    div_le_div_of_nonneg_left hK hlap (Real.log_le_log ha0 hab)
  rw [hAbel]
  calc
    _ ≤ |reciprocalLog b * (partialCoefficientSum c b - α * b)| +
        |reciprocalLog a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv reciprocalLog t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ K / Real.log a + K / Real.log a + 2 * K / Real.log a :=
      add_le_add (add_le_add (hB.trans hBA) hA) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeBands
namespace OAI

/-! Concrete modulus-five supplies and their reciprocal masses. We use
half-open bands `(exp A, exp B]`; this harmless endpoint convention makes
adjacent supplies exactly disjoint and matches finite Abel summation. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma partialSum_deletedModFive (E : Finset ℕ) (one : Bool) (x : ℝ) :
    partialCoefficientSum (deletedModFiveLogWeight E one) x =
      deletedModFiveTheta E one x := by
  unfold partialCoefficientSum deletedModFiveTheta deletedModFivePrimes
    modFivePrimesUpTo deletedModFiveLogWeight
  rw [sdiff_eq_filter, sum_filter, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : ModFivePrime one p <;> by_cases he : p ∈ E <;> simp [h, he]



lemma modFivePrimeBand_sum (E : Finset ℕ) (one : Bool) (a b : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, 1 / (p : ℝ)) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog p * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · have hl : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hs.1.1.one_lt)).ne'
    rw [if_pos hs]
    unfold deletedModFiveLogWeight
    rw [if_pos hs]
    unfold reciprocalLog
    field_simp
  · simp [deletedModFiveLogWeight, hs]

/-- Both selected prime classes have their correct logarithmic-band mass,
uniformly over the upper endpoint and with any fixed finite exclusions. -/
theorem ModFiveThetaInput.band_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (A B : ℝ), 1 ≤ A → A ≤ B →
      |(∑ p ∈ modFivePrimeBand E one (Real.exp A) (Real.exp B), 1 / (p : ℝ)) -
          modFiveDensity one * (Real.log B - Real.log A)| ≤ 4 * K / A := by
  obtain ⟨K, hK, h⟩ := hP.deleted_log_error E
  refine ⟨K, hK, fun one A B hA hAB => ?_⟩
  rw [modFivePrimeBand_sum]
  have hh := reciprocal_band_error (deletedModFiveLogWeight E one) (modFiveDensity one)
    K (Real.exp A) (Real.exp B) hK (Real.exp_le_exp.mpr hA)
      (Real.exp_le_exp.mpr hAB) (fun x hx => by
        rw [partialSum_deletedModFive]
        apply h one x
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        exact h2.trans ((Real.exp_le_exp.mpr hA).trans hx.1))
  simpa only [Real.log_exp] using hh

/-- The concrete centered-prime supplies have reciprocal mass in `[W,2W]`
once their lower logarithmic endpoint exceeds one fixed threshold. -/
theorem ModFiveThetaInput.centered_band_mass (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      W ≤ (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ∧
      (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨K, hK, h⟩ := hP.band_error E
  refine ⟨max 1 (8 * K / W), le_max_left _ _, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hB : A ≤ A * Real.exp (6 * W) := by
    have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity : 0 ≤ 6 * W)) hA0.le
    simpa only [mul_one] using hh
  have hmass := h true A (A * Real.exp (6 * W)) hA1 hB
  have he : Real.log (A * Real.exp (6 * W)) - Real.log A = 6 * W := by
    rw [Real.log_mul hA0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [he] at hmass
  have hsmall : 4 * K / A ≤ W / 2 := by
    have hh := (div_le_iff₀ hW).mp ((le_max_right 1 (8 * K / W)).trans hA)
    apply (div_le_iff₀ hA0).mpr
    nlinarith [hh]
  have hh := abs_le.mp hmass
  norm_num [modFiveDensity] at hh
  simp only [one_div]
  constructor <;> linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyGeometry
namespace OAI

/-! Actual disjoint prime supplies at geometric logarithmic scales. Their
mass follows from the published fixed-modulus input through the proved
partial-summation chain, and all support assertions are finite identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeSupplyEndpoint_zero (A W : ℝ) : primeSupplyEndpoint A W 0 = A := by
  simp [primeSupplyEndpoint]

lemma primeSupplyEndpoint_succ (A W : ℝ) (i : ℕ) :
    primeSupplyEndpoint A W (i + 1) = primeSupplyEndpoint A W i * Real.exp (6 * W) := by
  unfold primeSupplyEndpoint
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  ring








/-- Every centered supply is nonempty and has the required reciprocal mass.
The threshold is independent of the number of supplies and their indices. -/
theorem ModFiveThetaInput.centered_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ i : ℕ,
      (centeredPrimeSupply E A W i).Nonempty ∧
      W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨A₀, hA₀, hmass⟩ := hP.centered_band_mass E W hW
  refine ⟨A₀, hA₀, fun A hA i => ?_⟩
  have hA0 : 0 ≤ A := (zero_le_one.trans hA₀).trans hA
  have hlower : A₀ ≤ primeSupplyEndpoint A W i := by
    calc
      A₀ ≤ A := hA
      _ = primeSupplyEndpoint A W 0 := (primeSupplyEndpoint_zero A W).symm
      _ ≤ _ := primeSupplyEndpoint_mono A W hA0 hW.le (Nat.zero_le _)
  have hh := hmass (primeSupplyEndpoint A W i) hlower
  rw [← primeSupplyEndpoint_succ] at hh
  change W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W at hh
  refine ⟨?_, hh⟩
  by_contra he
  rw [not_nonempty_iff_eq_empty.mp he, sum_empty] at hh
  linarith [hh.1]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
namespace OAI

/-! The literal scale choice of the manuscript satisfies all prime-supply
mass and support hypotheses; no prime-family existence premise remains. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeSupplyScale_endpoint (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W) :=
    Nat.floor_le (by positivity)
  have hj' := (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj
  unfold primeSupplyEndpoint
  calc
    _ = Real.exp (Real.log L * (199 / 200 : ℝ) + 6 * W * primeSupplyCount W L) := by
      rw [Real.rpow_def_of_pos hLp, Real.exp_add]
    _ ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr (by nlinarith)
    _ = L := Real.exp_log hLp

lemma eventually_primeSupplyCount_pos (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ primeSupplyCount W L := by
  filter_upwards [eventually_ge_atTop (Real.exp (1200 * W))] with L hL
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hl : 1200 * W ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hl0 : 0 ≤ Real.log L := le_trans (by positivity : (0 : ℝ) ≤ 1200 * W) hl
  unfold primeSupplyCount
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W))).mpr
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 6 * W)).mpr
  linarith

theorem ModFiveThetaInput.eventually_actual_prime_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ primeSupplyCount W L ∧
      primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L ∧
      ∀ i : ℕ, (centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i).Nonempty ∧
        W ≤ (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ∧
        (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ≤ 2 * W := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  obtain ⟨A₀, _, hmass⟩ := hP.centered_supplies E W hWp
  have hlarge := (tendsto_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop A₀)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_primeSupplyCount_pos W hWp,
    hlarge] with L hL hJ hA
  exact ⟨hJ, primeSupplyScale_endpoint W L hWp hL,
    hmass (L ^ (199 / 200 : ℝ)) hA⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations











@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]




@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]


@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl



end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset








@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}





@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
namespace OAI

/-! The literal finite retained-divisor set and its Euler-product mass.
Distinct prime subsets produce distinct integers, so the divisor sum does
not contain hidden multiplicities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma primeSubset_product_injective (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p) S.powerset := by
  intro U hU V hV heq
  have hU' : U ⊆ S := mem_powerset.mp hU
  have hV' : V ⊆ S := mem_powerset.mp hV
  have hprimeU : ∀ p ∈ U, Nat.Prime p := fun p hp => hS p (hU' hp)
  have hprimeV : ∀ p ∈ V, Nat.Prime p := fun p hp => hS p (hV' hp)
  have hfactors := congrArg Nat.primeFactors heq
  simpa only [Nat.primeFactors_prod hprimeU, Nat.primeFactors_prod hprimeV] using hfactors

lemma retainedPrimeDivisor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : 0 < u := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  exact prod_pos (fun p hp => (hS p ((mem_powerset.mp hU) hp)).pos)



theorem retainedPrimeDivisors_weighted_mass (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (w : ℕ → ℝ) :
    (∑ u ∈ retainedPrimeDivisors S, (∏ p ∈ u.primeFactors, w p) / (u : ℝ)) =
      ∏ p ∈ S, (1 + w p / (p : ℝ)) := by
  unfold retainedPrimeDivisors
  rw [sum_image (primeSubset_product_injective S hS)]
  calc
    _ = ∑ U ∈ S.powerset, ∏ p ∈ U, (w p / (p : ℝ)) := by
      apply sum_congr rfl
      intro U hU
      have hUS : U ⊆ S := mem_powerset.mp hU
      rw [Nat.primeFactors_prod (fun p hp => hS p (hUS hp)), Nat.cast_prod,
        prod_div_distrib]
    _ = _ := (prod_one_add S).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingLiteralBins
namespace OAI

/-! The bin mass is the literal normalized sum of padding-divisor weights.
Boolean selections are finite subsets, so no extra multiplicity is present. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma paddingDivisorCoefficient_eq_four_pow (Q : Finset ℕ) (b : Q → Bool) :
    paddingDivisorCoefficient Q b = (4 : ℝ) ^ (selectedCoordinates Q b).card := by
  rw [← prod_const]
  simp only [selectedCoordinates, prod_filter, paddingDivisorCoefficient]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
namespace OAI

/-! Squarefree padding divisors encode prime selections without multiplicity.
This identifies the bin law with the paper's numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingAvailablePrimes_card (Q : Finset ℕ) (a : Q → Bool) :
    (paddingAvailablePrimes Q a).card = (selectedCoordinates Q a).card := by
  exact card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)








lemma paddingTiltNormalizer_eq_divisor_sum (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    paddingTiltNormalizer Q =
      ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) := by
  unfold paddingTiltNormalizer
  rw [prod_coe_sort Q (fun p : ℕ => 1 + 4 / (p : ℝ))]
  simpa only [prod_const] using
    (retainedPrimeDivisors_weighted_mass Q hQ (fun _ => (4 : ℝ))).symm


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingIntegerBins
namespace OAI

/-! The squarefree divisor formula uses literal divisibility by the site,
including the site zero. Bin membership is exactly the half-open interval
condition in the manuscript. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma paddingBin_eq_iff (η c x : ℝ) (j : ℤ) (hη : 0 < η) :
    paddingBin η c x = j ↔ (j : ℝ) * η ≤ x + c ∧ x + c < ((j : ℝ) + 1) * η := by
  rw [paddingBin, Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw
namespace OAI

/-! The harmonic divisor law `4^omega(q)/(q S)` is an actual finite
independent prime-selection law with inclusion probabilities `4/(p+4)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma reciprocal_padding_atom (p : ℕ) (hp : 0 < p) (b : Bool) :
    (reciprocalPaddingPrimeLaw p).weight b * (1 + 4 / (p : ℝ)) =
      if b then 4 / (p : ℝ) else 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hp4 : (p : ℝ) + 4 ≠ 0 := by positivity
  cases b <;> simp only [reciprocalPaddingPrimeLaw, booleanLaw, Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp <;> ring

lemma paddingSelectedDivisor_cast (Q : Finset ℕ) (b : Q → Bool) :
    (paddingSelectedDivisor Q b : ℝ) = ∏ p : Q, if b p then (p.val : ℝ) else 1 := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  simp only [selectedCoordinates, prod_filter]

lemma reciprocal_padding_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (b : Q → Bool) :
    (reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q =
      paddingDivisorCoefficient Q b / (paddingSelectedDivisor Q b : ℝ) := by
  simp only [reciprocalPaddingLaw, FiniteLaw.independent, paddingTiltNormalizer,
    ← prod_mul_distrib]
  rw [paddingDivisorCoefficient, paddingSelectedDivisor_cast, ← prod_div_distrib]
  apply prod_congr rfl
  intro p _
  rw [reciprocal_padding_atom p (hQ p p.property).pos]
  cases b p <;> simp

lemma reciprocal_padding_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (F : ℕ → ℝ) :
    (reciprocalPaddingLaw Q).average (fun b => F (paddingSelectedDivisor Q b)) =
      (paddingTiltNormalizer Q)⁻¹ *
        ∑ q ∈ retainedPrimeDivisors Q, ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q := by
  have hS := paddingTiltNormalizer_pos Q
  let G (q : retainedPrimeDivisors Q) : ℝ :=
    ((4 : ℝ) ^ q.val.primeFactors.card / (q.val : ℝ)) * F q.val
  have hatom (b : Q → Bool) :
      (reciprocalPaddingLaw Q).weight b * F (paddingSelectedDivisor Q b) =
        (paddingTiltNormalizer Q)⁻¹ * G (paddingDivisorEquiv Q hQ b) := by
    have hw := reciprocal_padding_weight Q hQ b
    change _ = (paddingTiltNormalizer Q)⁻¹ *
      ((4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card /
        (paddingSelectedDivisor Q b : ℝ) * F (paddingSelectedDivisor Q b))
    rw [paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
      ← paddingDivisorCoefficient_eq_four_pow]
    calc
      _ = (paddingTiltNormalizer Q)⁻¹ *
          (((reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q) *
            F (paddingSelectedDivisor Q b)) := by field_simp [hS.ne']
      _ = _ := by rw [hw]
  unfold FiniteLaw.average
  simp_rw [hatom]
  rw [← mul_sum, (paddingDivisorEquiv Q hQ).sum_comp G]
  congr 1
  exact sum_coe_sort (retainedPrimeDivisors Q)
    (fun q : ℕ => ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q)

lemma FiniteLaw.independent_average_coordinate {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] (μ : ι → FiniteLaw A) (i : ι) (f : A → ℝ) :
    (FiniteLaw.independent μ).average (fun x => f (x i)) = (μ i).average f := by
  have hh := FiniteLaw.independent_average_product μ (fun j x => if j = i then f x else 1)
  have he (j : ι) : (μ j).average (fun x => if j = i then f x else 1) =
      if j = i then (μ i).average f else 1 := by
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  simpa only [he, prod_ite_eq', mem_univ, ite_true] using hh



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDefectMass
namespace OAI

/-! Exact first moments of additive prime costs under the actual padding law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma padding_selected_prime_sum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) (c : ℕ → ℝ) :
    (∑ p ∈ (paddingSelectedDivisor Q b).primeFactors, c p) =
      ∑ p : Q, if b p then c p.val else 0 := by
  rw [paddingSelectedDivisor_primeFactors Q hQ, paddingAvailablePrimes, sum_image]
  · simp only [selectedCoordinates, sum_filter]
  · intro p _ r _ he
    exact Subtype.ext he

lemma padding_prime_cost_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (c : ℕ → ℝ) :
    (reciprocalPaddingLaw Q).average
      (fun b => ∑ p ∈ (paddingSelectedDivisor Q b).primeFactors, c p) =
        ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p := by
  simp only [padding_selected_prime_sum Q hQ]
  rw [FiniteLaw.average_sum, ← sum_coe_sort Q]
  apply sum_congr rfl
  intro p _
  rw [reciprocalPaddingLaw, FiniteLaw.independent_average_coordinate
    (fun p : Q => reciprocalPaddingPrimeLaw p.val) p
    (fun b : Bool => if b then c p.val else 0)]
  simp [reciprocalPaddingPrimeLaw, booleanLaw, FiniteLaw.average]

lemma padding_prime_cost_sum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (c : ℕ → ℝ) :
    (∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
      ∑ p ∈ q.primeFactors, c p) =
        paddingTiltNormalizer Q * ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p := by
  have he := reciprocal_padding_average Q hQ (fun q => ∑ p ∈ q.primeFactors, c p)
  rw [padding_prime_cost_average Q hQ] at he
  have hS := paddingTiltNormalizer_pos Q
  calc
    _ = paddingTiltNormalizer Q * ((paddingTiltNormalizer Q)⁻¹ *
        ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
          ∑ p ∈ q.primeFactors, c p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul]
    _ = _ := by rw [← he]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]





end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal
namespace OAI

/-! The actual finite harmonic mass in the manuscript's half-open bins.
Its lower bound follows from the proved reciprocal padding law and its
upper bound simply removes the two restrictions. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma padding_bin_weight_sum (L η : ℝ) (d q : ℕ) (hη : 0 < η) :
    (∑ j ∈ paddingBinIndices L η,
      if (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
          (j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
          Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η
      then (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0) =
      if PaddingPairEligible L η d q then
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0 := by
  have hi (j : ℤ) :
      ((j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
        Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η) ↔
        paddingBin η 0 (Real.log (d * q : ℕ)) = j := by
    simpa only [add_zero] using
      (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).symm
  simp only [hi, PaddingPairEligible]
  by_cases hc : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L
  · simp [hc]
  · simp [hc]

lemma totalPaddingBinMass_eq (D Q : Finset ℕ) (L η : ℝ) (hη : 0 < η) :
    totalPaddingBinMass D Q L η = ∑ d ∈ D, paddingPairHarmonicMass Q L η d := by
  unfold totalPaddingBinMass paddingPairHarmonicMass
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  exact padding_bin_weight_sum L η d q hη





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledWordSegments
namespace OAI

/-! Splitting a coded word into the main path and its attached witness paths. -/

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
@[simp] lemma segment_length (w : LabeledPrimeWord ι) (a n : ℕ) :
    (w.segment a n).word.length = min n (w.word.length - a) := by
  simp only [segment, List.length_take, List.length_drop]



end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform
namespace OAI

/-! The common padded carrier law pushes forward to the genuine uniform
product of prime residue fields. Padding points contribute zero mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





/-- The numerical whole tuple determines its column choices, as used by
the nonbacktracking matrix's actual copy labels. -/
theorem primeTuple_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun x : (j : Fin J) → P j => ∏ j, (x j).val) := by
  intro x y he
  change (∏ j, (x j).val) = (∏ j, (y j).val) at he
  funext j
  apply Subtype.ext
  have hp := hprime j _ (x j).property
  have hd : (x j).val ∣ ∏ l, (y l).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun l => (x l).val) (mem_univ j)
  obtain ⟨l, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun l => (y l).val)).mp hd
  have hv : (x j).val = (y l).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime l _ (y l).property)).mp hdiv
  have hjl : j = l := by
    by_contra hne
    exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne)))
      (x j).property (hv.symm ▸ (y l).property)
  subst l
  exact hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass
namespace OAI

/-! The centered divisor family is the actual image of one prime choice
from each disjoint band. Its harmonic mass has no representation
multiplicity and is exactly the product of the band masses. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeTupleDivisors_mass {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) =
      ∏ j, ∑ p ∈ P j, 1 / (p : ℝ) := by
  rw [primeTupleDivisors, sum_image]
  · calc
      _ = ∑ x : (j : Fin J) → P j, ∏ j, 1 / ((x j).val : ℝ) := by
        apply sum_congr rfl
        intro x _
        simp only [Nat.cast_prod, one_div, prod_inv_distrib]
      _ = ∏ j, ∑ p : P j, 1 / (p.val : ℝ) :=
        (Fintype.prod_sum (fun j (p : P j) => 1 / (p.val : ℝ))).symm
      _ = _ := by
        apply prod_congr rfl
        intro j _
        exact sum_coe_sort (P j) (fun p : ℕ => 1 / (p : ℝ))
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
namespace OAI

/-! Arithmetic support of the actual one-prime-per-band tuple family. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeHarmonicMass_eq_sum (S : Finset ℕ) :
    primeHarmonicMass S = ∑ p ∈ S, 1 / (p : ℝ) := by
  unfold primeHarmonicMass
  simpa only [one_div] using sum_coe_sort S (fun p : ℕ => 1 / (p : ℝ))








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeCosts
namespace OAI

/-! First moments of additive prime costs for the actual disjoint-band tuple
family. Large band masses dilute any fixed summable prime defect. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma tuple_coordinate_cost_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (c : ℕ → ℝ) (i : Fin J) :
    (∑ x : (j : Fin J) → P j,
      (∏ j, 1 / ((x j).val : ℝ)) * c (x i).val) =
      (∑ p ∈ P i, c p / (p : ℝ)) *
        ∏ j ∈ (univ : Finset (Fin J)).erase i, primeHarmonicMass (P j) := by
  have he (x : (j : Fin J) → P j) :
      (∏ j, 1 / ((x j).val : ℝ)) * c (x i).val =
        ∏ j, if j = i then (1 / ((x j).val : ℝ)) * c (x j).val
          else 1 / ((x j).val : ℝ) := by
    rw [← mul_prod_erase univ _ (mem_univ i),
      ← mul_prod_erase univ _ (mem_univ i)]
    simp only [ite_true]
    have ht : (∏ j ∈ (univ : Finset (Fin J)).erase i,
        if j = i then (1 / ((x j).val : ℝ)) * c (x j).val
          else 1 / ((x j).val : ℝ)) =
        ∏ j ∈ (univ : Finset (Fin J)).erase i, 1 / ((x j).val : ℝ) := by
      apply prod_congr rfl
      intro j hj
      rw [if_neg (mem_erase.mp hj).1]
    rw [ht]
    ring
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (j : Fin J) (p : P j) =>
    if j = i then (1 / (p.val : ℝ)) * c p.val else 1 / (p.val : ℝ)),
    ← mul_prod_erase univ _ (mem_univ i)]
  congr 1
  · simp only [ite_true]
    rw [← sum_coe_sort (P i)]
    apply sum_congr rfl
    intro p _
    ring
  · apply prod_congr rfl
    intro j hj
    simp only [if_neg (mem_erase.mp hj).1, primeHarmonicMass, one_div]

lemma primeTupleDivisors_cost_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k)) (c : ℕ → ℝ) :
    (∑ d ∈ primeTupleDivisors P, (1 / (d : ℝ)) * ∑ p ∈ d.primeFactors, c p) =
      ∑ i : Fin J, (∑ p ∈ P i, c p / (p : ℝ)) *
        ∏ j ∈ (univ : Finset (Fin J)).erase i, primeHarmonicMass (P j) := by
  rw [primeTupleDivisors, sum_image]
  · have he (x : (j : Fin J) → P j) :
        (1 / ((∏ j, (x j).val : ℕ) : ℝ)) *
            (∑ p ∈ (∏ j, (x j).val).primeFactors, c p) =
          ∑ i : Fin J, (∏ j, 1 / ((x j).val : ℝ)) * c (x i).val := by
      have hf : (∏ j, (x j).val).primeFactors = univ.image (fun j => (x j).val) :=
        familyTuple_primeFactors (fun j (p : P j) => p.val)
          (fun j p => hprime j _ p.property) x (selectedPrimeValues_injective x hdisjoint)
      rw [hf, sum_image]
      · simp only [Nat.cast_prod, one_div, prod_inv_distrib, mul_sum]
      · exact fun j _ k _ he => selectedPrimeValues_injective x hdisjoint he
    simp_rw [he]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    exact tuple_coordinate_cost_sum P c i
  · exact fun x _ y _ he => primeTuple_injective hprime hdisjoint he

lemma primeTupleDivisors_cost_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (c : ℕ → ℝ) (hc : ∀ p ∈ primeTuplePool P, 0 ≤ c p)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j)) :
    (∑ d ∈ primeTupleDivisors P, (1 / (d : ℝ)) * ∑ p ∈ d.primeFactors, c p) ≤
      ((∏ j, primeHarmonicMass (P j)) / W) *
        ∑ p ∈ primeTuplePool P, c p / (p : ℝ) := by
  rw [primeTupleDivisors_cost_sum P hprime hdisjoint]
  have hpool : (∑ p ∈ primeTuplePool P, c p / (p : ℝ)) =
      ∑ j : Fin J, ∑ p ∈ P j, c p / (p : ℝ) := by
    unfold primeTuplePool
    apply sum_biUnion
    intro i _ j _ hij
    exact hdisjoint i j hij.symm
  rw [hpool, mul_sum]
  apply sum_le_sum
  intro i _
  have hprod0 : 0 ≤ ∏ j ∈ (univ : Finset (Fin J)).erase i,
      primeHarmonicMass (P j) := prod_nonneg (fun j _ => (hW.trans_le (hmass j)).le)
  have hprod : (∏ j ∈ (univ : Finset (Fin J)).erase i, primeHarmonicMass (P j)) ≤
      (∏ j, primeHarmonicMass (P j)) / W := by
    apply (le_div_iff₀ hW).mpr
    rw [← mul_prod_erase univ _ (mem_univ i)]
    nlinarith [mul_le_mul_of_nonneg_right (hmass i) hprod0]
  have hcost : 0 ≤ ∑ p ∈ P i, c p / (p : ℝ) := by
    apply sum_nonneg
    intro p hp
    exact div_nonneg (hc p (mem_primeTuplePool.mpr ⟨i, hp⟩)) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left hprod hcost).trans_eq (mul_comm _ _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PairPrimeCosts
namespace OAI

/-! The tensor product of the tuple and padding laws retains separate first
moments, rather than the largest prime cost of an individual divisor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma pair_prime_cost_sum (D Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hcop : ∀ d ∈ D, ∀ q ∈ retainedPrimeDivisors Q, d.Coprime q)
    (c : ℕ → ℝ) :
    (∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q,
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) *
        ∑ p ∈ (d * q).primeFactors, c p) =
      paddingTiltNormalizer Q * (∑ d ∈ D, (1 / (d : ℝ)) * ∑ p ∈ d.primeFactors, c p) +
      (∑ d ∈ D, 1 / (d : ℝ)) * paddingTiltNormalizer Q *
        ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p := by
  have he (d : ℕ) (hd : d ∈ D) :
      (∑ q ∈ retainedPrimeDivisors Q,
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) *
          ∑ p ∈ (d * q).primeFactors, c p) =
        (1 / (d : ℝ)) * (∑ p ∈ d.primeFactors, c p) * paddingTiltNormalizer Q +
        (1 / (d : ℝ)) * (paddingTiltNormalizer Q *
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p) := by
    calc
      _ = ∑ q ∈ retainedPrimeDivisors Q,
          (((1 / (d : ℝ)) * (∑ p ∈ d.primeFactors, c p)) *
            ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) +
          (1 / (d : ℝ)) * (((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) *
            ∑ p ∈ q.primeFactors, c p)) := by
        apply sum_congr rfl
        intro q hq
        rw [(hcop d hd q hq).primeFactors_mul,
          sum_union (hcop d hd q hq).disjoint_primeFactors, Nat.cast_mul]
        ring
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum,
          ← paddingTiltNormalizer_eq_divisor_sum Q hQ, padding_prime_cost_sum Q hQ]
  calc
    _ = ∑ d ∈ D, ((1 / (d : ℝ)) * (∑ p ∈ d.primeFactors, c p) * paddingTiltNormalizer Q +
        (1 / (d : ℝ)) * (paddingTiltNormalizer Q *
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p)) := by
      apply sum_congr rfl
      intro d hd
      exact he d hd
    _ = _ := by
      rw [sum_add_distrib, ← sum_mul, ← sum_mul]
      ring

lemma tuple_padding_coprime {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    {d q : ℕ} (hd : d ∈ primeTupleDivisors P) (hq : q ∈ retainedPrimeDivisors Q) :
    d.Coprime q := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpq
  have hd0 : d ≠ 0 := (primeTupleDivisors_arithmetic P hprime hdisjoint hd).1.ne_zero
  have hq0 : q ≠ 0 := (retainedPrimeDivisor_pos Q hQ hq).ne'
  have hpD : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩
  have hpQ : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩
  exact disjoint_left.mp hPQ
    ((primeTupleDivisors_arithmetic P hprime hdisjoint hd).2.2 hpD)
    (retainedPrimeDivisor_factors Q hQ hq hpQ)

lemma tuple_padding_prime_cost_bound {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (c : ℕ → ℝ) (hc : ∀ p ∈ primeTuplePool P, 0 ≤ c p)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j)) :
    (∑ d ∈ primeTupleDivisors P, ∑ q ∈ retainedPrimeDivisors Q,
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) *
        ∑ p ∈ (d * q).primeFactors, c p) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, c p / (p : ℝ)) / W +
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p) := by
  rw [pair_prime_cost_sum _ Q hQ
    (fun _ hd _ hq => tuple_padding_coprime P Q hprime hdisjoint hQ hPQ hd hq) c]
  have hm : (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) =
      ∏ j, primeHarmonicMass (P j) := by
    rw [primeTupleDivisors_mass P hprime hdisjoint]
    simp only [primeHarmonicMass_eq_sum]
  rw [hm]
  have hb := mul_le_mul_of_nonneg_left
    (primeTupleDivisors_cost_bound P hprime hdisjoint c hc W hW hmass)
    (paddingTiltNormalizer_pos Q).le
  apply (add_le_add hb (le_refl _)).trans_eq
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PairModulusDefect
namespace OAI

/-! The mean modulus loss is controlled by the separate tuple and padding
prime-defect moments. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma squarefree_pair_defect {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    {n : ℕ} (hn : Squarefree n) :
    1 - ‖f n * g n‖ ≤ ∑ p ∈ n.primeFactors, (1 - ‖f p * g p‖) := by
  have he := multiplicative_prime_product_defect hfm hgm hf1 hg1 hf hg n.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  rwa [Nat.prod_primeFactors_of_squarefree hn] at he

lemma tuple_padding_modulus_defect {J : ℕ} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j)) :
    (∑ d ∈ primeTupleDivisors P, ∑ q ∈ retainedPrimeDivisors Q,
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) * (1 - ‖f (d * q) * g (d * q)‖)) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W +
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * (1 - ‖f p * g p‖)) := by
  apply le_trans _ (tuple_padding_prime_cost_bound P Q hprime hdisjoint hQ hPQ
    (fun p => 1 - ‖f p * g p‖) (fun p hp => by
      have hpp := primeTuplePool_prime hprime hp
      rw [norm_mul]
      exact sub_nonneg.mpr ((mul_le_mul (hf p hpp.pos) (hg p hpp.pos)
        (norm_nonneg _) zero_le_one).trans (by norm_num))) W hW hmass)
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro q hq
  have hsq : Squarefree (d * q) := (Nat.squarefree_mul
    (tuple_padding_coprime P Q hprime hdisjoint hQ hPQ hd hq)).mpr
      ⟨(primeTupleDivisors_arithmetic P hprime hdisjoint hd).1,
        retainedPrimeDivisor_squarefree Q hQ hq⟩
  exact mul_le_mul_of_nonneg_left (squarefree_pair_defect hfm hgm hf1 hg1 hf hg hsq)
    (by positivity)

lemma padding_modulus_defect_cost_le {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    (∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * (1 - ‖f p * g p‖)) ≤
      4 * ∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
  have hd : 0 ≤ 1 - ‖f p * g p‖ := by
    rw [norm_mul]
    exact sub_nonneg.mpr ((mul_le_mul (hf p (hQ p hp).pos) (hg p (hQ p hp).pos)
      (norm_nonneg _) zero_le_one).trans (by norm_num))
  calc
    _ ≤ (4 / (p : ℝ)) * (1 - ‖f p * g p‖) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hpR (by linarith)) hd
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexRawSelection
namespace OAI

/-! Numerical phase selection and the raw lower bound use the whole reciprocal
mass. No phase or nonvanishing condition is imposed on individual primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exists_weighted_phase_subset {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (z : ι → ℂ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hdefect : (∑ i ∈ S, w i * (1 - ‖z i‖)) ≤ (∑ i ∈ S, w i) / 2) :
    ∃ A ⊆ S, (∑ i ∈ S, w i) / 8 ≤ ‖∑ i ∈ A, (w i : ℂ) * z i‖ := by
  obtain ⟨A, hAS, hA⟩ := exists_subfamily_complex_mass S (fun i => (w i : ℂ) * z i)
  refine ⟨A, hAS, ?_⟩
  have he : (∑ i ∈ S, w i * (1 - ‖z i‖)) =
      (∑ i ∈ S, w i) - ∑ i ∈ S, w i * ‖z i‖ := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hn : (∑ i ∈ S, ‖(w i : ℂ) * z i‖) = ∑ i ∈ S, w i * ‖z i‖ := by
    apply sum_congr rfl
    intro i hi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  rw [hn] at hA
  rw [he] at hdefect
  linarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexPairSelection
namespace OAI

/-! Phase selection on the literal finite numerical pair family. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma complexPairWeight_nonneg (dq : ℕ × ℕ) : 0 ≤ complexPairWeight dq := by
  unfold complexPairWeight
  positivity

lemma eligibleComplexPairs_sum {M : Type*} [AddCommMonoid M]
    (D Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F : ℕ × ℕ → M) :
    (∑ dq ∈ eligibleComplexPairs D Q eligible, F dq) =
      ∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q, if eligible d q then F (d, q) else 0 := by
  rw [eligibleComplexPairs, sum_filter, sum_product]

lemma eligibleComplexPairs_mass (D Q : Finset ℕ) (L η : ℝ) (hη : 0 < η) :
    (∑ dq ∈ eligibleComplexPairs D Q (PaddingPairEligible L η), complexPairWeight dq) =
      totalPaddingBinMass D Q L η := by
  rw [eligibleComplexPairs_sum, totalPaddingBinMass_eq D Q L η hη]
  rfl

lemma eligibleComplexPairs_defect_le {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (eligible : ℕ → ℕ → Prop) :
    (∑ dq ∈ eligibleComplexPairs D Q eligible, complexPairWeight dq *
      (1 - ‖f (dq.1 * dq.2) * g (dq.1 * dq.2)‖)) ≤
      ∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q,
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) * (1 - ‖f (d * q) * g (d * q)‖) := by
  rw [eligibleComplexPairs_sum]
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro q hq
  by_cases he : eligible d q
  · simp only [he, ite_true, complexPairWeight, le_refl]
  · simp only [he, ite_false]
    apply mul_nonneg (by positivity)
    have hu := Nat.mul_pos (hD d hd) (retainedPrimeDivisor_pos Q hQ hq)
    rw [norm_mul]
    exact sub_nonneg.mpr ((mul_le_mul (hf _ hu) (hg _ hu)
      (norm_nonneg _) zero_le_one).trans (by norm_num))

lemma exists_eligible_pair_phase {f g : ℕ → ℂ} (D Q : Finset ℕ)
    (L η : ℝ) (hη : 0 < η)
    (hdefect : (∑ dq ∈ eligibleComplexPairs D Q (PaddingPairEligible L η),
      complexPairWeight dq * (1 - ‖f (dq.1 * dq.2) * g (dq.1 * dq.2)‖)) ≤
        totalPaddingBinMass D Q L η / 2) :
    ∃ A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η),
      totalPaddingBinMass D Q L η / 8 ≤
        ‖∑ dq ∈ A, (complexPairWeight dq : ℂ) *
          (f (dq.1 * dq.2) * g (dq.1 * dq.2))‖ := by
  have hm := eligibleComplexPairs_mass D Q L η hη
  obtain ⟨A, hA, hbound⟩ := exists_weighted_phase_subset
    (eligibleComplexPairs D Q (PaddingPairEligible L η)) complexPairWeight
    (fun dq => f (dq.1 * dq.2) * g (dq.1 * dq.2))
    (fun dq _ => complexPairWeight_nonneg dq) (by rwa [hm])
  exact ⟨A, hA, by rwa [hm] at hbound⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectPhase
namespace OAI

/-! Small prime-defect moments produce a numerical phase-selected family
whose coefficient is comparable to the full retained bin mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exists_pair_phase_of_prime_defect {J : ℕ} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W L η : ℝ) (hW : 0 < W) (hη : 0 < η)
    (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (htotal : paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) / 2 ≤
      totalPaddingBinMass (primeTupleDivisors P) Q L η)
    (hdefect : (∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W +
      4 * (∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 4) :
    ∃ A ⊆ eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η),
      totalPaddingBinMass (primeTupleDivisors P) Q L η / 8 ≤
        ‖∑ dq ∈ A, (complexPairWeight dq : ℂ) *
          (f (dq.1 * dq.2) * g (dq.1 * dq.2))‖ := by
  apply exists_eligible_pair_phase (primeTupleDivisors P) Q L η hη
  have hv : 0 ≤ paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j) :=
    mul_nonneg (paddingTiltNormalizer_pos Q).le
      (prod_nonneg (fun j _ => (hW.trans_le (hmass j)).le))
  have hD : ∀ d ∈ primeTupleDivisors P, 0 < d := by
    intro d hd
    exact Nat.pos_of_ne_zero (primeTupleDivisors_arithmetic P hprime hdisjoint hd).1.ne_zero
  apply (eligibleComplexPairs_defect_le hf hg (primeTupleDivisors P) Q hD hQ _).trans
  have hb := tuple_padding_modulus_defect hfm hgm hf1 hg1 hf hg P Q hprime hdisjoint
    hQ hPQ W hW hmass
  have hc := padding_modulus_defect_cost_le hf hg Q hQ
  have hs := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ((∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W)) hc) hv
  have ht := mul_le_mul_of_nonneg_left hdefect hv
  exact hb.trans (hs.trans (ht.trans (by linarith)))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedPairCosts
namespace OAI

/-! Passing the proved prime-cost moments to arbitrary selected pair subfamilies. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selected_pair_mass_le (D Q : Finset ℕ) (A : Finset (ℕ × ℕ))
    (L η : ℝ) (hη : 0 < η)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η)) :
    (∑ dq ∈ A, complexPairWeight dq) ≤ totalPaddingBinMass D Q L η := by
  rw [← eligibleComplexPairs_mass D Q L η hη]
  exact sum_le_sum_of_subset_of_nonneg hA (fun dq _ _ => complexPairWeight_nonneg dq)

lemma selected_pair_prime_cost_le {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (c : ℕ → ℝ) (hc : ∀ p, 0 ≤ c p)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ retainedPrimeDivisors Q) :
    (∑ dq ∈ A, complexPairWeight dq * ∑ p ∈ (dq.1 * dq.2).primeFactors, c p) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, c p / (p : ℝ)) / W +
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p) := by
  apply le_trans _ (tuple_padding_prime_cost_bound P Q hprime hdisjoint hQ hPQ c
    (fun p _ => hc p) W hW hmass)
  have hs := sum_le_sum_of_subset_of_nonneg
    (f := fun dq : ℕ × ℕ => complexPairWeight dq *
      ∑ p ∈ (dq.1 * dq.2).primeFactors, c p) hA
    (fun dq _ _ => mul_nonneg (complexPairWeight_nonneg dq)
      (sum_nonneg (fun p _ => hc p)))
  rw [sum_product] at hs
  exact hs

lemma selected_pair_reciprocal_cost_le {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ retainedPrimeDivisors Q) :
    (∑ dq ∈ A, complexPairWeight dq * ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W +
          4 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2) := by
  have hb := selected_pair_prime_cost_le P Q hprime hdisjoint hQ hPQ
    (fun p => 1 / (p : ℝ)) (fun p => by positivity) W hW hmass A hA
  have hp : (∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * (1 / (p : ℝ))) ≤
      4 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hmem
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hQ p hmem).pos
    calc
      _ ≤ (4 / (p : ℝ)) * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hpR (by linarith)) (by positivity)
      _ = _ := by ring
  have hv : 0 ≤ paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j) :=
    mul_nonneg (paddingTiltNormalizer_pos Q).le
      (prod_nonneg (fun j _ => (hW.trans_le (hmass j)).le))
  have he : (∑ p ∈ primeTuplePool P, (1 / (p : ℝ)) / (p : ℝ)) =
      ∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro p _
    ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add
    (le_refl ((∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W)) hp) hv)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RawPairSelection
namespace OAI

/-! One selection simultaneously retains raw complex mass and keeps the
coprimality error small. The hypotheses are the actual prime-tail moments. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem select_raw_pair_family {J : ℕ} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W L η γ : ℝ) (hW : 1 ≤ W) (hη : 0 < η) (hγ : 0 ≤ γ)
    (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (htotal : paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) / 2 ≤
      totalPaddingBinMass (primeTupleDivisors P) Q L η)
    (hdD : (∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 100)
    (hdQ : (∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 100)
    (hrD : (∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) ≤ γ / 1280)
    (hrQ : (∑ p ∈ Q, 1 / (p : ℝ) ^ 2) ≤ γ / 1280) :
    ∃ A ⊆ eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η),
      totalPaddingBinMass (primeTupleDivisors P) Q L η / 8 ≤ ‖selectedRawCoefficient A f g‖ ∧
      (∑ dq ∈ A, complexPairWeight dq) ≤ totalPaddingBinMass (primeTupleDivisors P) Q L η ∧
      (∑ dq ∈ A, complexPairWeight dq *
        ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤
          γ * totalPaddingBinMass (primeTupleDivisors P) Q L η / 128 := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hdD0 : 0 ≤ ∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ) := by
    apply sum_nonneg
    intro p hp
    have hpp := primeTuplePool_prime hprime hp
    apply div_nonneg _ (Nat.cast_nonneg p)
    rw [norm_mul]
    exact sub_nonneg.mpr ((mul_le_mul (hf p hpp.pos) (hg p hpp.pos)
      (norm_nonneg _) zero_le_one).trans (by norm_num))
  have hdsmall : (∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W +
      4 * (∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 4 := by
    have hdiv := div_le_self hdD0 hW
    linarith
  obtain ⟨A, hA, hphase⟩ := exists_pair_phase_of_prime_defect hfm hgm hf1 hg1 hf hg
    P Q hprime hdisjoint hQ hPQ W L η hWp hη hmass htotal hdsmall
  refine ⟨A, hA, hphase, selected_pair_mass_le _ _ A L η hη hA, ?_⟩
  have hA' : A ⊆ primeTupleDivisors P ×ˢ retainedPrimeDivisors Q :=
    hA.trans (filter_subset _ _)
  have hb := selected_pair_reciprocal_cost_le P Q hprime hdisjoint hQ hPQ W hWp hmass A hA'
  have hdiv : (∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W ≤ γ / 1280 :=
    (div_le_self (sum_nonneg (fun _ _ => by positivity)) hW).trans hrD
  have hsmall : (∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W +
      4 * (∑ p ∈ Q, 1 / (p : ℝ) ^ 2) ≤ γ / 256 := by linarith
  have hV : 0 ≤ paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j) :=
    mul_nonneg (paddingTiltNormalizer_pos Q).le
      (prod_nonneg (fun j _ => (hWp.trans_le (hmass j)).le))
  have hs := mul_le_mul_of_nonneg_left hsmall hV
  have ht := mul_le_mul_of_nonneg_left htotal hγ
  exact hb.trans (hs.trans (by nlinarith))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalRawSelection
namespace OAI

/-! Finite prime-defect tails supply the required numerical phase selection
for the canonical graph at every sufficiently large auxiliary scale. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem canonical_raw_pair_selection (hP : ModFiveThetaInput) {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (hsf : Summable (fun p : ℕ => if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0))
    (hsg : Summable (fun p : ℕ => if p.Prime then (1 - ‖g p‖) / (p : ℝ) else 0))
    (h : ℕ) (hh : 0 < h) (W γ : ℝ) (hW : 1 ≤ W) (hγ : 0 < γ) :
    ∃ E : Finset ℕ, (∀ p, p.Prime → p ∣ h → p ∈ E) ∧
      ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L, ∀ η : ℝ, 0 < η →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
      0 < S₀ ∧ ∃ A ⊆ eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η),
        S₀ / 8 ≤ ‖selectedRawCoefficient A f g‖ ∧
        (∑ dq ∈ A, complexPairWeight dq) ≤ S₀ ∧
        (∑ dq ∈ A, complexPairWeight dq *
          ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤ γ * S₀ / 128 := by
  let ε := min (1 / 100 : ℝ) (γ / 1280)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨E, hE, htail⟩ := exists_prime_defect_exclusion hf hg hsf hsg h.primeFactors ε hε
  refine ⟨E, fun p hp hph => hE (Nat.mem_primeFactors.mpr ⟨hp, hph, hh.ne'⟩), ?_⟩
  filter_upwards [hP.eventually_actual_prime_supplies E W hW,
    hP.eventually_canonical_retained_mass E W hW] with L hs hm
  intro hL η hη
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ j k, k ≠ j → Disjoint (P j) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
  have hq : ∀ p ∈ Q, p.Prime := fun _ hq => paddingPrimeSupply_prime hq
  have hPQ : Disjoint (primeTuplePool P) Q := centeredPrimePool_disjoint_padding _ _ _ _ _
  have hpE : Disjoint (primeTuplePool P) E := by
    apply disjoint_left.mpr
    intro p hp hpe
    obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
    exact (centeredPrimeSupply_mem hj).2.2.1 hpe
  have hqE : Disjoint Q E := by
    apply disjoint_left.mpr
    intro p hp hpe
    exact (mem_sdiff.mp hp).2 hpe
  have htp := htail (primeTuplePool P) (fun _ hp' => primeTuplePool_prime hp hp') hpE
  have htq := htail Q hq hqE
  have hmass : ∀ j, W ≤ primeHarmonicMass (P j) := by
    intro j
    simpa only [primeHarmonicMass_eq_sum, P, centeredPrimeBands] using (hs.2.2 j.val).2.1
  have htotal := (hm hL η hη).2
  have hV : 1 ≤ ∏ j, primeHarmonicMass (P j) :=
    Finset.one_le_prod (fun j _ => hW.trans (hmass j))
  have hS₀ : 0 < totalPaddingBinMass (primeTupleDivisors P) Q L η :=
    (half_pos (mul_pos (paddingTiltNormalizer_pos Q) (lt_of_lt_of_le zero_lt_one hV))).trans_le htotal
  refine ⟨hS₀, ?_⟩
  exact select_raw_pair_family hfm hgm hf1 hg1 hf hg P Q hp hd hq hPQ W L η γ
    hW hη hγ.le hmass htotal
    (htp.1.le.trans (min_le_left _ _)) (htq.1.le.trans (min_le_left _ _))
    (htp.2.le.trans (min_le_right _ _)) (htq.2.le.trans (min_le_right _ _))

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.canonical_raw_pair_selection := @OAI.TwoPointCorrelations.canonical_raw_pair_selection
