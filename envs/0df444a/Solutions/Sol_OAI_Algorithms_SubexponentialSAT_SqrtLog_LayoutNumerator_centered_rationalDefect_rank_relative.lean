-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:51:23.678468+00:00
-- url     : https://prove2.me/submissions/2cdc343b-18e6-4838-856d-d352835aa7e0

import Mathlib
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S081
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Spectral_centered_normalizedTail_le_of_sq

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BinomialInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Interpolation at consecutive integer weights

The coefficient construction uses the inverse of an actual finite matrix.
It applies over any commutative ring whose evaluation matrix has unit determinant.
The binomial evaluation matrix has determinant one, including in small characteristic.
-/

namespace SubexponentialSAT.BinomialInterpolation

open scoped BigOperators
open Matrix

noncomputable section

variable {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The zero extension connects finite-vector sums to the matrix construction's
natural-number-indexed sum over `range R`. -/
theorem sum_range_extendCoefficients {R : ℕ} (c : Fin R → K) (w : ℕ) :
    (∑ j ∈ Finset.range R, extendCoefficients c j * (w.choose j : K)) =
      ∑ j : Fin R, c j * (w.choose j.val : K) := by
  simpa only [extendCoefficients_fin] using
    (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => extendCoefficients c j * (w.choose j : K)) R).symm

theorem sum_range_extend_parity (A R : ℕ) (d : Fin R) :
    (∑ j ∈ Finset.range R, extendCoefficients (parityCoefficients (K := K) A R) j *
      ((A + d.val).choose j : K)) = (-1 : K) ^ (A + d.val) := by
  rw [sum_range_extendCoefficients, parityCoefficients_spec]

theorem sum_range_extend_parity_of_mem (A R w : ℕ) (hA : A ≤ w) (hR : w < A + R) :
    (∑ j ∈ Finset.range R, extendCoefficients (parityCoefficients (K := K) A R) j *
      (w.choose j : K)) = (-1 : K) ^ w := by
  let d : Fin R := ⟨w - A, Nat.sub_lt_right_of_lt_add hA (by simpa [Nat.add_comm] using hR)⟩
  have hd : A + d.val = w := Nat.add_sub_of_le hA
  simpa only [hd] using sum_range_extend_parity (K := K) A R d

section ElementarySymmetric

variable {S : Type*} [CommSemiring S]

omit [Fintype n] in
/-- The elementary symmetric sum of an indicator is the binomial coefficient
in the integer size of its support. The ambient set may be larger than the support. -/
theorem sum_powersetCard_prod_indicator (active ones : Finset n)
    (hsubset : ones ⊆ active) (j : ℕ) :
    (∑ t ∈ active.powersetCard j, ∏ i ∈ t, if i ∈ ones then (1 : S) else 0) =
      (ones.card.choose j : S) := by
  classical
  have hfilter :
      (active.powersetCard j).filter
          (fun t => t ⊆ ones) = ones.powersetCard j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hto⟩
      exact ⟨hto, hcard⟩
    · rintro ⟨hto, hcard⟩
      exact ⟨⟨Finset.Subset.trans hto hsubset, hcard⟩, hto⟩
  simp only [Finset.prod_boole]
  trans ∑ t ∈ active.powersetCard j,
    if t ⊆ ones then (1 : S) else 0
  · apply Finset.sum_congr rfl
    intro t _
    by_cases h : t ⊆ ones
    · have h' : ∀ i ∈ t, i ∈ ones := fun i hi => h hi
      rw [ite_eq_left h', ite_eq_left h]
    · have h' : ¬(∀ i ∈ t, i ∈ ones) := fun h' => h (fun i hi => h' i hi)
      rw [ite_eq_right h', ite_eq_right h]
  · rw [Finset.sum_boole, hfilter, Finset.card_powersetCard]

end ElementarySymmetric

end

end SubexponentialSAT.BinomialInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_MulticolorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multicolor universal types and consistent incidence slots

The number `r` of colors is an explicit natural parameter throughout. No
finiteness instance or cardinality identity treats it as a fixed constant.
The joint fiber uses a head color different from the selected slot color,
as required by Sections 3.1 and 3.4 of the subexponential construction.
-/

namespace SubexponentialSAT.MulticolorTypes

variable {r Q Δ : ℕ}

theorem card_joint_via_pairs (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (Joint t g i) =
      (r * r) ^ (Q - 1) * ((r - 1) * r ^ (Q * (Δ - 1))) := by
  rw [Fintype.card_congr (jointEquivPairs t g i)]
  simp [Spectator, Fintype.card_prod, ← pow_mul]

end SubexponentialSAT.MulticolorTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SpectralRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Rank defects of diagonal operators

The rank here is the dimension of the actual range of a linear map.  The main
bound is obtained by identifying that range with the span of precisely those
basis vectors on which the diagonal coefficient is nonzero.
-/

namespace SubexponentialSAT.SpectralRank

open Module Submodule
open scoped BigOperators

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A linear map's image is spanned by its values on any basis. -/
theorem range_eq_span_basis_images (b : Basis ι K V) (f : V →ₗ[K] V) :
    LinearMap.range f = Submodule.span K (Set.range fun i => f (b i)) := by
  calc
    LinearMap.range f = LinearMap.range (b.constr K (fun i => f (b i))) := by
      rw [b.constr_self]
    _ = _ := b.constr_range K

/-- For a diagonal operator, only the nonzero diagonal entries contribute to
the range; every corresponding basis vector does belong to that range. -/
theorem range_eq_span_nonzero (b : Basis ι K V) (f : V →ₗ[K] V) (μ : ι → K)
    (hdiag : ∀ i, f (b i) = μ i • b i) :
    LinearMap.range f =
      Submodule.span K (Set.range fun i : {i // μ i ≠ 0} => b i.1) := by
  rw [range_eq_span_basis_images b f]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    dsimp only
    by_cases hi : μ i = 0
    · rw [hdiag, hi, zero_smul]
      exact Submodule.zero_mem _
    · rw [hdiag]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : μ i.1 • b i.1 ∈
        Submodule.span K (Set.range fun j => f (b j)) := by
      rw [← hdiag]
      exact Submodule.subset_span ⟨i.1, rfl⟩
    have hi' := Submodule.smul_mem
      (Submodule.span K (Set.range fun j => f (b j))) (μ i.1)⁻¹ hi
    rw [smul_smul, inv_mul_cancel₀ i.2, one_smul] at hi'
    exact hi'

/-- Exact finite rank, counted by basis indices with nonzero eigenvalue. -/
theorem finrank_range_eq_card_nonzero [Fintype ι]
    (b : Basis ι K V) (f : V →ₗ[K] V) (μ : ι → K)
    (hdiag : ∀ i, f (b i) = μ i • b i) :
    finrank K (LinearMap.range f) = Nat.card {i // μ i ≠ 0} := by
  classical
  rw [range_eq_span_nonzero b f μ hdiag, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)

/-- Exact rank of `id - M`: each eigenvalue different from one contributes
one basis index, with its full multiplicity. -/
theorem finrank_defect_eq_card [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (μ : ι → K)
    (hdiag : ∀ i, M (b i) = μ i • b i) :
    finrank K (LinearMap.range (LinearMap.id - M)) = Nat.card {i // μ i ≠ 1} := by
  have hdiag' : ∀ i, (LinearMap.id - M : V →ₗ[K] V) (b i) = (1 - μ i) • b i := by
    intro i
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hdiag, sub_smul, one_smul]
  rw [finrank_range_eq_card_nonzero b (LinearMap.id - M) (fun i => 1 - μ i) hdiag']
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    not_congr (sub_eq_zero.trans eq_comm))

/-- A designated set of good indices need only have eigenvalue one. Extra
unit eigenvalues outside that set can reduce the rank further. -/
theorem finrank_defect_le_card_bad [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (μ : ι → K)
    (good : ι → Prop) [DecidablePred good]
    (hdiag : ∀ i, M (b i) = μ i • b i)
    (hgood : ∀ i, good i → μ i = 1) :
    finrank K (LinearMap.range (LinearMap.id - M)) ≤ Fintype.card {i // ¬ good i} := by
  classical
  rw [finrank_defect_eq_card b M μ hdiag, Nat.card_eq_fintype_card]
  apply Fintype.card_le_of_injective
    (fun i : {i // μ i ≠ 1} => (⟨i.1, fun hi => i.2 (hgood i.1 hi)⟩ : {i // ¬ good i}))
  intro i j hij
  apply Subtype.ext
  exact congrArg (fun x : {i // ¬ good i} => x.1) hij

/-- Exact cardinality decomposition, before assuming a binomial law. -/
theorem card_bad_eq_sum_fibers [Fintype ι]
    (weight : ι → ℕ) (n : ℕ) (hweight : ∀ i, weight i ≤ n) (good : Finset ℕ) :
    Fintype.card {i // weight i ∉ good} =
      ∑ w : {w : Fin (n + 1) // w.1 ∉ good}, Fintype.card {i // weight i = w.1.1} := by
  rw [Fintype.card_congr (badWeightEquiv weight n hweight good), Fintype.card_sigma]

/-- Rewrite a sum over bad finite weights in the ordinary range-sum form. -/
theorem sum_bad_fin_eq_range (n : ℕ) (good : Finset ℕ) (f : ℕ → ℕ) :
    (∑ w : {w : Fin (n + 1) // w.1 ∉ good}, f w.1.1) =
      ∑ w ∈ Finset.range (n + 1), if w ∈ good then 0 else f w := by
  calc
    _ = ∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) => w.1 ∉ good), f w.1 := by
      exact (Finset.sum_subtype
        (p := fun w : Fin (n + 1) => w.1 ∉ good)
        (Finset.univ.filter fun w : Fin (n + 1) => w.1 ∉ good)
        (by intro w; simp) (fun w : Fin (n + 1) => f w.1)).symm
    _ = ∑ w : Fin (n + 1), if w.1 ∈ good then 0 else f w.1 := by
      simp only [Finset.sum_filter, ite_not]
    _ = _ := Fin.sum_univ_eq_sum_range (fun w => if w ∈ good then 0 else f w) (n + 1)

end SubexponentialSAT.SpectralRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Restricted support of the multicolor interpolation matrices

The multicolor register permutations and the products of (1 - J_l) / 2 are constructed
explicitly.  The support conclusion is derived from their sublist expansion.
-/

namespace SubexponentialSAT.Subexp.MatrixSupport

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

theorem swapPositions_insert (i : Fin Δ) (s : Finset (Fin Q))
    (a : Fin Q) (ha : a ∉ s) (u : UniversalType r Q Δ) :
    swapPositions i (insert a s) u =
      swapPositions i s (swapPositions i {a} u) := by
  apply UniversalType.ext
  · funext l
    by_cases hla : l = a
    · subst l
      simp [ha]
    · by_cases hl : l ∈ s <;> simp [hl, hla]
  · funext j l
    by_cases hj : j = i
    · subst j
      by_cases hla : l = a
      · subst l
        simp [ha]
      · by_cases hl : l ∈ s <;> simp [hl, hla]
    · simp [swapPositions_slot_other, hj]

theorem applySwaps_eq_swapPositions (i : Fin Δ) (as : List (Fin Q))
    (ha : as.Nodup) (u : UniversalType r Q Δ) :
    applySwaps i as u = swapPositions i as.toFinset u := by
  induction as generalizing u with
  | nil => simp [applySwaps]
  | cons a as ih =>
    rw [List.nodup_cons] at ha
    simp only [applySwaps, List.toFinset_cons]
    rw [ih ha.2, swapPositions_insert]
    simpa using ha.1

section Operators

variable {K : Type*} [Field K]

theorem matrixEntry_eq_matrixLinear (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (u y : UniversalType r Q Δ) :
    matrixEntry i t R c u y = matrixLinear i t R c (delta y) u := by
  simp [matrixEntry]

theorem extendJoint_off_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) (u : UniversalType r Q Δ)
    (hu : u ∉ joint t g i) :
    extendJoint i t g f u = 0 := by
  classical
  simp only [extendJoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro y hy
  have hne : u ≠ y.val := by
    intro heq
    apply hu
    rw [heq]
    exact y.property
  simp [delta, hne]

/-- Matrix-vector multiplication is exactly the concrete projector action.
This supplies the bridge needed for a spectral proof of the rank bound.
-/
theorem jointMatrix_mulVec (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (f : Joint t g i → K) (u : Joint t g i) :
    (jointMatrix i t g R c).mulVec f u =
      matrixLinear i t R c (extendJoint i t g f) u.val := by
  classical
  simp only [Matrix.mulVec, dotProduct, jointMatrix, matrixEntry_eq_matrixLinear,
    extendJoint, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y hy
  exact mul_comm _ _

/-- A simultaneous eigenvector on the fiber extends to one on the full type space. -/
theorem extendJoint_swap_eigen (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) (sign : Fin Q → K)
    (heig : ∀ l : OtherPosition t, ∀ u : Joint t g i,
      f (jointSwap i t g l u) = sign l.val * f u)
    (l : OtherPosition t) (u : UniversalType r Q Δ) :
    extendJoint i t g f (swapPositions i {l.val} u) =
      sign l.val * extendJoint i t g f u := by
  classical
  by_cases hu : u ∈ joint t g i
  · let u' : Joint t g i := ⟨u, hu⟩
    change extendJoint i t g f (jointSwap i t g l u').val =
      sign l.val * extendJoint i t g f u'.val
    rw [extendJoint_on_joint i t g f (jointSwap i t g l u'),
      extendJoint_on_joint i t g f u']
    exact heig l u'
  · have hs : swapPositions i {l.val} u ∉ joint t g i :=
      fun h => hu ((swapPositions_mem_joint_iff i t g {l.val}
        (by simpa using Ne.symm l.property) u).mp h)
    rw [extendJoint_off_joint i t g f _ hs, extendJoint_off_joint i t g f _ hu]
    simp

theorem projectorProduct_cons (i : Fin Δ) (a : Fin Q) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    projectorProduct i (a :: as) f u =
      (projectorProduct i as f u -
        projectorProduct i as f (swapPositions i {a} u)) / 2 := by
  simp only [projectorProduct, List.length_cons, differenceProduct,
    pow_succ, div_eq_mul_inv]
  ring

/-- Eigenaction of an ordered product of the normalized projectors. -/
theorem projectorProduct_eigen (i : Fin Δ) (as : List (Fin Q))
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    projectorProduct i as f u =
      (as.map (fun l => (1 - sign l) / 2)).prod * f u := by
  induction as generalizing u with
  | nil => simp [projectorProduct, differenceProduct]
  | cons a as ih =>
    have htail : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
      fun l hl => heig l (List.mem_cons_of_mem a hl)
    rw [projectorProduct_cons, ih htail, ih htail, heig a (by simp)]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem applySwaps_eigen (i : Fin Δ) (as : List (Fin Q))
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    f (applySwaps i as u) = (as.map sign).prod * f u := by
  induction as generalizing u with
  | nil => simp [applySwaps]
  | cons a as ih =>
    have htail : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
      fun l hl => heig l (List.mem_cons_of_mem a hl)
    rw [applySwaps, ih htail, heig a (by simp)]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem swapPositions_eigen (i : Fin Δ) (s : Finset (Fin Q))
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ s, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    f (swapPositions i s u) = (∏ l ∈ s, sign l) * f u := by
  have hp := applySwaps_eq_swapPositions i s.toList s.nodup_toList u
  simp only [Finset.toList_toFinset] at hp
  rw [← hp]
  have heig' : ∀ l ∈ s.toList, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
    fun l hl => heig l (by simpa using hl)
  rw [applySwaps_eigen i s.toList sign f heig']
  rw [← List.prod_toFinset sign s.nodup_toList, Finset.toList_toFinset]

theorem elementaryProjector_eigen (i : Fin Δ) (t : Fin Q) (j : ℕ)
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ activePositions t, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    elementaryProjector i t j f u =
      (∑ A ∈ (activePositions t).powersetCard j,
        ∏ l ∈ A, (1 - sign l) / 2) * f u := by
  unfold elementaryProjector
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  have hsub := (Finset.mem_powersetCard.mp hA).1
  have heig' : ∀ l ∈ A.toList, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
    fun l hl => heig l (hsub (by simpa using hl))
  rw [projectorProduct_eigen i A.toList sign f heig']
  rw [← List.prod_toFinset (fun l => (1 - sign l) / 2) A.nodup_toList,
    Finset.toList_toFinset]

/-- Simultaneous position eigenvectors are eigenvectors of the constructed map. -/
theorem matrixLinear_eigen (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ activePositions t, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    matrixLinear i t R c f u =
      ((∏ l ∈ activePositions t, sign l) *
        ∑ j ∈ Finset.range R, c j *
          ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2) * f u := by
  rw [matrixLinear_apply]
  simp_rw [elementaryProjector_eigen i t _ sign f heig,
    swapPositions_eigen i (activePositions t) sign f heig]
  let P : K := ∏ l ∈ activePositions t, sign l
  let E : ℕ → K := fun j =>
    ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2
  change (∑ j ∈ Finset.range R, c j * (E j * (P * f u))) =
    (P * (∑ j ∈ Finset.range R, c j * E j)) * f u
  calc
    _ = (∑ j ∈ Finset.range R, c j * E j) * (P * f u) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by ring

/-- Concrete matrix eigenaction on the joint fiber.  No eigenvalue or
support conclusion is assumed; only the individual position actions are given. -/
theorem jointMatrix_eigen (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (sign : Fin Q → K) (f : Joint t g i → K)
    (heig : ∀ l : OtherPosition t, ∀ u : Joint t g i,
      f (jointSwap i t g l u) = sign l.val * f u)
    (u : Joint t g i) :
    (jointMatrix i t g R c).mulVec f u =
      ((∏ l ∈ activePositions t, sign l) *
        ∑ j ∈ Finset.range R, c j *
          ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2) * f u := by
  rw [jointMatrix_mulVec]
  have heig' : ∀ l ∈ activePositions t, ∀ v,
      extendJoint i t g f (swapPositions i {l} v) = sign l * extendJoint i t g f v := by
    intro l hl v
    have hlt : l ≠ t := (Finset.mem_erase.mp hl).1
    exact extendJoint_swap_eigen i t g f sign heig ⟨l, hlt⟩ v
  rw [matrixLinear_eigen i t R c sign (extendJoint i t g f) heig',
    extendJoint_on_joint]

theorem jointMatrix_eigenvector (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (sign : Fin Q → K) (f : Joint t g i → K)
    (heig : ∀ l : OtherPosition t, ∀ u : Joint t g i,
      f (jointSwap i t g l u) = sign l.val * f u) :
    (jointMatrix i t g R c).mulVec f = matrixEigenvalue t R c sign • f := by
  funext u
  exact jointMatrix_eigen i t g R c sign f heig u

end Operators

end SubexponentialSAT.Subexp.MatrixSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

section PredicateWords

variable {ι β υ : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
variable (Neg : β → Prop) [DecidablePred Neg]

omit [DecidableEq ι] [Fintype β] in
theorem weight_le (word : ι → β) : weight Neg word ≤ Fintype.card ι := by
  exact Finset.card_filter_le _ _

theorem card_support_fiber (s : Finset ι) :
    Fintype.card {word : ι → β // negativeSupport Neg word = s} =
      Fintype.card {b : β // Neg b} ^ s.card *
        Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - s.card) := by
  classical
  rw [Fintype.card_congr (supportFiberEquiv Neg s), Fintype.card_prod]
  simp []

/-- Exact tensor multiplicities for any finite positive/negative alphabet. -/
theorem card_weight (w : ℕ) :
    Fintype.card {word : ι → β // weight Neg word = w} =
      (Fintype.card ι).choose w *
        Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - w) *
        Fintype.card {b : β // Neg b} ^ w := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (negativeSupport (ι := ι) Neg)
    (p := fun word => weight Neg word = w)
    (q := fun s : Finset ι => s.card = w) (fun _ => Iff.rfl)
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  calc
    (∑ s : {s : Finset ι // s.card = w},
      Fintype.card {word : ι → β // negativeSupport Neg word = s.1}) =
        ∑ _s : {s : Finset ι // s.card = w},
          Fintype.card {b : β // Neg b} ^ w *
            Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - w) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [card_support_fiber, s.2]
    _ = _ := by simp [Nat.mul_comm, Nat.mul_assoc]

theorem card_weight_with_unused_left [Fintype υ] (w : ℕ) :
    Fintype.card {x : υ × (ι → β) // weight Neg x.2 = w} =
      Fintype.card υ * (Fintype.card ι).choose w *
        Fintype.card {b : β // ¬ Neg b} ^ (Fintype.card ι - w) *
        Fintype.card {b : β // Neg b} ^ w := by
  rw [Fintype.card_congr (weightedProductLeftEquiv (ι := ι) (υ := υ) Neg w),
    Fintype.card_prod, card_weight]
  simp only [Nat.mul_assoc]

end PredicateWords

theorem card_negative_eq_sum (r : ℕ) :
    Fintype.card (NegativeLabels r) = ∑ i ∈ Finset.range r, i := by
  rw [Fintype.card_congr
    (Equiv.subtypeProdEquivSigmaSubtype (fun a b : Fin r => b < a)), Fintype.card_sigma]
  have h (a : Fin r) : Fintype.card {b : Fin r // b < a} = a.1 := by
    rw [Fintype.card_of_subtype (Finset.Iio a) (by intro b; simp), Fin.card_Iio]
  simp_rw [h]
  simpa using Fin.sum_univ_eq_sum_range (fun i : ℕ => i) r

theorem card_positive_eq_sum (r : ℕ) :
    Fintype.card (PositiveLabels r) = ∑ i ∈ Finset.range (r + 1), i := by
  rw [Fintype.card_congr (positiveSigmaEquiv r), Fintype.card_sigma]
  have h (b : Fin r) : Fintype.card {a : Fin r // a ≤ b} = b.1 + 1 := by
    rw [Fintype.card_of_subtype (Finset.Iic b) (by intro a; simp), Fin.card_Iic]
  simp_rw [h]
  rw [show (∑ b : Fin r, (b.1 + 1)) = ∑ i ∈ Finset.range r, (i + 1) by
    simpa using Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1) r]
  simpa using (Finset.sum_range_succ' (fun i : ℕ => i) r).symm

theorem card_negative (r : ℕ) :
    Fintype.card (NegativeLabels r) = r * (r - 1) / 2 := by
  rw [card_negative_eq_sum, Finset.sum_range_id]

theorem card_positive (r : ℕ) :
    Fintype.card (PositiveLabels r) = r * (r + 1) / 2 := by
  rw [card_positive_eq_sum, Finset.sum_range_id]
  simp [Nat.mul_comm]

theorem card_not_negativePair (r : ℕ) :
    Fintype.card {x : Fin r × Fin r // ¬ negativePair x} = positiveMultiplicity r := by
  simpa [negativePair, not_lt, positiveMultiplicity] using card_positive r

theorem card_negativePair (r : ℕ) :
    Fintype.card {x : Fin r × Fin r // negativePair x} = negativeMultiplicity r := by
  change Fintype.card (NegativeLabels r) = negativeMultiplicity r
  exact card_negative r

/-- The positive and negative labels account for every ordered pair. -/
theorem multiplicities_add (r : ℕ) :
    positiveMultiplicity r + negativeMultiplicity r = r ^ 2 := by
  have h := Fintype.card_congr (Equiv.sumCompl (@negativePair r))
  rw [Fintype.card_sum, card_negativePair, card_not_negativePair,
    Fintype.card_prod, Fintype.card_fin] at h
  simpa [Nat.add_comm, pow_two] using h

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_LocalSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Spectrum of a swap of two finite ordered registers

The alphabet size is unrestricted relative to the characteristic.  The only
field assumption beyond `Field K` is `2 ≠ 0`.  Basis labels on or above the
diagonal are positive; labels strictly below the diagonal are negative.
-/

namespace SubexponentialSAT.Subexp.LocalSpectrum

open scoped BigOperators

variable (K : Type*) [Field K]
variable {α : Type*}

variable [LinearOrder α]

/-- Conjugating the actual swap gives a diagonal sign operator. -/
theorem eigenCoordinates_swap (f : Pair α → K) (i : Pair α) :
    eigenCoordinates K (swapMap K f) i = eigenvalue K i * eigenCoordinates K f i := by
  rcases i with ⟨a, b⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp [eigenCoordinates, eigenvalue, swapPair, ne_of_lt hab, hab, le_of_lt hab, swapMap]
    ring
  · simp [eigenCoordinates, eigenvalue, swapPair, swapMap]
  · simp [eigenCoordinates, eigenvalue, swapPair,
      Ne.symm (ne_of_lt hba), not_lt_of_ge (le_of_lt hba), not_le_of_gt hba,
      swapMap]
    ring

variable [Fintype α]

theorem swapEigenbasis_apply (h2 : (2 : K) ≠ 0) (i : Pair α) :
    swapEigenbasis K h2 i = fromEigenCoordinates K (Pi.single i 1) := by
  change Module.Basis.ofEquivFun (eigenCoordinateEquiv K h2) i = _
  rw [Module.Basis.coe_ofEquivFun]
  rfl

@[simp] theorem coordinates_basis (h2 : (2 : K) ≠ 0) (i : Pair α) :
    eigenCoordinateEquiv K h2 (swapEigenbasis K h2 i) = Pi.single i 1 := by
  rw [swapEigenbasis_apply]
  exact (eigenCoordinateEquiv K h2).apply_symm_apply (Pi.single i 1)

theorem swapEigenbasis_eigen (h2 : (2 : K) ≠ 0) (i : Pair α) :
    swapMap K (swapEigenbasis K h2 i) = eigenvalue K i • swapEigenbasis K h2 i := by
  apply (eigenCoordinateEquiv K h2).injective
  rw [map_smul]
  funext j
  change eigenCoordinates K (swapMap K (swapEigenbasis K h2 i)) j =
    eigenvalue K i * (eigenCoordinateEquiv K h2 (swapEigenbasis K h2 i)) j
  rw [eigenCoordinates_swap]
  change eigenvalue K j * (eigenCoordinateEquiv K h2 (swapEigenbasis K h2 i)) j = _
  rw [coordinates_basis]
  by_cases hij : i = j
  · subst j; rfl
  · simp [ hij]

theorem localKernel_eigen (h2 : (2 : K) ≠ 0) (i x : Pair α) :
    localKernel K (swapPair x) i = eigenvalue K i * localKernel K x i := by
  have h := congrFun (swapEigenbasis_eigen K h2 i) x
  simpa only [swapMap_apply, swapEigenbasis_apply, Pi.smul_apply, smul_eq_mul,
    localKernel] using h

end SubexponentialSAT.Subexp.LocalSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TensorSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section ProductKernel

variable (K : Type*) [Field K]
variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

theorem productBasis_apply (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (a x : ι → β) :
    productBasis K A B hAB hBA a x = ∏ l, A (x l) (a l) := by
  classical
  change Module.Basis.ofEquivFun (productCoordinateEquiv K A B hAB hBA) a x = _
  rw [Module.Basis.coe_ofEquivFun]
  simp [productCoordinateEquiv, SubexponentialSAT.LocalSpectrum.kernelMap,
    productKernel, Pi.single_apply]

/-- If the local kernel is an eigenkernel, the genuine product basis has the
same eigenvalue under a change at one position. -/
theorem productBasis_eigen (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (σ : β → β) (eigenvalue : β → K)
    (heigen : ∀ a x, A (σ x) a = eigenvalue a * A x a)
    (a x : ι → β) (l : ι) :
    productBasis K A B hAB hBA a (Function.update x l (σ (x l))) =
      eigenvalue (a l) * productBasis K A B hAB hBA a x := by
  classical
  simp only [productBasis_apply]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => A (Function.update x l (σ (x l)) j) (a j)) (Finset.mem_univ l)]
  rw [Function.update_self, heigen]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => A (x j) (a j)) (Finset.mem_univ l), mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

end ProductKernel

section Spectators

variable (K : Type*) [Field K]
variable {β ι U : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

variable [Fintype U] [DecidableEq U]

theorem spectatorBasis_apply (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (u : U) (a x : ι → β) (v : U) :
    spectatorBasis K A B hAB hBA (u, a) (x, v) =
      if v = u then productBasis K A B hAB hBA a x else 0 := by
  classical
  change Module.Basis.ofEquivFun (spectatorCoordinateEquiv K A B hAB hBA) (u, a) (x, v) = _
  rw [Module.Basis.coe_ofEquivFun]
  by_cases huv : v = u
  · subst v
    simp [spectatorCoordinateEquiv, productCoordinateEquiv, SubexponentialSAT.LocalSpectrum.kernelMap,
      productBasis_apply, productKernel, Pi.single_apply]
  · simp [spectatorCoordinateEquiv, productCoordinateEquiv, SubexponentialSAT.LocalSpectrum.kernelMap, productKernel, huv ]

theorem spectatorBasis_eigen (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (σ : β → β) (eigenvalue : β → K)
    (heigen : ∀ a x, A (σ x) a = eigenvalue a * A x a)
    (u : U) (a x : ι → β) (v : U) (l : ι) :
    spectatorBasis K A B hAB hBA (u, a) (Function.update x l (σ (x l)), v) =
      eigenvalue (a l) * spectatorBasis K A B hAB hBA (u, a) (x, v) := by
  rw [spectatorBasis_apply, spectatorBasis_apply]
  by_cases huv : v = u
  · simp only [huv, ite_true, if_true]
    exact productBasis_eigen K A B hAB hBA σ eigenvalue heigen a x l
  · simp [huv]

end Spectators

section JointBasis

open SubexponentialSAT.MulticolorTypes

variable {r Q Δ : ℕ}

/-- The actual register swap becomes a change of just one local pair under
the joint-fiber decomposition. -/
theorem jointEquivPairs_jointSwap (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEquivPairs t g i (MatrixSupport.jointSwap i t g l u) =
      (Function.update (jointEquivPairs t g i u).1 l
        (LocalSpectrum.swapPair ((jointEquivPairs t g i u).1 l)),
        (jointEquivPairs t g i u).2) := by
  apply Prod.ext
  · funext m
    by_cases h : m = l
    · subst m
      apply Prod.ext <;>
        simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions,
          LocalSpectrum.swapPair]
    · have hm : m.val ≠ l.val := fun hc => h (Subtype.ext hc)
      apply Prod.ext <;>
        simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions, h, hm]
  · apply Prod.ext
    · apply Subtype.ext
      simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions,
        Ne.symm l.property]
    · funext j m
      simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions, j.property]

theorem jointEigenbasis_swap_eigen (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (a : JointBasisIndex t g i)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a (MatrixSupport.jointSwap i t g l u) =
      LocalSpectrum.eigenvalue K (a.2 l) * jointEigenbasis K h2 t g i a u := by
  simp only [jointEigenbasis_apply, jointEquivPairs_jointSwap]
  exact @spectatorBasis_eigen K inferInstance (Fin r × Fin r) (OtherPosition t)
    (Spectator (Q := Q) g i) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance _ _
    (pairKernel_inverse K h2 inferInstance) (pairDualKernel_inverse K h2 inferInstance)
    LocalSpectrum.swapPair (LocalSpectrum.eigenvalue K) (LocalSpectrum.localKernel_eigen K h2)
    a.1 a.2 (jointEquivPairs t g i u).1 (jointEquivPairs t g i u).2 l

theorem negativePositions_subset {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) : negativePositions a ⊆ MatrixSupport.activePositions t := by
  intro l hl
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hl
  simp [MatrixSupport.activePositions, j.property]

theorem jointWeight_le {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) : jointWeight a ≤ Q - 1 := by
  simpa only [jointWeight, card_otherPosition] using
    SubexponentialSAT.SubexpSwapMultiplicity.weight_le SubexponentialSAT.SubexpSwapMultiplicity.negativePair a.2

theorem jointEigenbasis_sign_eigen (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (a : JointBasisIndex t g i)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a (MatrixSupport.jointSwap i t g l u) =
      jointSign K a l.val * jointEigenbasis K h2 t g i a u := by
  rw [jointSign_other]
  exact jointEigenbasis_swap_eigen K h2 t g i a l u

end JointBasis

section Multiplicities

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSwapMultiplicity

variable {r Q Δ : ℕ}

/-- Exact dimensions of the weight spaces of the actual tensor eigenbasis. -/
theorem card_jointWeight (t : Fin Q) (g : Fin r) (i : Fin Δ) (w : ℕ) :
    Fintype.card {a : JointBasisIndex t g i // jointWeight a = w} =
      spectatorCard r Q Δ * (Q - 1).choose w *
        positiveMultiplicity r ^ (Q - 1 - w) * negativeMultiplicity r ^ w := by
  change Fintype.card {x : Spectator (Q := Q) g i ×
      (OtherPosition t → Fin r × Fin r) // weight negativePair x.2 = w} = _
  simpa only [JointBasisIndex, jointWeight, swapWeight, card_otherPosition,
    card_spectator, card_not_negativePair, card_negativePair] using
    card_weight_with_unused_left (ι := OtherPosition t)
      (υ := Spectator (Q := Q) g i) negativePair w

theorem card_bad_jointWeight (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) :
    Fintype.card {a : JointBasisIndex t g i // jointWeight a ∉ Finset.Ico A (A + R)} =
      spectatorCard r Q Δ *
        weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R := by
  rw [SubexponentialSAT.SpectralRank.card_bad_eq_sum_fibers jointWeight (Q - 1) jointWeight_le]
  simp_rw [card_jointWeight]
  rw [SubexponentialSAT.SpectralRank.sum_bad_fin_eq_range (Q - 1) (Finset.Ico A (A + R))
    (fun w => spectatorCard r Q Δ * (Q - 1).choose w *
      positiveMultiplicity r ^ (Q - 1 - w) * negativeMultiplicity r ^ w)]
  simp only [weightedTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp [Nat.mul_assoc]

theorem localMultiplicity_sum (r : ℕ) :
    positiveMultiplicity r + negativeMultiplicity r = r * r := by
  have h : Fintype.card {x : Fin r × Fin r // ¬ negativePair x} +
      Fintype.card {x : Fin r × Fin r // negativePair x} = Fintype.card (Fin r × Fin r) := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  simpa only [card_not_negativePair, card_negativePair, Fintype.card_prod,
    Fintype.card_fin] using h

/-- The total number of actual coordinates has the same spectator factor as
the weight-space count; hence the normalized weight distribution is binomial. -/
theorem card_joint_via_multiplicities (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (Joint t g i) = spectatorCard r Q Δ *
      (positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) := by
  rw [SubexponentialSAT.MulticolorTypes.card_joint_via_pairs, localMultiplicity_sum]
  simp only [spectatorCard]
  ac_rfl

end Multiplicities

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SpectralRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual rank bounds for the multi-color swap construction

The linear-algebra input is the dimension of the actual range of `id - M`.
The local swap multiplicities and the finite tail are kept as ordinary natural
counts, and converted to real inequalities only at the final scaling step.
-/

namespace SubexponentialSAT.Subexp.SpectralRank

open Module
open scoped BigOperators

section Rank

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- The previously proved exact range computation gives a real rank bound
by the number of bad basis indices. -/
theorem real_rank_defect_le_bad
    (b : Basis ι K V) (M : V →ₗ[K] V) (eigenvalue : ι → K)
    (good : ι → Prop) [DecidablePred good]
    (hdiag : ∀ i, M (b i) = eigenvalue i • b i)
    (hgood : ∀ i, good i → eigenvalue i = 1) :
    (finrank K (LinearMap.range (LinearMap.id - M)) : ℝ) ≤
      (Fintype.card {i // ¬ good i} : ℝ) := by
  exact_mod_cast _root_.OAI.Algorithms.SubexponentialSAT.SpectralRank.finrank_defect_le_card_bad
    b M eigenvalue good hdiag hgood

/-- Scale an actual rank bound by the number of slot constraints. -/
theorem scaled_rank_defect_le
    (b : Basis ι K V) (M : V →ₗ[K] V) (eigenvalue : ι → K)
    (good : ι → Prop) [DecidablePred good] (d N : ℕ) (τ : ℝ)
    (hdiag : ∀ i, M (b i) = eigenvalue i • b i)
    (hgood : ∀ i, good i → eigenvalue i = 1)
    (hbad : (d : ℝ) * (Fintype.card {i // ¬ good i} : ℝ) ≤ τ * (N : ℝ)) :
    (d : ℝ) * (finrank K (LinearMap.range (LinearMap.id - M)) : ℝ) ≤
      τ * (N : ℝ) :=
  (mul_le_mul_of_nonneg_left (real_rank_defect_le_bad b M eigenvalue good hdiag hgood)
    (Nat.cast_nonneg d)).trans hbad

end Rank

/-- Spectator registers multiply the tail and the total mass by the same
ordinary integer. No field-characteristic condition enters this count. -/
theorem scale_tail_bound (d copies bad total : ℕ) (τ : ℝ)
    (htail : (d : ℝ) * (bad : ℝ) ≤ τ * (total : ℝ)) :
    (d : ℝ) * ((copies * bad : ℕ) : ℝ) ≤ τ * ((copies * total : ℕ) : ℝ) := by
  calc
    _ = (copies : ℝ) * ((d : ℝ) * (bad : ℝ)) := by push_cast; ring
    _ ≤ (copies : ℝ) * (τ * (total : ℝ)) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg copies)
    _ = _ := by push_cast; ring

section Scalar

variable {K α : Type*} [Field K] [DecidableEq α]

/-- Evaluate the actual elementary-symmetric expression at a sign profile.
The integer number of negative signs is retained before coefficients are
cast to the field, so this is valid when the truncation length exceeds the
characteristic. -/
theorem scalar_signIndicator (h2 : (2 : K) ≠ 0)
    (active ones : Finset α) (hsub : ones ⊆ active) (R : ℕ) (c : ℕ → K) :
    ((∏ l ∈ active, if l ∈ ones then (-1 : K) else 1) *
      ∑ j ∈ Finset.range R, c j *
        ∑ A ∈ active.powersetCard j,
          ∏ l ∈ A, (1 - (if l ∈ ones then (-1 : K) else 1)) / 2) =
      coefficientEigenvalue R c ones.card := by
  classical
  have hfilter : active.filter (fun l => l ∈ ones) = ones := by
    ext l
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hprod : (∏ l ∈ active, if l ∈ ones then (-1 : K) else 1) =
      (-1 : K) ^ ones.card := by
    simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one, hfilter]
  have hprojector (l : α) :
      (1 - (if l ∈ ones then (-1 : K) else 1)) / 2 =
        if l ∈ ones then (1 : K) else 0 := by
    by_cases hl : l ∈ ones
    · simp only [ite_eq_left hl, sub_neg_eq_add, one_add_one_eq_two]
      exact div_self h2
    · simp [hl]
  rw [hprod, coefficientEigenvalue]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp_rw [hprojector]
  exact _root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.sum_powersetCard_prod_indicator active ones hsub j

end Scalar

section ProbabilityTail

open SubexponentialSAT.Subexp.TensorSpectrum SubexponentialSAT.SubexpSwapMultiplicity

/-- A common denominator converts the exact probability tail to the finite
integer multiplicity tail. -/
theorem normalizedTail_eq_weightedTail (r q A R : ℕ) :
    normalizedTail r q A R =
      (weightedTail q (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) /
        (((positiveMultiplicity r + negativeMultiplicity r) ^ q : ℕ) : ℚ) := by
  rw [multiplicities_add]
  simp only [weightedTail, Nat.cast_sum, Nat.cast_pow, Finset.sum_div]
  unfold normalizedTail
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ Finset.Ico A (A + R)
  · simp [hw]
  · simp [hw, swapProbability, swapMultiplicity]

/-- The source probability bound and the denominator-cleared rank input are
equivalent when there is at least one color and one slot. -/
theorem normalizedTail_le_iff (r q A R d : ℕ) (τ : ℚ)
    (hr : 0 < r) (hd : 0 < d) :
    normalizedTail r q A R ≤ τ / (d : ℚ) ↔
      (d : ℚ) * (weightedTail q (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ q : ℕ) : ℚ) := by
  have htotal : (0 : ℚ) <
      (((positiveMultiplicity r + negativeMultiplicity r) ^ q : ℕ) : ℚ) := by
    rw [multiplicities_add]
    exact_mod_cast (pow_pos (pow_pos hr 2) q)
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [normalizedTail_eq_weightedTail, div_le_div_iff₀ htotal hd']
  rw [mul_comm (_ : ℚ) (d : ℚ)]

end ProbabilityTail

section ConcreteMatrix

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport SubexponentialSAT.Subexp.TensorSpectrum SubexponentialSAT.SubexpSwapMultiplicity

variable {K : Type*} [Field K] {r Q Δ : ℕ}

/-- Evaluate the scalar belonging to the same concrete matrix used by the
support theorem, rather than introducing a second matrix construction. -/
theorem matrixEigenvalue_signIndicator (h2 : (2 : K) ≠ 0) (t : Fin Q)
    (R : ℕ) (c : ℕ → K) (ones : Finset (Fin Q))
    (hsub : ones ⊆ activePositions t) :
    matrixEigenvalue t R c (fun l => if l ∈ ones then (-1 : K) else 1) =
      coefficientEigenvalue R c ones.card := by
  exact scalar_signIndicator h2 (activePositions t) ones hsub R c

/-- The actual matrix acts diagonally on the explicitly constructed tensor
basis, with the integer number of negative local labels as its weight. -/
theorem jointMatrix_eigenbasis (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (R : ℕ) (c : ℕ → K)
    (a : JointBasisIndex t g i) :
    (jointMatrix i t g R c).mulVecLin (jointEigenbasis K h2 t g i a) =
      coefficientEigenvalue R c (jointWeight a) • jointEigenbasis K h2 t g i a := by
  rw [Matrix.mulVecLin_apply]
  have heig := jointMatrix_eigenvector i t g R c (jointSign K a)
    (jointEigenbasis K h2 t g i a) (jointEigenbasis_sign_eigen K h2 t g i a)
  have hvalue : matrixEigenvalue t R c (jointSign K a) =
      coefficientEigenvalue R c (jointWeight a) := by
    change matrixEigenvalue t R c (fun l => if l ∈ negativePositions a then -1 else 1) = _
    simpa only [card_negativePositions] using
      matrixEigenvalue_signIndicator h2 t R c (negativePositions a)
        (negativePositions_subset a)
  rw [hvalue] at heig
  exact heig

/-- Multi-color matrix rank bound in a form with no division. The tail uses
the actual positive and negative local multiplicities and is an ordinary
finite integer sum. -/
theorem jointMatrix_rank_bound_real (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (c : ℕ → K) (τ : ℝ)
    (hcoeff : ∀ w ∈ Finset.Ico A (A + R),
      (∑ j ∈ Finset.range R, c j * (w.choose j : K)) = (-1 : K) ^ w)
    (htail : (Δ : ℝ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℝ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℝ)) :
    (Δ : ℝ) *
      (finrank K (LinearMap.range (LinearMap.id - (jointMatrix i t g R c).mulVecLin)) : ℝ) ≤
        τ * (Fintype.card (Joint t g i) : ℝ) := by
  apply scaled_rank_defect_le (jointEigenbasis K h2 t g i)
    (jointMatrix i t g R c).mulVecLin
    (fun a => coefficientEigenvalue R c (jointWeight a))
    (fun a => jointWeight a ∈ Finset.Ico A (A + R)) Δ (Fintype.card (Joint t g i)) τ
  · exact jointMatrix_eigenbasis h2 t g i R c
  · intro a ha
    rw [coefficientEigenvalue, hcoeff (jointWeight a) ha, ← mul_pow]
    simp
  · rw [card_bad_jointWeight, card_joint_via_multiplicities]
    exact scale_tail_bound Δ (spectatorCard r Q Δ)
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R)
      ((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1)) τ htail

/-- Rational form used by the authoritative multi-color layout interface. -/
theorem jointMatrix_rank_bound (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (c : ℕ → K) (τ : ℚ)
    (hcoeff : ∀ w ∈ Finset.Ico A (A + R),
      (∑ j ∈ Finset.range R, c j * (w.choose j : K)) = (-1 : K) ^ w)
    (htail : (Δ : ℚ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    (Δ : ℚ) *
      (finrank K (LinearMap.range (LinearMap.id - (jointMatrix i t g R c).mulVecLin)) : ℚ) ≤
        τ * (Fintype.card (Joint t g i) : ℚ) := by
  have ht : (Δ : ℝ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℝ) ≤
        (τ : ℝ) * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℝ) := by
    exact_mod_cast htail
  have hrank := jointMatrix_rank_bound_real h2 t g i A R c (τ : ℝ) hcoeff ht
  exact_mod_cast hrank

/-- Constructed binomial interpolation coefficients discharge the coefficient
hypothesis without any restriction relating the color count to the field. -/
theorem jointMatrix_parity_rank_bound (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (τ : ℚ)
    (htail : (Δ : ℚ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    (Δ : ℚ) *
      (finrank K (LinearMap.range (LinearMap.id -
        (jointMatrix i t g R (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
          (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
        τ * (Fintype.card (Joint t g i) : ℚ) := by
  apply jointMatrix_rank_bound h2 t g i A R
    (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
      (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R)) τ
  · intro w hw
    exact _root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.sum_range_extend_parity_of_mem A R w
      (Finset.mem_Ico.mp hw).1 (Finset.mem_Ico.mp hw).2
  · exact htail

/-- The literal relative-rank conclusion of Lemma 3.1. -/
theorem jointMatrix_parity_rank_relative (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (τ : ℚ)
    (htail : (Δ : ℚ) *
      (weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R : ℚ) ≤
        τ * (((positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) : ℕ) : ℚ)) :
    (finrank K (LinearMap.range (LinearMap.id -
      (jointMatrix i t g R (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
        (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
      (τ / (Δ : ℚ)) * (Fintype.card (Joint t g i) : ℚ) := by
  have hd : (0 : ℚ) < Δ := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hrank := jointMatrix_parity_rank_bound h2 t g i A R τ htail
  calc
    _ ≤ (τ * (Fintype.card (Joint t g i) : ℚ)) / (Δ : ℚ) := by
      apply (le_div_iff₀ hd).2
      simpa only [mul_comm] using hrank
    _ = _ := by ring

/-- The literal rank fraction, now with only the source probability-tail input. -/
theorem jointMatrix_parity_rank_relative_of_probability (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) (τ : ℚ)
    (htail : normalizedTail r (Q - 1) A R ≤ τ / (Δ : ℚ)) :
    (finrank K (LinearMap.range (LinearMap.id -
      (jointMatrix i t g R (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients
        (_root_.OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K) A R))).mulVecLin)) : ℚ) ≤
      (τ / (Δ : ℚ)) * (Fintype.card (Joint t g i) : ℚ) := by
  apply jointMatrix_parity_rank_relative h2 t g i A R τ
  exact (normalizedTail_le_iff r (Q - 1) A R Δ τ
    (Nat.zero_lt_of_lt g.isLt) (Nat.zero_lt_of_lt i.isLt)).mp htail

end ConcreteMatrix

end SubexponentialSAT.Subexp.SpectralRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SpectralRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exponential binomial window applied to the actual universal matrix.
The field is arbitrary of characteristic different from two, and the number
of slots remains a free parameter. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open Module
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixSupport SubexponentialSAT.Subexp.TensorSpectrum
open SubexponentialSAT.Subexp.SpectralRank

variable {K : Type*} [Field K] {r Q Δ R : ℕ}

/-- The actual universal swap matrix has small relative rank defect on the
explicit rational-floor interval. No condition bounds the slot count. -/
theorem centered_jointMatrix_rank_relative (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (finrank K (LinearMap.range (LinearMap.id -
      (jointMatrix i t g R (SubexponentialSAT.BinomialInterpolation.extendCoefficients
        (SubexponentialSAT.BinomialInterpolation.parityCoefficients (K := K)
          (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R))).mulVecLin)) : ℚ) ≤
      ε * (Fintype.card (Joint t g i) : ℚ) := by
  have hΔ : (Δ : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  have ht := centered_normalizedTail_le_of_sq ε hr hQ hR hsize hε hwidth
  have hcancel : (ε * (Δ : ℚ)) / (Δ : ℚ) = ε := by field_simp
  have ht' : normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤
      (ε * (Δ : ℚ)) / (Δ : ℚ) := by simpa only [hcancel] using ht
  have hb := jointMatrix_parity_rank_relative_of_probability (K := K) h2 t g i
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R (ε * (Δ : ℚ)) ht'
  simpa only [hcancel] using hb

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutNumeratorBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# From the rational spectral matrix to the integer constraint family

The integer constraints are literally `d I - N`. Their rational range has
exactly the dimension of `I - M`, and the same numerators supply the ring
row construction from `LayoutScaledMatrices`.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open Matrix Module
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation SubexponentialSAT.Subexp.MatrixSupport
open LayoutScaledMatrices

variable {r Q Δ : ℕ}

theorem rationalDefect_eq (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    rationalDefect i t g A R = (denominator R : ℚ) •
      (1 - jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))) := by
  ext a b
  simp only [rationalDefect, clearedDefect, Int.cast_sub]
  rw [joint_cast ℚ (by norm_num)]
  by_cases hab : a = b <;>
    simp [ hab, smul_eq_mul, mul_sub]

theorem rationalDefect_linear (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    (rationalDefect i t g A R).mulVecLin = (denominator R : ℚ) •
      (LinearMap.id - (jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))).mulVecLin) := by
  rw [rationalDefect_eq]
  apply LinearMap.ext
  intro x
  simp [ ]

theorem rationalDefect_range (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    LinearMap.range (rationalDefect i t g A R).mulVecLin =
      LinearMap.range (LinearMap.id - (jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))).mulVecLin) := by
  rw [rationalDefect_linear]
  apply LinearMap.range_smul
  simp [denominator]

theorem rationalDefect_finrank (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    finrank ℚ (LinearMap.range (rationalDefect i t g A R).mulVecLin) =
      finrank ℚ (LinearMap.range (LinearMap.id - (jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))).mulVecLin)) := by
  rw [rationalDefect_range]

/-- The actual cleared integer matrix inherits the centered spectral bound. -/
theorem centered_rationalDefect_rank_relative_oai
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (R : ℕ) (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (finrank ℚ (LinearMap.range (rationalDefect i t g
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R).mulVecLin) : ℚ) ≤
      ε * (Fintype.card (Joint t g i) : ℚ) := by
  rw [rationalDefect_finrank]
  exact Spectral.centered_jointMatrix_rank_relative (by norm_num)
    t g i ε hr hQ hR hsize hε hwidth

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative_oai
