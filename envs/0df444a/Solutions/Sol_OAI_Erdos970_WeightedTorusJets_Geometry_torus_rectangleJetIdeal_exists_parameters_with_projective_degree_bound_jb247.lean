-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:58:26.522819+00:00
-- url     : https://prove2.me/submissions/9c07ba56-d69f-4b37-a944-bdd4b932feee

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
import Definitions.Def_OAIQ247J007
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_Geometry_DegreeBezout_linear_normalization_weighted_local_length_le_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HomogeneousDeformation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section

open scoped BigOperators

open Module

open MvPolynomial

noncomputable section

namespace WeightedTorusJets.Geometry



theorem finrank_homogeneousSubmodule {σ K : Type*} [Fintype σ] [Field K] (n : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K n) =
      (Fintype.card σ + n - 1).choose n := by
  classical
  let e : Sym σ n ≃ {d : σ →₀ ℕ // d.degree = n} := Sym.equivNatSum σ n
  let : Fintype {d : σ →₀ ℕ // d.degree = n} := Fintype.ofEquiv (Sym σ n) e
  rw [Module.finrank_eq_card_basis (WeightedTorusJets.homogeneousMonomialBasis σ K n)]
  exact (Fintype.card_congr e).symm.trans (Sym.card_sym_eq_choose n)

end WeightedTorusJets.Geometry

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HilbertSeries
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators

open _root_.Filter

open scoped BigOperators

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveDegree_cast (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    (projectiveDegree I hI : ℚ) =
      ((hilbertPolynomial I hI).natDegree.factorial : ℚ) *
        (hilbertPolynomial I hI).leadingCoeff := by
  unfold projectiveDegree
  split_ifs with h
  · simp [h]
  · have hz := (exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose_spec
    have hcast := Int.toNat_of_nonneg hz.1.le
    exact (by exact_mod_cast hcast :
      ((exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose.toNat : ℚ) =
        ((exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose : ℚ)).trans hz.2

end WeightedTorusJets.Geometry.GradedQuotient

end
end

section

namespace WeightedTorusJets

open DirectSum

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
  (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]

theorem decompose_smul_of_homogeneous_right (r : A) {m : M} {j : ℕ}
    (hm : m ∈ ℳ j) (i : ℕ) :
    (decompose ℳ (r • m) (i + j) : M) = (decompose 𝒜 r i : A) • m := by
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_ r
  · simp
  · intro k a
    have ham : (a : A) • m ∈ ℳ (k + j) := by
      simpa only [vadd_eq_add] using SetLike.GradedSMul.smul_mem a.2 hm
    by_cases hki : k = i
    · subst k
      rw [decompose_of_mem_same ℳ ham,
        decompose_of_mem_same 𝒜 a.2]
    · rw [decompose_of_mem_ne ℳ ham
        (by omega : k + j ≠ i + j), decompose_of_mem_ne 𝒜 a.2 hki, zero_smul]
  · intro r s hr hs
    simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
      congrArg₂ (· + ·) hr hs

theorem homogeneous_component_smul_mem (N : Submodule A M) (hN : N.IsHomogeneous ℳ)
    {r : A} (hr : ∀ m : M, r • m ∈ N) (i : ℕ) (m : M) :
    (decompose 𝒜 r i : A) • m ∈ N := by
  refine DirectSum.Decomposition.inductionOn ℳ ?_ ?_ ?_ m
  · simp
  · intro j m
    rw [← decompose_smul_of_homogeneous_right 𝒜 ℳ r m.2 i]
    exact hN (i + j) (hr m)
  · intro m n hm hn
    simpa only [smul_add] using N.add_mem hm hn

theorem exists_homogeneous_annihilator_of_annihilator
    (N : Submodule A M) (hN : N.IsHomogeneous ℳ)
    {r : A} (hr0 : r ≠ 0) (hr : ∀ m : M, r • m ∈ N) :
    ∃ s : A, s ≠ 0 ∧ (∃ i : ℕ, s ∈ 𝒜 i) ∧ ∀ m : M, s • m ∈ N := by
  classical
  have hex : ∃ i : ℕ, (decompose 𝒜 r i : A) ≠ 0 := by
    by_contra! h
    apply hr0
    rw [← sum_support_decompose 𝒜 r]
    exact Finset.sum_eq_zero (fun i _ => h i)
  obtain ⟨i, hi⟩ := hex
  exact ⟨decompose 𝒜 r i, hi, ⟨i, (decompose 𝒜 r i).2⟩,
    homogeneous_component_smul_mem 𝒜 ℳ N hN hr i⟩

theorem exists_homogeneous_annihilator_of_rank_zero [IsDomain A]
    (N : Submodule A M) (hN : N.IsHomogeneous ℳ) [Module.Finite A (M ⧸ N)]
    (hrank : Module.rank A (M ⧸ N) = 0) :
    ∃ s : A, s ≠ 0 ∧ (∃ i : ℕ, s ∈ 𝒜 i) ∧ ∀ m : M, s • m ∈ N := by
  have ht : Module.IsTorsion A (M ⧸ N) := by
    intro x
    obtain ⟨r, hr, hx⟩ := rank_eq_zero_iff.mp hrank x
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hx⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  apply exists_homogeneous_annihilator_of_annihilator 𝒜 ℳ N hN
    (mem_nonZeroDivisors_iff_ne_zero.mp hr0)
  apply (Module.isTorsionBy_quotient_iff N r).mp
  intro x
  exact Submodule.mem_annihilator.mp hr x Submodule.mem_top

include 𝒜 in

theorem decompose_smul_mem_of_homogeneous (N : Submodule A M)
    (r : A) {m : M} (hm : SetLike.IsHomogeneousElem ℳ m) (hNm : m ∈ N) (j : ℕ) :
    (decompose ℳ (r • m) j : M) ∈ N := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul,
    decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  apply N.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hm
  have hki : (decompose 𝒜 r k : A) • m ∈ ℳ (k + i) := by
    simpa only [vadd_eq_add] using
      SetLike.GradedSMul.smul_mem (decompose 𝒜 r k).2 hi
  by_cases h : k + i = j
  · subst j
    rw [decompose_of_mem_same ℳ hki]
    exact N.smul_mem _ hNm
  · rw [decompose_of_mem_ne ℳ hki h]
    exact N.zero_mem

include 𝒜 in

theorem homogeneous_submodule_span (s : Set M)
    (hs : ∀ m ∈ s, SetLike.IsHomogeneousElem ℳ m) :
    (Submodule.span A s).IsHomogeneous ℳ := by
  rintro i m hm
  rw [Finsupp.span_eq_range_linearCombination, LinearMap.mem_range] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum, decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  apply Submodule.sum_mem
  intro z _
  exact decompose_smul_mem_of_homogeneous 𝒜 ℳ _ (c z) (hs z z.2)
    (Submodule.subset_span z.2) i

variable [IsScalarTower K A M]

omit [GradedAlgebra 𝒜] [DirectSum.Decomposition ℳ] in

theorem homogeneous_coefficients_sum_mem {r D n : ℕ} (v : Fin r → M)
    (hv : ∀ i, v i ∈ ℳ D) (hn : D ≤ n) (c : Fin r → 𝒜 (n - D)) :
    (∑ i, (c i : A) • v i) ∈
      (ℳ n ⊓ (Submodule.span A (Set.range v)).restrictScalars K) := by
  constructor
  · apply Submodule.sum_mem
    intro i _
    simpa only [vadd_eq_add, Nat.sub_add_cancel hn] using
      SetLike.GradedSMul.smul_mem (c i).2 (hv i)
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [IsScalarTower K A M] in

theorem exists_homogeneous_coefficients {r D n : ℕ} (v : Fin r → M)
    (hv : ∀ i, v i ∈ ℳ D) (hn : D ≤ n) (y : M)
    (hy : y ∈ ℳ n) (hyspan : y ∈ Submodule.span A (Set.range v)) :
    ∃ c : Fin r → 𝒜 (n - D), (∑ i, (c i : A) • v i) = y := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hyspan
  refine ⟨fun i => decompose 𝒜 (c i) (n - D), ?_⟩
  have hp := congrArg (fun z : M => (decompose ℳ z n : M)) hc
  rw [decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    decompose_of_mem_same ℳ hy] at hp
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  have h := (decompose_smul_of_homogeneous_right 𝒜 ℳ (c i) (hv i) (n - D)).symm
  rw [Nat.sub_add_cancel hn] at h
  exact h

end WeightedTorusJets

open scoped BigOperators

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CoefficientSubspaceEquiv
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.finite_rectangularQuotient _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
namespace WeightedTorusJets

variable {K A M ι : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] [Fintype ι]

theorem finrank_coefficient_subspace (C : Submodule K A) (P : Submodule K M)
    (v : ι → M) (hv : LinearIndependent A v)
    (hmem : ∀ c : ι → C, ∑ i, (c i : A) • v i ∈ P)
    (hrep : ∀ y ∈ P, ∃ c : ι → C, ∑ i, (c i : A) • v i = y) :
    Module.finrank K P = Fintype.card ι * Module.finrank K C := by
  rw [← (coefficientSubspaceEquiv C P v hv hmem hrep).finrank_eq]
  simp [Module.finrank]

end WeightedTorusJets

namespace WeightedTorusJets

theorem finrank_homogeneous_span {K A M : Type*} [Field K] [CommRing A]
    [Algebra K A] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
    (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {r D n : ℕ} (v : Fin r → M) (hv : ∀ i, v i ∈ ℳ D)
    (hlin : LinearIndependent A v) (hn : D ≤ n) :
    Module.finrank K ↥(ℳ n ⊓ (Submodule.span A (Set.range v)).restrictScalars K) =
      r * Module.finrank K (𝒜 (n - D)) := by
  simpa only [Fintype.card_fin] using finrank_coefficient_subspace (𝒜 (n - D))
    (ℳ n ⊓ (Submodule.span A (Set.range v)).restrictScalars K) v hlin
    (homogeneous_coefficients_sum_mem 𝒜 ℳ v hv hn)
    (fun y hy => exists_homogeneous_coefficients 𝒜 ℳ v hv hn y hy.1 hy.2)

end WeightedTorusJets

open scoped BigOperators DirectSum

namespace WeightedTorusJets.Geometry

theorem exists_finset_homogeneous_span_eq_top
    {A K M : Type*} [CommRing A] [Field K] [AddCommGroup M]
    [Module A M] [Module K M] [Module.Finite A M]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜] :
    ∃ s : Finset M, Submodule.span A (s : Set M) = ⊤ ∧
      ∀ x ∈ s, ∃ n, x ∈ 𝓜 n := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let t := s.biUnion fun x => (DirectSum.decompose 𝓜 x).support.image
    fun n => (DirectSum.decompose 𝓜 x n : M)
  refine ⟨t, ?_, ?_⟩
  · apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← DirectSum.sum_support_decompose 𝓜 x]
    apply Submodule.sum_mem
    intro n hn
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  · intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨n, (DirectSum.decompose 𝓜 y n).property⟩

theorem exists_homogeneous_generic_basis
    {A K M F N : Type*} [CommRing A] [Field K] [Field F]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module K M]
    [Algebra A F] [IsFractionRing A F] [Module A N] [Module F N]
    [IsScalarTower A F N] [Module.Finite A M]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    (f : M →ₗ[A] N) [IsLocalizedModule (nonZeroDivisors A) f] :
    ∃ v : Fin (Module.finrank F N) → M,
      ∃ b : Module.Basis (Fin (Module.finrank F N)) F N,
        (∀ i, f (v i) = b i) ∧
        (∀ i, ∃ n, v i ∈ 𝓜 n) ∧ LinearIndependent A v := by
  classical
  have : Module.Finite F N :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors A) (Rₚ := F) f
  have : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr (IsFractionRing.injective A F)
  obtain ⟨s, hs, hhom⟩ := exists_finset_homogeneous_span_eq_top (A := A) 𝓜
  have hspan : Submodule.span F (f '' (s : Set M)) = ⊤ :=
    span_eq_top_of_isLocalizedModule F (nonZeroDivisors A) f hs
  let ι := (linearIndepOn_empty F (id : N → N)).extend
    (Set.empty_subset (f '' (s : Set M)))
  let b₀ : Module.Basis ι F N := Module.Basis.ofSpan hspan.ge
  let := Module.Finite.finite_basis b₀
  let := Fintype.ofFinite ι
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hpre (i : Fin (Module.finrank F N)) : ∃ x ∈ s, f x = b i := by
    apply Module.Basis.ofSpan_subset hspan.ge
    refine ⟨e.symm i, ?_⟩
    exact (Module.Basis.reindex_apply b₀ e i).symm
  choose v hv hvf using hpre
  refine ⟨v, b, hvf, fun i => hhom _ (hv i), ?_⟩
  have hcomp : f ∘ v = b := funext hvf
  apply LinearIndependent.of_comp f
  rw [hcomp]
  exact b.linearIndependent.restrict_scalars' A

theorem finrank_quotient_span_eq_zero_of_full_rank
    {A M : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent A v) (hn : n = Module.finrank A M) :
    Module.finrank A (M ⧸ Submodule.span A (Set.range v)) = 0 := by
  have h := (Submodule.span A (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin] at h
  omega

theorem generic_fiber_finrank_eq
    {A M F N : Type*} [CommRing A] [Field F]
    [AddCommGroup M] [AddCommGroup N] [Module A M]
    [Algebra A F] [IsFractionRing A F] [Module A N] [Module F N]
    [IsScalarTower A F N] (f : M →ₗ[A] N)
    [IsLocalizedModule (nonZeroDivisors A) f] :
    Module.finrank F N = Module.finrank A M :=
  (IsLocalization.finrank_eq F (nonZeroDivisors A) le_rfl).trans
    (IsLocalizedModule.finrank_eq (nonZeroDivisors A) f le_rfl)

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem exists_common_degree_independent
    {K A M ι : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [Fintype ι]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (𝓜 : ℕ → Submodule K M)
    [SetLike.GradedSMul 𝓐 𝓜]
    {a : A} (ha0 : a ≠ 0) (ha1 : a ∈ 𝓐 1)
    {v : ι → M} (hv : LinearIndependent A v)
    (hhom : ∀ i, ∃ n, v i ∈ 𝓜 n) :
    ∃ D : ℕ, ∃ w : ι → M, LinearIndependent A w ∧ ∀ i, w i ∈ 𝓜 D := by
  classical
  choose e he using hhom
  let D := Finset.univ.sup e
  let w := fun i => a ^ (D - e i) • v i
  refine ⟨D, w, ?_, ?_⟩
  · apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hc' : ∑ j, (c j * a ^ (D - e j)) • v j = 0 := by
      simpa only [mul_smul] using hc
    exact (mul_eq_zero.mp (Fintype.linearIndependent_iff.mp hv _ hc' i)).resolve_right
      (pow_ne_zero _ ha0)
  · intro i
    have hei : e i ≤ D := Finset.le_sup (Finset.mem_univ i)
    have ha : a ^ (D - e i) ∈ 𝓐 (D - e i) := by
      simpa using SetLike.pow_mem_graded (D - e i) ha1
    have hw := SetLike.GradedSMul.smul_mem ha (he i)
    simpa only [vadd_eq_add, Nat.sub_add_cancel hei] using hw



variable {K A M : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [Module.IsTorsionFree A M]
    (𝓐 : ℕ → Submodule K A) (𝓜 : ℕ → Submodule K M)
    [SetLike.GradedSMul 𝓐 𝓜]

theorem finrank_gradedPiece_le_shifted_submodule
    (N : Submodule A M) {b : A} {E : ℕ} (hb0 : b ≠ 0) (hb : b ∈ 𝓐 E)
    (hN : ∀ m : M, b • m ∈ N) (n : ℕ)
    [Module.Finite K (𝓜 (E + n))] :
    Module.finrank K (𝓜 n) ≤
      Module.finrank K ↥((𝓜 (E + n)) ⊓ N.restrictScalars K) := by
  have hle : (𝓜 (E + n)) ⊓ N.restrictScalars K ≤ 𝓜 (E + n) := inf_le_left
  have : Module.Finite K ↥((𝓜 (E + n)) ⊓ N.restrictScalars K) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  let f : 𝓜 n →ₗ[K] ↥((𝓜 (E + n)) ⊓ N.restrictScalars K) :=
    { toFun m := ⟨b • (m : M),
        ⟨by
          change b • (m : M) ∈ 𝓜 (E + n)
          exact SetLike.GradedSMul.smul_mem hb m.property,
          hN m⟩⟩
      map_add' m m' := by ext; exact smul_add b (m : M) m'
      map_smul' c m := by ext; exact smul_comm b c (m : M) }
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro x y h
  apply Subtype.ext
  exact smul_right_injective M hb0 (congrArg Subtype.val h)

omit [IsDomain A] [Module.IsTorsionFree A M] in

theorem finrank_gradedSubmodule_le
    (N : Submodule A M) (n : ℕ) [Module.Finite K (𝓜 n)] :
    Module.finrank K ↥((𝓜 n) ⊓ N.restrictScalars K) ≤ Module.finrank K (𝓜 n) :=
  Submodule.finrank_mono inf_le_left

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem exists_hilbert_finrank_sandwich
    {K A M : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [Module.Finite A M] [Module.IsTorsionFree A M]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] [∀ n, Module.Finite K (𝓜 n)]
    {a : A} (ha0 : a ≠ 0) (ha1 : a ∈ 𝓐 1)
    (d : ℕ) (hdim : ∀ n, Module.finrank K (𝓐 n) = (n + d).choose d) :
    ∃ D E : ℕ, ∀ n, D ≤ n →
      Module.finrank A M * ((n - D + d).choose d) ≤ Module.finrank K (𝓜 n) ∧
      Module.finrank K (𝓜 n) ≤
        Module.finrank A M * ((n + E - D + d).choose d) := by
  classical
  let f := LocalizedModule.mkLinearMap (nonZeroDivisors A) M
  obtain ⟨v, _, _, hhom, hv⟩ := exists_homogeneous_generic_basis
    (F := FractionRing A) 𝓜 f
  have hr := generic_fiber_finrank_eq (F := FractionRing A) f
  obtain ⟨D, w, hw, hwD⟩ := exists_common_degree_independent 𝓐 𝓜 ha0 ha1 hv hhom
  let N := Submodule.span A (Set.range w)
  have hN : N.IsHomogeneous 𝓜 := by
    apply WeightedTorusJets.homogeneous_submodule_span 𝓐 𝓜
    rintro x ⟨i, rfl⟩
    exact ⟨D, hwD i⟩
  have hzero : Module.finrank A (M ⧸ N) = 0 :=
    finrank_quotient_span_eq_zero_of_full_rank hw hr
  have hrank : Module.rank A (M ⧸ N) = 0 := by
    rw [← Module.finrank_eq_rank, hzero, Nat.cast_zero]
  obtain ⟨b, hb0, ⟨E, hbE⟩, hbN⟩ :=
    WeightedTorusJets.exists_homogeneous_annihilator_of_rank_zero 𝓐 𝓜 N hN hrank
  refine ⟨D, E, fun n hn => ⟨?_, ?_⟩⟩
  · have h := finrank_gradedSubmodule_le 𝓜 N n
    change Module.finrank K ↥(𝓜 n ⊓ (Submodule.span A (Set.range w)).restrictScalars K) ≤ _ at h
    rw [WeightedTorusJets.finrank_homogeneous_span 𝓐 𝓜 w hwD hw hn, hr, hdim] at h
    exact h
  · have h := finrank_gradedPiece_le_shifted_submodule 𝓐 𝓜 N hb0 hbE hbN n
    change _ ≤ Module.finrank K
      ↥(𝓜 (E + n) ⊓ (Submodule.span A (Set.range w)).restrictScalars K) at h
    rw [WeightedTorusJets.finrank_homogeneous_span 𝓐 𝓜 w hwD hw (by omega), hr, hdim] at h
    simpa only [Nat.add_comm E n] using h

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open _root_.Filter _root_.Polynomial

theorem leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (P : Polynomial ℚ)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_cases hP : P = 0
  · simp [hP]
  · exact (leadingCoeff_pos_of_eventually_nat_eval_nonneg P hP hpos).le

theorem natDegree_leadingCoeff_eq_of_eventually_nat_eval_sandwich
    (P L U : Polynomial ℚ) (d : ℕ)
    (hL : L.natDegree = d) (hU : U.natDegree = d)
    (hLU : L.leadingCoeff = U.leadingCoeff) (hpos : 0 < L.leadingCoeff)
    (hlo : ∀ᶠ n : ℕ in atTop, L.eval (n : ℚ) ≤ P.eval (n : ℚ))
    (hhi : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ U.eval (n : ℚ)) :
    P.natDegree = d ∧ P.leadingCoeff = L.leadingCoeff := by
  have hlo' : ∀ᶠ n : ℕ in atTop, 0 ≤ (P - L).eval (n : ℚ) := by
    filter_upwards [hlo] with n hn
    simpa only [eval_sub] using sub_nonneg.mpr hn
  have hhi' : ∀ᶠ n : ℕ in atTop, 0 ≤ (U - P).eval (n : ℚ) := by
    filter_upwards [hhi] with n hn
    simpa only [eval_sub] using sub_nonneg.mpr hn
  have hcPL := leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (P - L) hlo'
  have hcUP := leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (U - P) hhi'
  have hLne : L ≠ 0 := leadingCoeff_ne_zero.mp hpos.ne'
  have hUne : U ≠ 0 := leadingCoeff_ne_zero.mp (hLU ▸ hpos.ne')
  have hdegreeLU : L.degree = U.degree := by
    rw [degree_eq_natDegree hLne, degree_eq_natDegree hUne, hL, hU]
  have hdegLP : L.degree ≤ P.degree := by
    by_contra h
    rw [leadingCoeff_sub_of_degree_lt' (lt_of_not_ge h)] at hcPL
    linarith
  have hdegPU : P.degree ≤ U.degree := by
    by_contra h
    have hUP : U.degree < P.degree := lt_of_not_ge h
    have hLP : L.degree < P.degree := hdegreeLU ▸ hUP
    rw [leadingCoeff_sub_of_degree_lt hLP] at hcPL
    rw [leadingCoeff_sub_of_degree_lt' hUP] at hcUP
    have hPne : P ≠ 0 := ne_zero_of_degree_gt hUP
    exact (leadingCoeff_ne_zero.mpr hPne) (by linarith)
  have hdeg : P.degree = L.degree := le_antisymm (hdegPU.trans_eq hdegreeLU.symm) hdegLP
  have hnat : P.natDegree = d := (natDegree_eq_natDegree hdeg).trans hL
  refine ⟨hnat, ?_⟩
  have coeff_nonneg (Q : Polynomial ℚ) (hQ : Q.natDegree ≤ d)
      (hQpos : ∀ᶠ n : ℕ in atTop, 0 ≤ Q.eval (n : ℚ)) : 0 ≤ Q.coeff d := by
    rcases hQ.eq_or_lt with h | h
    · rw [← h, coeff_natDegree]
      exact leadingCoeff_nonneg_of_eventually_nat_eval_nonneg Q hQpos
    · rw [coeff_eq_zero_of_natDegree_lt h]
  have hsub₁ : (P - L).natDegree ≤ d := by
    simpa only [hnat, hL, max_self] using natDegree_sub_le P L
  have hsub₂ : (U - P).natDegree ≤ d := by
    simpa only [hnat, hU, max_self] using natDegree_sub_le U P
  have hcoeff₁ := coeff_nonneg (P - L) hsub₁ hlo'
  have hcoeff₂ := coeff_nonneg (U - P) hsub₂ hhi'
  have hcoeffP : P.coeff d = P.leadingCoeff := by rw [← hnat, coeff_natDegree]
  have hcoeffL : L.coeff d = L.leadingCoeff := by rw [← hL, coeff_natDegree]
  have hcoeffU : U.coeff d = U.leadingCoeff := by rw [← hU, coeff_natDegree]
  rw [coeff_sub, hcoeffP, hcoeffL] at hcoeff₁
  rw [coeff_sub, hcoeffU, hcoeffP, ← hLU] at hcoeff₂
  linarith

theorem natDegree_leadingCoeff_eq_of_eventually_binomial_sandwich
    (P : Polynomial ℚ) (d D E r : ℕ) (hr : 0 < r)
    (hlo : ∀ᶠ n : ℕ in atTop,
      (r : ℚ) * ((n - D + d).choose d : ℚ) ≤ P.eval (n : ℚ))
    (hhi : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) ≤ (r : ℚ) * ((n + E - D + d).choose d : ℚ)) :
    P.natDegree = d ∧ P.leadingCoeff = (r : ℚ) / (d.factorial : ℚ) := by
  let L : Polynomial ℚ := (r : ℚ) • preHilbertPoly ℚ d D
  let U : Polynomial ℚ := (r : ℚ) •
    (preHilbertPoly ℚ d D).comp (Polynomial.X + Polynomial.C (E : ℚ))
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hL : L.natDegree = d := by
    dsimp [L]
    rw [natDegree_smul _ hr0, natDegree_preHilbertPoly]
  have hU : U.natDegree = d := by
    dsimp [U]
    rw [natDegree_smul _ hr0, natDegree_comp, natDegree_preHilbertPoly,
      natDegree_add_C, natDegree_X, mul_one]
  have hcL : L.leadingCoeff = (r : ℚ) / (d.factorial : ℚ) := by
    rw [leadingCoeff, hL]
    change ((r : ℚ) • preHilbertPoly ℚ d D).coeff d = _
    rw [coeff_smul, coeff_preHilbertPoly_self]
    rfl
  have hcU : U.leadingCoeff = (r : ℚ) / (d.factorial : ℚ) := by
    have hcompdeg : ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).natDegree = d := by
      rw [natDegree_comp, natDegree_preHilbertPoly, natDegree_add_C, natDegree_X, mul_one]
    have hcompcoeff : ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff d =
        ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).leadingCoeff := by
      calc
        _ = ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff
            ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).natDegree :=
          congrArg ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff hcompdeg.symm
        _ = _ := coeff_natDegree
    rw [leadingCoeff, hU]
    change ((r : ℚ) • (preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff d = _
    rw [coeff_smul, hcompcoeff,
      leadingCoeff_comp (by rw [natDegree_add_C, natDegree_X]; decide),
      leadingCoeff_preHilbertPoly, leadingCoeff_X_add_C, one_pow, mul_one]
    rfl
  have hLpos : 0 < L.leadingCoeff := by rw [hcL]; positivity
  have hL_eval : ∀ᶠ n : ℕ in atTop, L.eval (n : ℚ) ≤ P.eval (n : ℚ) := by
    filter_upwards [hlo, eventually_ge_atTop D] with n hn hDn
    have hind : n + d - D = n - D + d := by omega
    simpa only [L, eval_smul, smul_eq_mul,
      preHilbertPoly_eq_choose_sub_add ℚ d hDn] using hn
  have hU_eval : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ U.eval (n : ℚ) := by
    filter_upwards [hhi, eventually_ge_atTop D] with n hn hDn
    have hind : n + E + d - D = n + E - D + d := by omega
    simpa only [U, eval_smul, smul_eq_mul, eval_comp, eval_add, eval_X, eval_C,
      ← Nat.cast_add,
      preHilbertPoly_eq_choose_sub_add ℚ d (by omega : D ≤ n + E)] using hn
  obtain ⟨hdeg, hlc⟩ := natDegree_leadingCoeff_eq_of_eventually_nat_eval_sandwich
    P L U d hL hU (hcL.trans hcU.symm) hLpos hL_eval hU_eval
  exact ⟨hdeg, hlc.trans hcL⟩

end WeightedTorusJets.Geometry
end

section
namespace WeightedTorusJets.Geometry

open _root_.Filter

theorem hilbertPolynomial_degree_coefficient_eq_rank
    {K A M : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [Module.Finite A M] [Module.IsTorsionFree A M] [Nontrivial M]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] [∀ n, Module.Finite K (𝓜 n)]
    {a : A} (ha0 : a ≠ 0) (ha1 : a ∈ 𝓐 1)
    (d : ℕ) (hdim : ∀ n, Module.finrank K (𝓐 n) = (n + d).choose d)
    (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in atTop, (Module.finrank K (𝓜 n) : ℚ) = P.eval (n : ℚ)) :
    P.natDegree = d ∧ (d.factorial : ℚ) * P.leadingCoeff = (Module.finrank A M : ℚ) := by
  obtain ⟨D, E, hDE⟩ := exists_hilbert_finrank_sandwich 𝓐 𝓜 ha0 ha1 d hdim
  have hlo : ∀ᶠ n : ℕ in atTop,
      (Module.finrank A M : ℚ) * ((n - D + d).choose d : ℚ) ≤ P.eval (n : ℚ) := by
    filter_upwards [hP, eventually_ge_atTop D] with n hPn hn
    rw [← hPn]
    exact_mod_cast (hDE n hn).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) ≤ (Module.finrank A M : ℚ) * ((n + E - D + d).choose d : ℚ) := by
    filter_upwards [hP, eventually_ge_atTop D] with n hPn hn
    rw [← hPn]
    exact_mod_cast (hDE n hn).2
  obtain ⟨hdeg, hlc⟩ := natDegree_leadingCoeff_eq_of_eventually_binomial_sandwich
    P d D E (Module.finrank A M) (Module.finrank_pos (R := A) (M := M)) hlo hhi
  refine ⟨hdeg, ?_⟩
  rw [hlc]
  field_simp

end WeightedTorusJets.Geometry
end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConeMap
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.parameterIdeal_isPrime _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem X_none_not_mem_coneIdeal (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    X none ∉ coneIdeal p := by
  simpa only [coneIdeal, RingHom.mem_ker, coneMap_X_none] using
    (Polynomial.X_ne_zero : (Polynomial.X : Polynomial (MvPolynomial σ K ⧸ p)) ≠ 0)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] coneIdeal_isPrime polynomialAwayPrime_isPrime

theorem conePolynomialLocalEquiv_algebraMap (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : MvPolynomial (Option σ) K) :
    conePolynomialLocalEquiv p
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)) f) =
      algebraMap (Polynomial (MvPolynomial σ K))
        (Localization.AtPrime (p.map Polynomial.C)) (conePolynomialMap f) := by
  dsimp only [conePolynomialLocalEquiv, AlgEquiv.trans_apply]
  rw [AlgEquiv.symm_apply_eq]
  simp only [AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Option σ) K)
    (Localization.Away (X (none : Option σ) : MvPolynomial (Option σ) K))]
  rw [IsScalarTower.algebraMap_apply (Polynomial (MvPolynomial σ K))
    (Localization.Away (Polynomial.X : Polynomial (MvPolynomial σ K)))]
  exact (Localization.localRingHom_to_map _ _ coneAwayEquiv.toRingHom rfl _).trans
    (congrArg _ (coneAwayEquiv_algebraMap f))

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] coneIdeal_isPrime Polynomial.algebra Polynomial.isLocalization

theorem coneLocalEquiv_algebraMap (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : MvPolynomial (Option σ) K) :
    coneLocalEquiv p
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)) f) =
      algebraMap (Polynomial (Localization.AtPrime p))
        (Localization.AtPrime
          ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map Polynomial.C))
        (Polynomial.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))
          (conePolynomialMap f)) := by
  change DegreeBezout.polynomialLocalCoefficientPolyEquiv p
    (conePolynomialLocalEquiv p
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)) f)) = _
  rw [conePolynomialLocalEquiv_algebraMap, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply (Polynomial (MvPolynomial σ K))
    (Polynomial (Localization.AtPrime p))]
  rfl

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem polynomial_height_map_C (p : Ideal A) [p.IsPrime] :
    (p.map (Polynomial.C : A →+* Polynomial A)).height = p.height := by
  have : (p.map (Polynomial.C : A →+* Polynomial A)).LiesOver p := by
    constructor
    ext r
    change r ∈ p ↔ Polynomial.C r ∈ p.map Polynomial.C
    constructor
    · exact Ideal.mem_map_of_mem _
    · intro h
      simpa only [Polynomial.coeff_C_zero] using (Ideal.mem_map_C_iff.mp h) 0
  simp [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K σ : Type*} [CommRing K] [IsNoetherianRing K] [Finite σ]

theorem coneIdeal_height (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (coneIdeal p).height = p.height := by
  let : (coneIdeal p).IsPrime := coneIdeal_isPrime p
  have h := ringKrullDim_eq_of_ringEquiv (conePolynomialLocalEquiv p).toRingEquiv
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (coneIdeal p)
      (Localization.AtPrime (coneIdeal p)),
    IsLocalization.AtPrime.ringKrullDim_eq_height (p.map Polynomial.C)
      (Localization.AtPrime (p.map Polynomial.C)), polynomial_height_map_C] at h
  exact WithBot.coe_eq_coe.mp h

end WeightedTorusJets.Geometry

end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_Homogenize
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.parameterIdeal_isPrime _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section

section

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

theorem homogenize_isHomogeneous (f : MvPolynomial σ K) :
    (homogenize f).IsHomogeneous f.totalDegree := by
  apply IsHomogeneous.sum
  intro i hi
  have hi' : i ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hrename : (rename some (homogeneousComponent i f)).IsHomogeneous i := by
    rw [rename_eq_aeval]
    simpa only [one_mul] using (homogeneousComponent_isHomogeneous i f).aeval
      (X ∘ some) (fun j => isHomogeneous_X K (some j))
  simpa only [Nat.sub_add_cancel hi'] using
    (isHomogeneous_X_pow (R := K) (none : Option σ) (f.totalDegree - i)).mul hrename

theorem dehomogenize_homogenize (f : MvPolynomial σ K) :
    MvPolynomial.aeval (fun o : Option σ => o.elim (1 : MvPolynomial σ K) X) (homogenize f) = f := by
  simp only [homogenize, map_sum, map_mul, map_pow, aeval_X, Option.elim_none,
    one_pow, one_mul, aeval_rename, Function.comp_def, Option.elim_some, aeval_X_left_apply]
  exact sum_homogeneousComponent f

theorem homogenize_totalDegree (f : MvPolynomial σ K) :
    (homogenize f).totalDegree = f.totalDegree := by
  by_cases hf : f = 0
  · simp [hf, homogenize]
  · apply (homogenize_isHomogeneous f).totalDegree
    intro hzero
    apply hf
    rw [← dehomogenize_homogenize f, hzero, map_zero]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem eval₂_homogenize
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S) (t : S)
    (p : MvPolynomial σ K) :
    (homogenize p).eval₂ c (fun o : Option σ => o.elim t (fun i => x i * t)) =
      p.eval₂ c x * t ^ p.totalDegree := by
  have hx : (fun o : Option σ => o.elim t (fun i => x i * t)) =
      (fun o : Option σ => (o.elim 1 x) * t) := by
    funext o
    cases o <;> simp
  rw [hx, homogeneous_eval₂_mul (homogenize_isHomogeneous p)]
  congr 1
  have hcomp : (eval₂Hom c x).comp (MvPolynomial.aeval
      (fun o : Option σ => o.elim (1 : MvPolynomial σ K) X)).toRingHom =
      eval₂Hom c (fun o : Option σ => o.elim 1 x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro o
      cases o <;> simp
  have h := congrArg (eval₂Hom c x) (dehomogenize_homogenize p)
  change ((eval₂Hom c x).comp (MvPolynomial.aeval
    (fun o : Option σ => o.elim (1 : MvPolynomial σ K) X)).toRingHom) (homogenize p) = _ at h
  rwa [hcomp] at h

theorem polynomial_eval₂_homogenize
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S)
    (p : MvPolynomial σ K) :
    (homogenize p).eval₂ (Polynomial.C.comp c)
      (fun o : Option σ => o.elim Polynomial.X (fun i => Polynomial.C (x i) * Polynomial.X)) =
      Polynomial.C (p.eval₂ c x) * Polynomial.X ^ p.totalDegree := by
  rw [eval₂_homogenize, ← MvPolynomial.hom_eval₂]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem conePolynomialMap_homogenize {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) :
    conePolynomialMap (homogenize f) = Polynomial.C f * Polynomial.X ^ f.totalDegree := by
  rw [conePolynomialMap, aeval_def]
  have halg : algebraMap K (Polynomial (MvPolynomial σ K)) =
      Polynomial.C.comp (algebraMap K (MvPolynomial σ K)) := by
    apply RingHom.ext
    intro r
    exact Polynomial.algebraMap_apply (A := MvPolynomial σ K) r
  rw [halg, polynomial_eval₂_homogenize, MvPolynomial.algebraMap_eq]
  simp

theorem conePolynomialMap_padded_homogenize {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (e : ℕ) :
    conePolynomialMap ((X (none : Option σ)) ^ e * homogenize f) =
      Polynomial.C f * Polynomial.X ^ (e + f.totalDegree) := by
  rw [map_mul, map_pow, conePolynomialMap_X_none, conePolynomialMap_homogenize, pow_add]
  exact mul_left_comm _ _ _

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem quotient_length_eq_of_flat_local_extension
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B]
    (hm : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  let : IsLocalHom (algebraMap A B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out (3-1) (1-1)).mp hm.le
  have hlength : Module.length B (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
    infer_instance
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange A B (A ⧸ I), hm, hlength, mul_one]

theorem quotient_length_local_polynomial
    {A : Type*} [CommRing A] [IsLocalRing A] (I : Ideal A) :
    let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
    let B := Localization.AtPrime p
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  dsimp only
  let : Module.Free A (Polynomial A) := .of_basis (Polynomial.basisMonomials A)
  apply quotient_length_eq_of_flat_local_extension
  rw [IsScalarTower.algebraMap_eq A (Polynomial A) _, ← Ideal.map_map,
    Polynomial.algebraMap_eq]
  exact Localization.AtPrime.map_eq_maximalIdeal

theorem local_polynomial_parameter_isUnit
    {A : Type*} [CommRing A] [IsLocalRing A] :
    let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
    let B := Localization.AtPrime p
    IsUnit (algebraMap (Polynomial A) B Polynomial.X) := by
  dsimp only
  apply IsLocalization.map_units
    (M := ((IsLocalRing.maximalIdeal A).map
      (Polynomial.C : A →+* Polynomial A)).primeCompl) _ ⟨Polynomial.X, ?_⟩
  change Polynomial.X ∉
    (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
  intro h
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    simpa using (Ideal.mem_map_C_iff.mp h) 1
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    ((IsLocalRing.maximalIdeal A).eq_top_of_isUnit_mem h1 isUnit_one)



theorem span_range_mul_units {ι A : Type*} [CommRing A]
    (a u : ι → A) (hu : ∀ i, IsUnit (u i)) :
    Ideal.span (Set.range fun i => a i * u i) = Ideal.span (Set.range a) := by
  simp only [Ideal.span_range_eq_iSup, Ideal.span_singleton_mul_right_unit (hu _)]

theorem quotient_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) :
    Module.length B (B ⧸ I.map e) = Module.length A (A ⧸ I) := by
  rw [Module.length_quotient, Module.length_quotient]
  exact Order.coheight_orderIso e.idealComapOrderIso.symm I

theorem radical_map_eq_maximal_of_radical_eq
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hm : (IsLocalRing.maximalIdeal A).map f = IsLocalRing.maximalIdeal B)
    (I : Ideal A) (hI : I.radical = IsLocalRing.maximalIdeal A) :
    (I.map f).radical = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · exact (Ideal.radical_mono (Ideal.map_mono (I.le_radical.trans_eq hI))).trans_eq
      (by rw [hm]; exact Ideal.IsPrime.radical inferInstance)
  · rw [← hm, ← hI]
    exact Ideal.map_radical_le f

theorem local_polynomial_scaled_span {ι A : Type*} [CommRing A] [IsLocalRing A]
    (a : ι → A) (e : ι → ℕ) :
    let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
    let B := Localization.AtPrime p
    Ideal.span (Set.range fun i =>
      algebraMap (Polynomial A) B (Polynomial.C (a i) * Polynomial.X ^ e i)) =
        (Ideal.span (Set.range a)).map (algebraMap A B) := by
  dsimp only
  let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
  let B := Localization.AtPrime p
  have hunit : IsUnit (algebraMap (Polynomial A) B Polynomial.X) :=
    local_polynomial_parameter_isUnit
  simp only [map_mul, map_pow]
  rw [span_range_mul_units _ _ (fun i => hunit.pow (e i)), Ideal.map_span, ← Set.range_comp]
  rfl



open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

attribute [local instance] coneIdeal_isPrime

theorem coneLocalEquiv_padded_ideal {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ) :
    let A := MvPolynomial σ K
    let R := Localization.AtPrime p
    let S := MvPolynomial (Option σ) K
    let L := Localization.AtPrime (coneIdeal p)
    let B := Localization.AtPrime ((IsLocalRing.maximalIdeal R).map Polynomial.C)
    ((paddedHomogenizedIdeal f n).map (algebraMap S L)).map (coneLocalEquiv p).toRingHom =
      ((Ideal.span (Set.range f)).map (algebraMap A R)).map (algebraMap R B) := by
  dsimp only
  let A := MvPolynomial σ K
  let R := Localization.AtPrime p
  let S := MvPolynomial (Option σ) K
  let L := Localization.AtPrime (coneIdeal p)
  let B := Localization.AtPrime ((IsLocalRing.maximalIdeal R).map Polynomial.C)
  have hgen (i : ι) : coneLocalEquiv p
      (algebraMap S L ((X (none : Option σ)) ^ n i * homogenize (f i))) =
      algebraMap (Polynomial R) B
        (Polynomial.C (algebraMap A R (f i)) * Polynomial.X ^ (n i + (f i).totalDegree)) := by
    rw [coneLocalEquiv_algebraMap, conePolynomialMap_padded_homogenize]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  calc
    _ = Ideal.span (Set.range fun i => algebraMap (Polynomial R) B
        (Polynomial.C (algebraMap A R (f i)) * Polynomial.X ^ (n i + (f i).totalDegree))) := by
      simp only [paddedHomogenizedIdeal, Ideal.map_span,
        ← Set.range_comp, Function.comp_def]
      exact congrArg (fun v : ι → B => Ideal.span (Set.range v)) (funext hgen)
    _ = (Ideal.span (Set.range fun i => algebraMap A R (f i))).map (algebraMap R B) :=
      local_polynomial_scaled_span (fun i => algebraMap A R (f i))
        (fun i => n i + (f i).totalDegree)
    _ = _ := by
      change (Ideal.span (Set.range fun i => algebraMap A R (f i))).map (algebraMap R B) =
        ((Ideal.span (Set.range f)).map (algebraMap A R)).map (algebraMap R B)
      congr 1
      rw [Ideal.map_span, ← Set.range_comp]
      rfl

theorem cone_padded_quotient_length {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ) :
    let A := MvPolynomial σ K
    let R := Localization.AtPrime p
    let S := MvPolynomial (Option σ) K
    let L := Localization.AtPrime (coneIdeal p)
    Module.length L (L ⧸ (paddedHomogenizedIdeal f n).map (algebraMap S L)) =
      Module.length R (R ⧸ (Ideal.span (Set.range f)).map (algebraMap A R)) := by
  dsimp only
  let : CommRing (Localization.AtPrime p) := inferInstance
  let : CommRing (Polynomial (Localization.AtPrime p)) := inferInstance
  let B := Localization.AtPrime
    ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map Polynomial.C)
  refine (quotient_length_eq_of_ringEquiv (B := B)
    (coneLocalEquiv p).toRingEquiv _).symm.trans ?_
  exact (congrArg (fun I : Ideal B => Module.length B (B ⧸ I))
    (coneLocalEquiv_padded_ideal p f n)).trans (quotient_length_local_polynomial _)

theorem cone_padded_local_radical {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ)
    (hf : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    ((paddedHomogenizedIdeal f n).map
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime (coneIdeal p)) := by
  let A := MvPolynomial σ K
  let R := Localization.AtPrime p
  let S := MvPolynomial (Option σ) K
  let L := Localization.AtPrime (coneIdeal p)
  let B := Localization.AtPrime ((IsLocalRing.maximalIdeal R).map Polynomial.C)
  let : CommRing R := inferInstance
  let : CommRing (Polynomial R) := inferInstance
  let J : Ideal L := (paddedHomogenizedIdeal f n).map (algebraMap S L)
  have hradB : (J.map (coneLocalEquiv p).toRingHom).radical = IsLocalRing.maximalIdeal B := by
    change (((paddedHomogenizedIdeal f n).map (algebraMap S L)).map
      (coneLocalEquiv p).toRingHom).radical = _
    rw [coneLocalEquiv_padded_ideal]
    apply radical_map_eq_maximal_of_radical_eq (A := R) (B := B) (algebraMap R B) _ _ hf
    rw [IsScalarTower.algebraMap_eq R (Polynomial R) _, ← Ideal.map_map,
      Polynomial.algebraMap_eq]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have hradL : J.radical = IsLocalRing.maximalIdeal L := by
    let : IsLocalHom (coneLocalEquiv p).toRingHom :=
      IsLocalHom.of_surjective _ (coneLocalEquiv p).surjective
    have h := congrArg (Ideal.comap (coneLocalEquiv p).toRingHom) hradB
    rw [Ideal.comap_radical,
      Ideal.comap_map_of_bijective (coneLocalEquiv p).toRingHom (coneLocalEquiv p).bijective,
      IsLocalRing.maximalIdeal_comap] at h
    exact h
  exact hradL

end WeightedTorusJets.Geometry

end

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LocalFractionAlgebra
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section

section

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem maximal_polynomial_height (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsMaximal] : p.height = n := by
  induction n with
  | zero =>
    have h := p.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    have h0 : p.height ≤ 0 := WithBot.coe_le_coe.mp (by simpa using h)
    exact le_antisymm h0 bot_le
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) := p.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver q := ⟨rfl⟩
    have hq : q.height = n := ih q
    calc
      p.height = P.height := (e.height_map p).symm
      _ = q.height + 1 := Polynomial.height_eq_height_add_one q P
      _ = (n + 1 : ℕ) := by rw [hq]; simp

end WeightedTorusJets.Geometry

end

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_InvariantDerivation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section


namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem maximal_mvPolynomial_height {σ : Type*} [Fintype σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsMaximal] : p.height = Fintype.card σ := by
  let e := (MvPolynomial.renameEquiv K (Fintype.equivFin σ)).toRingEquiv
  have := maximal_polynomial_height (Fintype.card σ) (p.map e)
  rwa [e.height_map] at this

end WeightedTorusJets.Geometry











namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

theorem regular_local_maximal_height [IsRegularLocalRing R] :
    (IsLocalRing.maximalIdeal R).height =
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) : ℕ∞) := by
  apply WithBot.coe_injective
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K R : Type*} [Field K] [Infinite K] [CommRing R] [Algebra K R]

theorem exists_mem_submodule_notMem_ideals (V : Submodule K R)
    {ι : Type*} [Finite ι] (p : ι → Ideal R)
    (hp : ∀ i, ¬ Ideal.span (V : Set R) ≤ p i) :
    ∃ x ∈ V, ∀ i, x ∉ p i := by
  let q (i : ι) : Submodule K V :=
    ((p i).restrictScalars K).comap V.subtype
  have hq (i : ι) : q i ≠ ⊤ := by
    intro hi
    apply hp i
    rw [Ideal.span_le]
    intro x hx
    have : (⟨x, hx⟩ : V) ∈ q i := hi ▸ Submodule.mem_top
    exact this
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top q hq
  exact ⟨x, x.property, hx⟩

theorem exists_finset_mem_submodule_height [IsNoetherianRing R]
    (V : Submodule K R) (r : ℕ) (hr : r ≤ (Ideal.span (V : Set R)).height) :
    ∃ s : Finset R, (∀ x ∈ s, x ∈ V) ∧ s.card ≤ r ∧
      r ≤ (Ideal.span (s : Set R)).height := by
  classical
  induction r with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨s, hsV, hsc, hsh⟩ := ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let J : Ideal R := Ideal.span (s : Set R)
    let S := {p : Ideal R | p ∈ J.minimalPrimes ∧ p.height = r}
    have hS : S.Finite := J.finite_minimalPrimes_of_isNoetherianRing.subset (fun _ h => h.1)
    have : Finite S := hS.to_subtype
    have hp (p : S) : ¬ Ideal.span (V : Set R) ≤ p.1 := by
      intro hVp
      have h := hr.trans (Ideal.height_mono hVp)
      rw [p.2.2] at h
      exact (Nat.not_succ_le_self r) (by exact_mod_cast h)
    obtain ⟨x, hxV, hxp⟩ := exists_mem_submodule_notMem_ideals V (fun p : S => p.1) hp
    have hspan : Ideal.span ((insert x s : Finset R) : Set R) = J ⊔ Ideal.span {x} := by
      rw [Finset.coe_insert, Ideal.span_insert]
      exact sup_comm _ _
    refine ⟨insert x s, ?_, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hsc 1), ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxV
      · exact hsV y hy
    · rw [hspan, Ideal.height_eq_inf_minimalPrimes]
      refine le_iInf₂ fun p hp => ?_
      have : p.IsPrime := hp.isPrime
      have hJp : J ≤ p := le_sup_left.trans hp.le
      have hle : (r : ℕ∞) ≤ p.height := hsh.trans (Ideal.height_mono hJp)
      by_cases htop : p.height = ⊤
      · exact htop ▸ le_top
      have : p.FiniteHeight := ⟨Or.inr htop⟩
      have hne : (r : ℕ∞) ≠ p.height := by
        intro heq
        have hpS : p ∈ S := ⟨Ideal.mem_minimalPrimes_of_height_le hJp (heq.symm.trans_le hsh),
          heq.symm⟩
        exact hxp ⟨p, hpS⟩ (hp.le <| Ideal.mem_sup_right <| Ideal.mem_span_singleton_self x)
      exact Order.add_one_le_of_lt (lt_of_le_of_ne hle hne)

theorem exists_parameters_in_submodule [IsNoetherianRing R] [IsLocalRing R]
    (V : Submodule K R) (h : ℕ)
    (hV : (Ideal.span (V : Set R)).radical = IsLocalRing.maximalIdeal R)
    (hdim : (IsLocalRing.maximalIdeal R).height = h) :
    ∃ s : Finset R, (∀ x ∈ s, x ∈ V) ∧ s.card = h ∧
      (Ideal.span (s : Set R)).radical = IsLocalRing.maximalIdeal R := by
  have hheight : (Ideal.span (V : Set R)).height = h := by
    rw [Ideal.height_eq_inf_minimalPrimes,
      ← (Ideal.span (V : Set R)).radical_minimalPrimes, hV,
      ← Ideal.height_eq_inf_minimalPrimes, hdim]
  obtain ⟨s, hsV, hsc, hsh⟩ := exists_finset_mem_submodule_height V h hheight.ge
  have hsm : Ideal.span (s : Set R) ≤ IsLocalRing.maximalIdeal R := by
    refine (Ideal.span_le.mpr fun x hx => ?_)
    rw [← hV]
    exact Ideal.le_radical (Ideal.subset_span (hsV x hx))
  have hsproper : Ideal.span (s : Set R) ≠ ⊤ := by
    intro ht
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (ht ▸ hsm))
  have hspan : (Ideal.span (s : Set R)).spanFinrank ≤ s.card := by
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (M := R) s.finite_toSet
    simpa [Set.ncard_coe_finset] using this
  have hh : (Ideal.span (s : Set R)).height ≤ (s.card : ℕ∞) :=
    (Ideal.height_le_spanFinrank _ hsproper).trans (by exact_mod_cast hspan)
  have hcard : s.card = h := le_antisymm hsc (by exact_mod_cast hsh.trans hh)
  refine ⟨s, hsV, hcard, le_antisymm ?_ ?_⟩
  · exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr hsm
  · rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun p hp => ?_
    have : p.IsPrime := hp.isPrime
    have hpheight : (IsLocalRing.maximalIdeal R).height ≤ p.height := by
      rw [hdim]
      exact hsh.trans (Ideal.height_mono hp.le)
    exact (Ideal.eq_of_le_of_height_le p
      (IsLocalRing.le_maximalIdeal hp.isPrime.ne_top) hpheight).ge

theorem exists_polynomial_parameters [IsNoetherianRing R] [IsLocalRing R]
    {σ : Type*} (φ : MvPolynomial σ K →ₐ[K] R) (S : Set (MvPolynomial σ K))
    (d h : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d)
    (hI : (Ideal.span (φ '' S)).radical = IsLocalRing.maximalIdeal R)
    (hdim : (IsLocalRing.maximalIdeal R).height = h) :
    ∃ g : Fin h → MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (φ ∘ g)) ≤ Ideal.span (φ '' S) ∧
      (Ideal.span (Set.range (φ ∘ g))).radical = IsLocalRing.maximalIdeal R := by
  let U : Submodule K (MvPolynomial σ K) := Submodule.span K S
  let V : Submodule K R := U.map φ.toLinearMap
  have hV : (Ideal.span (V : Set R)).radical = IsLocalRing.maximalIdeal R := by
    change (Ideal.span ((Submodule.span K S).map φ.toLinearMap : Set R)).radical = _
    rw [Submodule.map_span]
    change Ideal.radical (Submodule.span R (Submodule.span K (φ '' S) : Set R)) = _
    rw [Submodule.span_span_of_tower]
    exact hI
  obtain ⟨s, hsV, hsc, hsrad⟩ := exists_parameters_in_submodule V h hV hdim
  have hlift (x : s) : ∃ f ∈ U, φ f = (x : R) := Submodule.mem_map.mp (hsV x x.property)
  choose f hfU hf using hlift
  let e : s ≃ Fin h := Finset.equivFinOfCardEq hsc
  let g (i : Fin h) := f (e.symm i)
  have hg (i : Fin h) : g i ∈ U := hfU (e.symm i)
  have hgr : Set.range (φ ∘ g) = (s : Set R) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      simpa only [Function.comp_apply, g, hf, Finset.mem_coe] using (e.symm i).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simpa only [Function.comp_apply, g, e.symm_apply_apply] using hf ⟨x, hx⟩
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro i
    apply (MvPolynomial.mem_restrictTotalDegree σ d (g i)).mp
    exact (Submodule.span_le.mpr fun f hf =>
      (MvPolynomial.mem_restrictTotalDegree σ d f).mpr (hS f hf)) (hg i)
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.span_subset_span K R _
      (Submodule.apply_mem_span_image_of_mem_span φ.toLinearMap (hg i))
  · rw [hgr]
    exact hsrad

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

theorem polynomial_parameters_at_generic_point {K σ A : Type*}
    [Field K] [Infinite K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] [IsLocalization.AtPrime A p]
    (S : Set (MvPolynomial σ K)) (hp : p ∈ (Ideal.span S).minimalPrimes)
    (d : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i))) ≤
        (Ideal.span S).map (algebraMap (MvPolynomial σ K) A) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A := by
  have : IsRegularLocalRing A := IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).toRingEquiv
  let φ : MvPolynomial σ K →ₐ[K] A := IsScalarTower.toAlgHom K (MvPolynomial σ K) A
  have hrad : (Ideal.span (φ '' S)).radical = IsLocalRing.maximalIdeal A := by
    change (Ideal.span ((algebraMap (MvPolynomial σ K) A) '' S)).radical = _
    rw [← Ideal.map_span,
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A p (Ideal.span S) hp,
      IsLocalization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨g, hg, hdeg, hle, hrad⟩ := exists_polynomial_parameters φ S d _ hS hrad
    (regular_local_maximal_height (R := A))
  refine ⟨g, hg, hdeg, ?_, hrad⟩
  rw [Ideal.map_span]
  exact hle



theorem polynomial_parameters_at_localized_generic_point {K σ A : Type*}
    [Field K] [Infinite K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
    (M : Submonoid (MvPolynomial σ K)) [Algebra (Localization M) A]
    [IsScalarTower (MvPolynomial σ K) (Localization M) A]
    (p : Ideal (Localization M)) [p.IsPrime] [IsLocalization.AtPrime A p]
    (S : Set (MvPolynomial σ K))
    (hp : p ∈ ((Ideal.span S).map (algebraMap (MvPolynomial σ K) (Localization M))).minimalPrimes)
    (d : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i))) ≤
        (Ideal.span S).map (algebraMap (MvPolynomial σ K) A) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A := by
  have : IsLocalization.AtPrime A (p.comap (algebraMap (MvPolynomial σ K) (Localization M))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M A p
  rw [IsLocalization.minimalPrimes_map M (Localization M) (Ideal.span S)] at hp
  exact polynomial_parameters_at_generic_point
    (p.comap (algebraMap (MvPolynomial σ K) (Localization M))) S hp d hS



theorem quotient_length_antitone {R : Type*} [CommRing R]
    {I J : Ideal R} (hIJ : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  exact Module.length_le_of_surjective (Ideal.Quotient.factorₐ R hIJ).toLinearMap
    (Ideal.Quotient.factor_surjective hIJ)

theorem local_quotient_artinian_of_radical {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (J : Ideal R)
    (hJ : J.radical = IsLocalRing.maximalIdeal R) : IsArtinianRing (R ⧸ J) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rw [← J.radical_minimalPrimes, hJ, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

theorem local_quotient_length_ne_top_of_radical {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (J : Ideal R)
    (hJ : J.radical = IsLocalRing.maximalIdeal R) :
    Module.length R (R ⧸ J) ≠ ⊤ := by
  have := local_quotient_artinian_of_radical J hJ
  have : IsArtinian R (R ⧸ J) :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ J) Ideal.Quotient.mk_surjective
  exact Module.length_ne_top



theorem polynomial_parameters_with_finite_length {K σ A : Type*}
    [Field K] [Infinite K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
    (M : Submonoid (MvPolynomial σ K)) [Algebra (Localization M) A]
    [IsScalarTower (MvPolynomial σ K) (Localization M) A]
    (p : Ideal (Localization M)) [p.IsPrime] [IsLocalization.AtPrime A p]
    (S : Set (MvPolynomial σ K))
    (hp : p ∈ ((Ideal.span S).map (algebraMap (MvPolynomial σ K) (Localization M))).minimalPrimes)
    (d : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i))) ≤
        (Ideal.span S).map (algebraMap (MvPolynomial σ K) A) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (Ideal.span S).map (algebraMap (MvPolynomial σ K) A)) ≤
        Module.length A (A ⧸ Ideal.span
          (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))) ∧
      Module.length A (A ⧸ Ideal.span
        (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))) ≠ ⊤ := by
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  obtain ⟨g, hg, hd, hle, hrad⟩ :=
    polynomial_parameters_at_localized_generic_point (A := A) M p S hp d hS
  exact ⟨g, hg, hd, hle, hrad, quotient_length_antitone hle,
    local_quotient_length_ne_top_of_radical _ hrad⟩

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem support_invariantJet_subset (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) : (invariantJet c a f).support ⊆ f.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_invariantJet] at hm
  exact MvPolynomial.mem_support_iff.mpr (fun h ↦ hm (by rw [h, mul_zero]))

theorem totalDegree_invariantJet_le (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) : (invariantJet c a f).totalDegree ≤ f.totalDegree :=
  MvPolynomial.totalDegree_le_of_support_subset (support_invariantJet_subset c a f)

end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialBox
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
namespace WeightedTorusJets.Geometry

theorem totalDegree_lt_of_mem_polynomialBox {K : Type*} [Field K] {N : ℕ}
    (hN : 0 < N) {F : MvPolynomial (Fin 4) K} (hF : F ∈ polynomialBox K N) :
    F.totalDegree < 4 * N := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨n, rfl⟩ := hF
      change (MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm fun i => (n i : ℕ)) (1 : K)).totalDegree < _
      rw [MvPolynomial.totalDegree_monomial _ one_ne_zero, Finsupp.sum_fintype]
      · simpa using Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
          Finset.univ_nonempty (fun i _ ↦ (n i).isLt)
      · simp
  | zero => simp [Nat.mul_pos (by decide : 0 < 4) hN]
  | add F G _ _ hF hG =>
      exact (MvPolynomial.totalDegree_add F G).trans_lt (max_lt hF hG)
  | smul a F _ hF => exact (MvPolynomial.totalDegree_smul_le a F).trans_lt hF



theorem rectangleJetIdeal_map {ι R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (jet : (ι → ℕ) → R) (t : ι → ℕ) (b : ℕ) :
    (rectangleJetIdeal jet t b).map f = rectangleJetIdeal (fun a => f (jet a)) t b := by
  simp only [rectangleJetIdeal, Ideal.map_span, Set.image_image]

theorem polynomial_prime_height_eq_cotangent_finrank
    {K σ A : Type*} [Field K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra (MvPolynomial σ K) A]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] [IsLocalization.AtPrime A p] :
    p.height = (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.CotangentSpace A) : ℕ∞) := by
  have : IsRegularLocalRing A := IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).toRingEquiv
  apply WithBot.coe_injective
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p A,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, regular_local_maximal_height]

theorem rectangleJetIdeal_exists_parameters_with_length
    {K A : Type*} [Field K] [Infinite K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial (Fin 4) K) A]
    [IsScalarTower K (MvPolynomial (Fin 4) K) A]
    [Algebra (Localization (Submonoid.powers
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) A]
    [IsScalarTower (MvPolynomial (Fin 4) K)
      (Localization (Submonoid.powers
        (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) A]
    (p : Ideal (Localization (Submonoid.powers
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))))
    [p.IsPrime] [IsLocalization.AtPrime A p]
    (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : MvPolynomial (Fin 4) K}
    (hF : F ∈ polynomialBox K N)
    (hp : p ∈ (rectangleJetIdeal
      (fun a => algebraMap _ _ (invariantJet c a F)) t b).minimalPrimes) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial (Fin 4) K,
      (∀ i, g i ∈ Submodule.span K
        ((fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j})) ∧
      (∀ i, (g i).totalDegree ≤ 4 * N) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (rectangleJetIdeal
        (fun a => algebraMap (MvPolynomial (Fin 4) K)
          (Localization (Submonoid.powers
            (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))))
          (invariantJet c a F)) t b).map
          (algebraMap (Localization (Submonoid.powers
            (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) A)) ≤
        Module.length A (A ⧸ Ideal.span
          (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K) A (g i)))) ∧
      Module.length A (A ⧸ Ideal.span
        (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K) A (g i)))) ≠ ⊤ := by
  let M := Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))
  let S := (fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j}
  have hS : ∀ f ∈ S, f.totalDegree ≤ 4 * N := by
    rintro f ⟨a, _, rfl⟩
    exact (totalDegree_invariantJet_le c a F).trans
      (totalDegree_lt_of_mem_polynomialBox hN hF).le
  have hp' : p ∈ ((Ideal.span S).map
      (algebraMap (MvPolynomial (Fin 4) K) (Localization M))).minimalPrimes := by
    change p ∈ ((rectangleJetIdeal (fun a => invariantJet c a F) t b).map _).minimalPrimes
    rwa [rectangleJetIdeal_map]
  obtain ⟨g, hg, hd, _, hrad, hle, hfin⟩ :=
    polynomial_parameters_with_finite_length (A := A) M p S hp' (4 * N) hS
  have hlocal : (Ideal.span S).map (algebraMap (MvPolynomial (Fin 4) K) A) =
      (rectangleJetIdeal (fun a => algebraMap (MvPolynomial (Fin 4) K) (Localization M)
        (invariantJet c a F)) t b).map (algebraMap (Localization M) A) := by
    change (rectangleJetIdeal (fun a => invariantJet c a F) t b).map _ = _
    rw [rectangleJetIdeal_map, rectangleJetIdeal_map]
    simp only [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 4) K) (Localization M) A]
  refine ⟨g, hg, hd, hrad, ?_, hfin⟩
  rw [← (Ideal.quotientEquivAlgOfEq A hlocal).toLinearEquiv.length_eq]
  exact hle


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem adjoin_fractionField_coordinates
    {K R L ι : Type*} [Field K] [CommRing R] [Field L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L]
    [IsFractionRing R L] (x : ι → R)
    (hgen : Algebra.adjoin K (Set.range x) = ⊤) :
    IntermediateField.adjoin K (Set.range (fun i => algebraMap R L (x i))) = ⊤ := by
  let E := IntermediateField.adjoin K (Set.range (fun i => algebraMap R L (x i)))
  have hR : (IsScalarTower.toAlgHom K R L).range ≤ E.toSubalgebra := by
    rw [← Algebra.map_top, ← hgen, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨r, ⟨i, rfl⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  apply top_le_iff.mp
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R z
  exact E.div_mem (hR ⟨a, rfl⟩) (hR ⟨b, rfl⟩)

theorem adjoin_quotient_coordinates
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) :
    Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  have h : MvPolynomial.aeval (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) =
      Ideal.Quotient.mkₐ K I := by
    ext i
    simp
  rw [h]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective K I)

theorem exists_coordinate_transcendence_basis
    {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (x : ι → L) (hgen : IntermediateField.adjoin K (Set.range x) = ⊤) :
    ∃ s : Set ι, IsTranscendenceBasis K (fun i : s => x i) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, hgen,
      Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  obtain ⟨t, htr, ht⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range x)
  obtain ⟨s, rfl, hxs⟩ := Set.exists_image_eq_injOn_of_subset_range htr
  exact ⟨s, (isTranscendenceBasis_image hxs).mpr ht⟩

theorem exists_prime_quotient_coordinate_basis
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ∃ s : Set σ, IsTranscendenceBasis K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i))) := by
  exact exists_coordinate_transcendence_basis
    (K := K) (L := FractionRing (MvPolynomial σ K ⧸ p))
    (fun i : σ => algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
      (Ideal.Quotient.mk p (MvPolynomial.X i)))
    (adjoin_fractionField_coordinates
      (K := K) (R := MvPolynomial σ K ⧸ p) (L := FractionRing (MvPolynomial σ K ⧸ p))
      (fun i : σ => Ideal.Quotient.mk p (MvPolynomial.X i)) (adjoin_quotient_coordinates p))



attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_localization_prime_height
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime ∧
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).height = p.height := by
  let M : Submonoid (MvPolynomial σ B) :=
    (nonZeroDivisors B).map MvPolynomial.C
  have hM := coefficient_nonZeroDivisors_disjoint p hp
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial σ F) p inferInstance hM,
    IsLocalization.height_map_of_disjoint M p hM⟩

theorem coordinateFractionAlgebra_algebraMap
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : AlgebraicIndependent K x) (b : MvPolynomial σ K) :
    letI := coordinateFractionAlgebra hx
    algebraMap (FractionRing (MvPolynomial σ K)) L
      (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) b) =
        MvPolynomial.aeval x b := by
  exact IsFractionRing.lift_algebraMap
    (algebraicIndependent_iff_injective_aeval.2 hx) b

theorem transcendenceBasis_isAlgebraic_coordinateFraction
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : IsTranscendenceBasis K x) :
    letI := coordinateFractionAlgebra hx.1
    Algebra.IsAlgebraic (FractionRing (MvPolynomial σ K)) L := by
  let := coordinateFractionAlgebra hx.1
  have := hx.isAlgebraic_field
  apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq
    hx.1.aevalEquivField.toRingHom (RingHom.id L)
    hx.1.aevalEquivField.surjective Function.injective_id
  rfl

theorem coordinateFraction_aeval_comp_map
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : AlgebraicIndependent K x) (y : τ → L) :
    letI := coordinateFractionAlgebra hx
    (MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y).toRingHom.comp
        (MvPolynomial.map (algebraMap (MvPolynomial σ K)
          (FractionRing (MvPolynomial σ K)))) =
      MvPolynomial.eval₂Hom (MvPolynomial.aeval x).toRingHom y := by
  let := coordinateFractionAlgebra hx
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
    change MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y
      (MvPolynomial.C (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) b)) =
        MvPolynomial.aeval x b
    rw [MvPolynomial.aeval_C]
    exact coordinateFractionAlgebra_algebraMap hx b
  · intro i
    simp

theorem coordinateFraction_kernel_isMaximal
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : IsTranscendenceBasis K x) (y : τ → L) :
    letI := coordinateFractionAlgebra hx.1
    ((RingHom.ker (MvPolynomial.eval₂Hom (MvPolynomial.aeval x).toRingHom y)).map
      (algebraMap (MvPolynomial τ (MvPolynomial σ K))
        (MvPolynomial τ (FractionRing (MvPolynomial σ K))))).IsMaximal := by
  let := coordinateFractionAlgebra hx.1
  have := transcendenceBasis_isAlgebraic_coordinateFraction hx
  apply coefficient_localization_isMaximal _
    (MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y)
  change RingHom.ker ((MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y).toRingHom.comp
    (algebraMap (MvPolynomial τ (MvPolynomial σ K))
      (MvPolynomial τ (FractionRing (MvPolynomial σ K))))) = _
  rw [MvPolynomial.algebraMap_def, coordinateFraction_aeval_comp_map hx.1 y]

end WeightedTorusJets.Geometry

open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets.Geometry

theorem aeval_coordinateSplit_symm
    {K A σ : Type*} [CommSemiring K] [CommSemiring A] [Algebra K A]
    (s : Set σ) (x : σ → A) (q : MvPolynomial (sᶜ : Set σ) (MvPolynomial s K)) :
    aeval x ((coordinateSplit s).symm q) =
      eval₂ (aeval (R := K) (fun i : s => x i)).toRingHom (fun i : (sᶜ : Set σ) => x i) q := by
  have he : (aeval (R := K) x).toRingHom.comp (coordinateSplit s).symm.toRingHom =
      eval₂Hom (aeval (R := K) (fun i : s => x i)).toRingHom (fun i : (sᶜ : Set σ) => x i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coordinateSplit_symm_C, aeval_rename, Function.comp_def]
    · intro i
      simp
  exact congrArg (fun f : MvPolynomial (sᶜ : Set σ) (MvPolynomial s K) →+* A => f q) he

theorem totalDegree_coordinateSplit_le
    {K σ : Type*} [CommSemiring K] (s : Set σ) (p : MvPolynomial σ K) :
    (coordinateSplit s p).totalDegree ≤ p.totalDegree := by
  classical
  let φ := (coordinateSplit (K := K) s).toRingHom
  have hX : ∀ i : σ, (φ (X i)).totalDegree ≤ 1 := by
    intro i
    by_cases hi : i ∈ s
    · change (coordinateSplit s (X (⟨i, hi⟩ : s))).totalDegree ≤ 1
      rw [coordinateSplit_X_mem s ⟨i, hi⟩]
      simp
    · change (coordinateSplit s (X (⟨i, hi⟩ : (sᶜ : Set σ)))).totalDegree ≤ 1
      rw [coordinateSplit_X_compl s ⟨i, hi⟩]
      cases subsingleton_or_nontrivial K
      · simp [Subsingleton.elim (X (⟨i, hi⟩ : (sᶜ : Set σ)) : MvPolynomial (sᶜ : Set σ) (MvPolynomial s K)) 0]
      · simp
  change (φ p).totalDegree ≤ p.totalDegree
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  apply le_trans _ (le_totalDegree hd)
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
  calc
    _ ≤ (φ (C (p.coeff d))).totalDegree +
        (∑ i ∈ d.support, (φ (X i ^ d i)).totalDegree) :=
      (totalDegree_mul _ _).trans
        (Nat.add_le_add_left (totalDegree_finsetProd _ _) _)
    _ = ∑ i ∈ d.support, ((φ (X i)) ^ d i).totalDegree := by simp [φ]
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hX i))
    _ = d.sum (fun _ e => e) := rfl

theorem totalDegree_localized_coordinateSplit_le
    {K σ : Type*} [Field K] (s : Set σ) (p : MvPolynomial σ K) :
    (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
      (coordinateSplit s p)).totalDegree ≤ p.totalDegree := by
  exact (Finset.sup_mono (support_map_subset _ _)).trans (totalDegree_coordinateSplit_le s p)




theorem aeval_componentCoordinate {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) :
    MvPolynomial.aeval (componentCoordinate p) =
      (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p)
        (FractionRing (MvPolynomial σ K ⧸ p))).comp (Ideal.Quotient.mkₐ K p) := by
  ext i
  simp [componentCoordinate]

theorem ker_aeval_componentCoordinate {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) :
    RingHom.ker (MvPolynomial.aeval (componentCoordinate p)).toRingHom = p := by
  rw [aeval_componentCoordinate]
  ext q
  change algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
    (Ideal.Quotient.mk p q) = 0 ↔ q ∈ p
  rw [map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K ⧸ p)
    (FractionRing (MvPolynomial σ K ⧸ p))), Ideal.Quotient.eq_zero_iff_mem]

theorem coordinateSplit_prime_eq_evaluation_kernel {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) :
    p.comap (coordinateSplit s).symm.toRingHom =
      RingHom.ker (MvPolynomial.eval₂Hom
        (MvPolynomial.aeval (R := K) (fun i : s => componentCoordinate p i)).toRingHom
        (fun i : (sᶜ : Set σ) => componentCoordinate p i)) := by
  conv_lhs => rw [← ker_aeval_componentCoordinate p]
  rw [RingHom.comap_ker]
  congr 1
  apply RingHom.ext
  intro q
  exact aeval_coordinateSplit_symm s (componentCoordinate p) q

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coordinateSplit_localized_prime_isMaximal {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hs : IsTranscendenceBasis K (fun i : s => componentCoordinate p i)) :
    ((p.comap (coordinateSplit s).symm.toRingHom).map
      (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))).IsMaximal := by
  rw [coordinateSplit_prime_eq_evaluation_kernel]
  exact coordinateFraction_kernel_isMaximal hs
    (fun i : (sᶜ : Set σ) => componentCoordinate p i)

end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CoordinateLocalizedPrime
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace WeightedTorusJets.Geometry

open scoped AlgebraMonoidAlgebra

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coordinateLocalizedPrime_height {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) :
    (coordinateLocalizedPrime s p).height = p.height := by
  exact (coefficient_localization_prime_height (F := FractionRing (MvPolynomial s K))
    (p.comap (coordinateSplit (K := K) s).symm.toRingHom)
    (coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs)).2.trans
    ((coordinateSplit (K := K) s).symm.toRingEquiv.height_comap p)

theorem coordinateFraction_localEquiv_algebraMap {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    [(coordinateLocalizedPrime s p).IsPrime]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) (f : MvPolynomial σ K) :
    coordinateFractionLocalEquiv s p hs (algebraMap _ (Localization.AtPrime p) f) =
      algebraMap _ (Localization.AtPrime (coordinateLocalizedPrime s p))
        (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
          (coordinateSplit s f)) := by
  have : ((p.comap (coordinateSplit (K := K) s).symm.toRingHom).map
      (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))).IsPrime :=
    ‹(coordinateLocalizedPrime s p).IsPrime›
  have hsplit : coordinateSplitLocalEquiv s p (algebraMap _ (Localization.AtPrime p) f) =
      algebraMap _ (Localization.AtPrime (p.comap (coordinateSplit (K := K) s).symm.toRingHom))
        (coordinateSplit s f) := by
    apply (coordinateSplitLocalEquiv s p).symm.injective
    rw [AlgEquiv.symm_apply_apply]
    change algebraMap _ (Localization.AtPrime p) f =
      Localization.localRingHom _ p (coordinateSplit (K := K) s).symm.toRingHom rfl
        (algebraMap _ _ (coordinateSplit s f))
    rw [Localization.localRingHom_to_map]
    change algebraMap _ (Localization.AtPrime p) f =
      algebraMap _ (Localization.AtPrime p) ((coordinateSplit s).symm (coordinateSplit s f))
    rw [AlgEquiv.symm_apply_apply]
  change (coefficientLocalizationLocalEquiv
      (F := FractionRing (MvPolynomial s K))
      (p.comap (coordinateSplit (K := K) s).symm.toRingHom)
      (coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs))
    (coordinateSplitLocalEquiv s p (algebraMap _ (Localization.AtPrime p) f)) = _
  rw [hsplit, AlgEquiv.commutes]
  rfl

theorem coordinateLocalizedPrime_finite_quotient {K σ : Type*} [Field K] [Finite σ]
    (s : Set σ) (p : Ideal (MvPolynomial σ K))
    [(coordinateLocalizedPrime s p).IsMaximal] :
    Module.Finite (FractionRing (MvPolynomial s K))
      (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K)) ⧸
        coordinateLocalizedPrime s p) := by
  let := Ideal.Quotient.field (coordinateLocalizedPrime s p)
  exact finite_of_finite_type_of_isJacobsonRing _ _

theorem coordinate_complement_card_eq_height {K σ : Type*} [Field K] [Finite σ]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    [(coordinateLocalizedPrime s p).IsMaximal]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) :
    (Nat.card (sᶜ : Set σ) : ℕ∞) = p.height := by
  let := Fintype.ofFinite (sᶜ : Set σ)
  rw [← coordinateLocalizedPrime_height s p hs, maximal_mvPolynomial_height]
  simp only [Nat.card_eq_fintype_card]

theorem exists_coordinate_localization {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ∃ (s : Set σ)
      (_hs : IsTranscendenceBasis K (fun i : s => componentCoordinate p i))
      (hq : (coordinateLocalizedPrime s p).IsMaximal),
      letI := hq
      Module.Finite (FractionRing (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K)) ⧸
          coordinateLocalizedPrime s p) ∧
      (Nat.card (sᶜ : Set σ) : ℕ∞) = p.height ∧
      ∃ e : Localization.AtPrime p ≃ₐ[K] Localization.AtPrime (coordinateLocalizedPrime s p),
        ∀ f : MvPolynomial σ K,
          e (algebraMap _ (Localization.AtPrime p) f) =
            algebraMap _ (Localization.AtPrime (coordinateLocalizedPrime s p))
              (MvPolynomial.map
                (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
                (coordinateSplit s f)) ∧
          (MvPolynomial.map
            (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
            (coordinateSplit s f)).totalDegree ≤ f.totalDegree := by
  obtain ⟨s, hs⟩ := exists_prime_quotient_coordinate_basis p
  have hq : (coordinateLocalizedPrime s p).IsMaximal :=
    coordinateSplit_localized_prime_isMaximal s p hs
  refine ⟨s, hs, hq, coordinateLocalizedPrime_finite_quotient s p,
    coordinate_complement_card_eq_height s p hs.1, coordinateFractionLocalEquiv s p hs.1, ?_⟩
  intro f
  exact ⟨coordinateFraction_localEquiv_algebraMap s p hs.1 f,
    totalDegree_localized_coordinateSplit_le s f⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

theorem ring_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let f : A ≃ₗ[A] B :=
    { e.toAddEquiv with map_smul' := by intro a b; exact e.map_mul a b }
  rw [← Module.length_eq_of_surjective (M := B) e.surjective]
  exact f.length_eq

theorem quotient_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map e.toRingHom) :
    Module.length A (A ⧸ I) = Module.length B (B ⧸ J) := by
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ I) (M := A ⧸ I)
      (Ideal.Quotient.mk_surjective (I := I)),
    Module.length_eq_of_surjective (S := B) (R := B ⧸ J) (M := B ⧸ J)
      (Ideal.Quotient.mk_surjective (I := J))]
  exact ring_length_eq_of_ringEquiv (Ideal.quotientEquiv I J e hJ)

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry

theorem radical_map_ringEquiv_eq_maximalIdeal
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (I : Ideal A)
    (hI : I.radical = IsLocalRing.maximalIdeal A) :
    (I.map e.toRingHom).radical = IsLocalRing.maximalIdeal B := by
  have hk : RingHom.ker e.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
  rw [← Ideal.map_radical_of_surjective e.surjective
    (hk ▸ bot_le), hI]
  exact IsLocalRing.map_ringEquiv_maximalIdeal e

theorem map_span_range_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B]
    (e : A →+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i) :
    (Ideal.span (Set.range f)).map e = Ideal.span (Set.range g) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext h)

theorem quotient_length_eq_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i) :
    Module.length A (A ⧸ Ideal.span (Set.range f)) =
      Module.length B (B ⧸ Ideal.span (Set.range g)) := by
  exact DegreeBezout.quotient_length_eq_of_ringEquiv e _ _
    (map_span_range_of_commuting_images e.toRingHom f g h).symm

theorem radical_span_eq_maximalIdeal_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i)
    (hf : (Ideal.span (Set.range f)).radical = IsLocalRing.maximalIdeal A) :
    (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal B := by
  rw [← map_span_range_of_commuting_images e.toRingHom f g h]
  exact radical_map_ringEquiv_eq_maximalIdeal e _ hf



universe u v w

end WeightedTorusJets.Geometry

end
end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LinearShearHom
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section
namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {K σ τ : Type*} [CommSemiring K]
    (v : σ → MvPolynomial τ K) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (f : MvPolynomial σ K) : (MvPolynomial.aeval v f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  have hmul := totalDegree_mul (C (f.coeff d)) (d.prod fun i k => v i ^ k)
  simp only [totalDegree_C, zero_add] at hmul
  apply hmul.trans
  refine (totalDegree_finsetProd d.support (fun i => v i ^ d i)).trans ?_
  apply le_trans _ (le_totalDegree hd)
  apply Finset.sum_le_sum
  intro i _
  simpa only [Nat.mul_one] using
    (totalDegree_pow (v i) (d i)).trans (Nat.mul_le_mul_left (d i) (hv i))

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.LinearNormalization

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

theorem totalDegree_linearShear_le (c : Fin n → K) (f : MvPolynomial (Fin (n + 1)) K) :
    (linearShear c f).totalDegree ≤ f.totalDegree := by
  change (linearShearHom c f).totalDegree ≤ f.totalDegree
  apply WeightedTorusJets.Geometry.totalDegree_aeval_le_of_linear
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [Fin.cases_succ]
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    apply (totalDegree_mul _ _).trans
    simp

@[simp] theorem totalDegree_linearShear (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    (linearShear c f).totalDegree = f.totalDegree := by
  apply le_antisymm (totalDegree_linearShear_le c f)
  have h := totalDegree_linearShear_le (-c) (linearShear c f)
  have hc : linearShear (-c) (linearShear c f) = f := by
    exact congrArg (fun h : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K => h f)
      (by simpa using linearShearHom_comp_neg (-c))
  simpa only [hc] using h

theorem isHomogeneous_linearShear (c : Fin n → K)
    {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (linearShear c f).IsHomogeneous d := by
  change (linearShearHom c f).IsHomogeneous d
  have hvars : ∀ i : Fin (n + 1),
      (Fin.cases (X 0 : MvPolynomial (Fin (n + 1)) K)
        (fun j => X j.succ + C (c j) * X 0) i : MvPolynomial (Fin (n + 1)) K).IsHomogeneous 1 := by
    intro i
    cases i using Fin.cases with
    | zero => exact isHomogeneous_X K 0
    | succ i => exact (isHomogeneous_X K i.succ).add (isHomogeneous_C_mul_X _ _)
  simpa only [linearShearHom, one_mul] using hf.aeval _ hvars

theorem eval_mul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (a : K) (r : σ → K) :
    eval (fun i => a * r i) f = a ^ d * eval r f := by
  classical
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial e b he =>
    rw [eval_monomial, eval_monomial]
    simp_rw [mul_pow, Finsupp.prod_mul]
    have he' : e.sum (fun _ k => k) = d := by
      simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using he
    have hp : e.prod (fun _ k => a ^ k) = a ^ d := by
      simpa only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum] using congrArg (fun k => a ^ k) he'
    rw [hp]
    ring

theorem exists_eval_cons_one_ne_zero [Infinite K]
    {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) f ≠ 0 := by
  have hxf : (X 0 : MvPolynomial (Fin (n + 1)) K) * f ≠ 0 :=
    mul_ne_zero (X_ne_zero _) hf0
  obtain ⟨r, hr⟩ : ∃ r : Fin (n + 1) → K, eval r (X 0 * f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hxf (((isHomogeneous_X K 0).mul hf).eq_zero_of_forall_eval_eq_zero h)
  have hrs : r 0 ≠ 0 ∧ eval r f ≠ 0 := by
    simpa only [map_mul, eval_X, mul_ne_zero_iff] using hr
  have hr0 := hrs.1
  have hrf := hrs.2
  refine ⟨fun i => (r 0)⁻¹ * r i.succ, ?_⟩
  have hc : Fin.cons 1 (fun i => (r 0)⁻¹ * r i.succ) =
      fun i => (r 0)⁻¹ * r i := by
    funext i
    cases i using Fin.cases <;> simp [hr0]
  rw [hc, eval_mul_of_isHomogeneous hf]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hr0)) hrf

theorem homogeneousComponent_linearShear (c : Fin n → K)
    (d : ℕ) (f : MvPolynomial (Fin (n + 1)) K) :
    homogeneousComponent d (linearShear c f) =
      linearShear c (homogeneousComponent d f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial e b =>
    rw [homogeneousComponent_of_mem
      (isHomogeneous_linearShear c (isHomogeneous_monomial b rfl)),
      homogeneousComponent_of_mem (isHomogeneous_monomial b rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, hp, hq]

theorem eval_cons_one_zero_of_isHomogeneous
    {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    eval (Fin.cons 1 0) f =
      constantCoeff ((finSuccEquiv K n f).coeff d) := by
  have hdeg : (finSuccEquiv K n f).natDegree < d + 1 := by
    have ht := hf.totalDegree_le
    have h := degreeOf_le_totalDegree f 0
    rw [← natDegree_finSuccEquiv f] at h
    omega
  have aux : ∀ i ∈ Finset.range d,
      constantCoeff ((finSuccEquiv K n f).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hf.finSuccEquiv_coeff_isHomogeneous i (d - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    omega
  simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map,
    Polynomial.eval_eq_sum_range' hdeg, eval_zero, one_pow, mul_one, map_sum,
    Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]

theorem eval_cons_one_zero_linearShear (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    eval (Fin.cons 1 0) (linearShear c f) = eval (Fin.cons 1 c) f := by
  have h : (eval (Fin.cons 1 0)).comp (linearShearHom c).toRingHom =
      eval (Fin.cons 1 c) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [linearShearHom]
    · intro i
      cases i using Fin.cases <;> simp [linearShearHom]
  exact congrArg (fun g : MvPolynomial (Fin (n + 1)) K →+* K => g f) h

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal _root_.Polynomial RingHom
variable {K : Type*} [Field K] {n : ℕ}

theorem algEquiv_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) : e.toAlgHom.IsIntegral :=
  RingHom.isIntegral_of_surjective e.toAlgHom.toRingHom e.surjective

theorem isUnit_leadingCoeff_finSuccEquiv_of_full_degree
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f ≠ 0)
    (hd : degreeOf 0 f = f.totalDegree) :
    IsUnit (finSuccEquiv K n f).leadingCoeff := by
  have hp : finSuccEquiv K n f ≠ 0 := by
    intro h
    exact hf ((finSuccEquiv K n).injective (by simpa using h))
  have hnd : (finSuccEquiv K n f).natDegree = f.totalDegree := by
    simpa only [natDegree_finSuccEquiv] using hd
  have hl : (finSuccEquiv K n f).coeff f.totalDegree ≠ 0 := by
    rw [← hnd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  have ht := totalDegree_coeff_finSuccEquiv_add_le f f.totalDegree hl
  have hz : ((finSuccEquiv K n f).coeff f.totalDegree).totalDegree = 0 := by omega
  have he := totalDegree_eq_zero_iff_eq_C.mp hz
  have hc : ((finSuccEquiv K n f).coeff f.totalDegree).coeff 0 ≠ 0 := by
    intro hc
    exact hl (by rw [he, hc, map_zero])
  rw [← coeff_natDegree, hnd, he]
  exact hc.isUnit.map MvPolynomial.C

theorem eliminationHom_isIntegral (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f ≠ 0) (hfi : f ∈ I)
    (hd : degreeOf 0 (linearShear c f) = f.totalDegree) :
    (eliminationHom c I).IsIntegral := by
  have hsf : linearShear c f ≠ 0 := by
    intro h
    exact hf ((linearShear c).injective (by simpa using h))
  have hu := isUnit_leadingCoeff_finSuccEquiv_of_full_degree hsf
    (by simpa only [totalDegree_linearShear] using hd)
  have hb : (eliminationBaseHom c I).IsIntegral := by
    exact (monic_of_isUnit_leadingCoeff_inv_smul hu).quotient_isIntegral
      (Submodule.smul_of_tower_mem _ hu.unit⁻¹.val (Ideal.mem_map_of_mem _ hfi))
  have he := algEquiv_isIntegral
    (A := Polynomial (MvPolynomial (Fin n) K) ⧸ eliminationIdeal c I)
    (B := MvPolynomial (Fin (n + 1)) K ⧸ I) (eliminationQuotientEquiv c I)
  exact hb.trans _ _ he

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
variable {K : Type*} [Field K] {n : ℕ}

theorem eliminationHom_apply_raw (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (p : MvPolynomial (Fin n) K) :
    eliminationHom c I p = Ideal.Quotient.mk I
      ((eliminationEquiv c).symm (Polynomial.C p)) := by
  exact eliminationQuotientEquiv_mk c I (Polynomial.C p)

theorem eliminationEquiv_linearShear_neg (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    eliminationEquiv c (linearShear (-c) f) = finSuccEquiv K n f := by
  rw [eliminationEquiv, AlgEquiv.trans_apply, linearShear_apply_neg]

theorem eliminationEquiv_symm_C_X (c : Fin n → K) (i : Fin n) :
    (eliminationEquiv c).symm (Polynomial.C (MvPolynomial.X i)) =
      linearShear (-c) (MvPolynomial.X i.succ) := by
  apply (eliminationEquiv c).symm_apply_eq.mpr
  rw [eliminationEquiv_linearShear_neg, finSuccEquiv_X_succ]

@[simp] theorem eliminationHom_X (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (i : Fin n) :
    eliminationHom c I (MvPolynomial.X i) =
      Ideal.Quotient.mk I (linearShear (-c) (MvPolynomial.X i.succ)) := by
  rw [eliminationHom_apply_raw, eliminationEquiv_symm_C_X]

theorem eliminationHom_apply (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (p : MvPolynomial (Fin n) K) :
    eliminationHom c I p =
      Ideal.Quotient.mk I (linearShear (-c) (MvPolynomial.rename Fin.succ p)) := by
  have h : eliminationHom c I = (Ideal.Quotient.mkₐ K I).comp
      ((linearShear (-c)).toAlgHom.comp (MvPolynomial.rename Fin.succ)) := by
    ext i
    simp only [eliminationHom_X, AlgHom.comp_apply, rename_X,
      AlgEquiv.coe_toAlgHom, Quotient.mkₐ_eq_mk]
  exact congrArg (fun g : MvPolynomial (Fin n) K →ₐ[K]
    MvPolynomial (Fin (n + 1)) K ⧸ I => g p) h

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.Geometry

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_homogeneous_relation_not_dvd_coordinate
    {R σ : Type*} [CommRing R] [IsDomain R]
    (P : Ideal (MvPolynomial σ R)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ R)) (hP0 : P ≠ ⊥)
    (i : σ) (hi : X i ∉ P) :
    ∃ (n : ℕ) (f : MvPolynomial σ R),
      f ≠ 0 ∧ f ∈ P ∧ f.IsHomogeneous n ∧ ¬ X i ∣ f := by
  classical
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hex : ∃ n : ℕ, ∃ f : MvPolynomial σ R,
      f ∈ P ∧ f ≠ 0 ∧ f.totalDegree = n := ⟨a.totalDegree, a, haP, ha0, rfl⟩
  obtain ⟨f, hfP, hf0, hfdeg⟩ := Nat.find_spec hex
  obtain ⟨n, hn, hn0⟩ : ∃ n ∈ Finset.range (f.totalDegree + 1),
      homogeneousComponent n f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf0
    rw [← sum_homogeneousComponent f]
    exact Finset.sum_eq_zero h
  have hnP := homogeneousComponent_mem_of_mem hP hfP n
  have hhom := homogeneousComponent_isHomogeneous n f
  refine ⟨n, homogeneousComponent n f, hn0, hnP, hhom, ?_⟩
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro hzero
    apply hn0
    rw [hg, hzero, mul_zero]
  have hgP : g ∈ P :=
    (Ideal.IsPrime.mem_or_mem inferInstance (hg ▸ hnP)).resolve_left hi
  have hmin := Nat.find_min' hex ⟨g, hgP, hg0, rfl⟩
  have hdeg := congrArg MvPolynomial.totalDegree hg
  rw [hhom.totalDegree hn0, totalDegree_mul_of_isDomain (X_ne_zero i) hg0,
    totalDegree_X] at hdeg
  have hnle : n ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  omega

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem coordinate_dvd_sub_aeval_update_zero
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ R) :
    X i ∣ p - aeval (Function.update (X (R := R)) i 0) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  | mul_X p j hp =>
    by_cases hji : j = i
    · subst j
      simp only [map_mul, aeval_X, Function.update_self, mul_zero, sub_zero]
      exact dvd_mul_left _ _
    · simp only [map_mul, aeval_X, Function.update_of_ne hji]
      rw [← sub_mul]
      exact dvd_mul_of_dvd_left hp _

theorem aeval_update_zero_eq_zero_iff
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ R) :
    aeval (Function.update (X (R := R)) i 0) p = 0 ↔ X i ∣ p := by
  constructor
  · intro h
    simpa only [h, sub_zero] using coordinate_dvd_sub_aeval_update_zero i p
  · rintro ⟨q, rfl⟩
    simp

theorem isHomogeneous_aeval_update_zero
    {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (aeval (Function.update (X (R := R)) i 0) p).IsHomogeneous n := by
  simpa only [one_mul] using hp.aeval (n := 1) (Function.update (X (R := R)) i 0)
    (fun j => by
      by_cases h : j = i
      · subst j
        simpa only [Function.update_self] using isHomogeneous_zero (R := R) (σ := σ) 1
      · simpa only [Function.update_of_ne h] using isHomogeneous_X R j)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial
variable {K : Type*} [Field K] {n : ℕ}

theorem eval_aeval_update_zero {σ : Type*} [DecidableEq σ]
    (i : σ) (r : σ → K) (f : MvPolynomial σ K) :
    eval r (aeval (Function.update (X (R := K)) i 0) f) =
      eval (Function.update r i 0) f := by
  have h : (eval r).comp (aeval (Function.update (X (R := K)) i 0)).toRingHom =
      eval (Function.update r i 0) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp
    · intro j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hji]
  exact congrArg (fun g : MvPolynomial σ K →+* K => g f) h

theorem exists_eval_cons_one_with_zero [Infinite K]
    (j : Fin n) {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hnot : ¬ X j.succ ∣ f) :
    ∃ c : Fin n → K, c j = 0 ∧ eval (Fin.cons 1 c) f ≠ 0 := by
  have hne : aeval (Function.update (X (R := K)) j.succ 0) f ≠ 0 :=
    (WeightedTorusJets.Geometry.aeval_update_zero_eq_zero_iff j.succ f).not.mpr hnot
  obtain ⟨c, hc⟩ := exists_eval_cons_one_ne_zero
    (WeightedTorusJets.Geometry.isHomogeneous_aeval_update_zero j.succ hf) hne
  refine ⟨Function.update c j 0, Function.update_self j 0 c, ?_⟩
  have hvec : Function.update (Fin.cons 1 c : Fin (n + 1) → K) j.succ 0 =
      (Fin.cons 1 (Function.update c j 0) : Fin (n + 1) → K) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
    | succ i => simp [Function.update_apply, Fin.succ_inj]
  rwa [eval_aeval_update_zero, hvec] at hc

theorem degreeOf_linearShear_eq_of_isHomogeneous
    (c : Fin n → K) {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (heval : eval (Fin.cons 1 c) f ≠ 0) :
    degreeOf 0 (linearShear c f) = f.totalDegree := by
  have hf0 : f ≠ 0 := by
    intro h
    exact heval (by simp [h])
  have htd := hf.totalDegree hf0
  apply le_antisymm
  · simpa only [totalDegree_linearShear] using degreeOf_le_totalDegree (linearShear c f) 0
  · rw [← eval_cons_one_zero_linearShear, eval_cons_one_zero_of_isHomogeneous
      (isHomogeneous_linearShear c hf), constantCoeff_eq, finSuccEquiv_coeff_coeff] at heval
    have hdeg := le_degreeOf_of_mem_support 0 (mem_support_iff.mpr heval)
    simpa only [Finsupp.cons_zero, htd] using hdeg

theorem exists_linearShear_fix_coordinate_full [Infinite K]
    (j : Fin n) {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hnot : ¬ X j.succ ∣ f) :
    ∃ c : Fin n → K, c j = 0 ∧
      degreeOf 0 (linearShear c f) = f.totalDegree ∧
      linearShear c (X j.succ) = X j.succ := by
  obtain ⟨c, hc, hv⟩ := exists_eval_cons_one_with_zero j hf hnot
  refine ⟨c, hc, degreeOf_linearShear_eq_of_isHomogeneous c hf hv, ?_⟩
  change linearShearHom c (X j.succ) = X j.succ
  simp [hc]

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {n : ℕ}

theorem eliminationKer_isHomogeneous (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K)) :
    (RingHom.ker (eliminationHom c I)).IsHomogeneous
      (homogeneousSubmodule (Fin n) K) := by
  intro d p hp
  rw [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply]
  have hpI : linearShear (-c) (MvPolynomial.rename Fin.succ p) ∈ I := by
    have hp0 : eliminationHom c I p = 0 := hp
    rw [eliminationHom_apply, Ideal.Quotient.eq_zero_iff_mem] at hp0
    exact hp0
  have hd := homogeneousComponent_mem_of_mem hI hpI d
  rw [homogeneousComponent_linearShear, ← rename_homogeneousComponent] at hd
  change eliminationHom c I (homogeneousComponent d p) = 0
  rw [eliminationHom_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact hd

theorem homogeneous_prime_finOne_eq_bot
    (P : Ideal (MvPolynomial (Fin 1) K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin 1) K))
    (hX : X (0 : Fin 1) ∉ P) : P = ⊥ := by
  by_contra hP0
  obtain ⟨d, f, hf0, hfP, hf, hnot⟩ :=
    WeightedTorusJets.Geometry.exists_homogeneous_relation_not_dvd_coordinate P hP hP0 0 hX
  have hne : aeval (Function.update (X (R := K)) (0 : Fin 1) 0) f ≠ 0 :=
    (WeightedTorusJets.Geometry.aeval_update_zero_eq_zero_iff 0 f).not.mpr hnot
  have hu : Function.update (X (R := K)) (0 : Fin 1) 0 =
      (0 : Fin 1 → MvPolynomial (Fin 1) K) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  have hc : f.coeff 0 ≠ 0 := by
    intro hc
    apply hne
    rw [hu, aeval_zero, constantCoeff_eq, hc, map_zero]
  have hd : d = 0 := by
    have hd' := hf hc
    simpa only [map_zero] using hd'.symm
  subst d
  have he : f = C (f.coeff 0) := by
    simpa only [homogeneousComponent_zero] using (homogeneousComponent_eq_self hf).symm
  exact (Ideal.IsPrime.ne_top inferInstance)
    (P.eq_top_of_isUnit_mem hfP (he ▸ hc.isUnit.map MvPolynomial.C))

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

theorem exists_integral_injective_linear_quotient_fixed_last [Infinite K]
    {n : ℕ} (P : Ideal (MvPolynomial (Fin (n + 1)) K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K))
    (hX : X (Fin.last n) ∉ P) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin (s + 1)) K →ₐ[K]
      (MvPolynomial (Fin (n + 1)) K ⧸ P),
      Function.Injective g ∧ g.IsIntegral ∧
      (∀ i, ∃ l : MvPolynomial (Fin (n + 1)) K,
        l.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk P l) ∧
      g (X (Fin.last s)) = Ideal.Quotient.mk P (X (Fin.last n)) := by
  induction n with
  | zero =>
    have hP0 : P = ⊥ := homogeneous_prime_finOne_eq_bot P hP hX
    have hbij : Function.Bijective (Ideal.Quotient.mkₐ K P) :=
      (Ideal.Quotient.mk_bijective_iff_eq_bot P).mpr hP0
    exact ⟨0, le_rfl, Ideal.Quotient.mkₐ K P, hbij.1,
      RingHom.isIntegral_of_surjective _ hbij.2,
      fun i => ⟨MvPolynomial.X i, isHomogeneous_X K i, rfl⟩, rfl⟩
  | succ n ih =>
    by_cases hP0 : P = ⊥
    · have hbij : Function.Bijective (Ideal.Quotient.mkₐ K P) :=
        (Ideal.Quotient.mk_bijective_iff_eq_bot P).mpr hP0
      exact ⟨n + 1, le_rfl, Ideal.Quotient.mkₐ K P, hbij.1,
        RingHom.isIntegral_of_surjective _ hbij.2,
        fun i => ⟨MvPolynomial.X i, isHomogeneous_X K i, rfl⟩, rfl⟩
    · obtain ⟨d, f, hf0, hfP, hf, hnot⟩ :=
        WeightedTorusJets.Geometry.exists_homogeneous_relation_not_dvd_coordinate
          P hP hP0 (Fin.last (n + 1)) hX
      obtain ⟨c, hc, hdeg, _⟩ := exists_linearShear_fix_coordinate_full (Fin.last n) hf
        (by simpa using hnot)
      have hfix : linearShear (-c) (X (Fin.last n).succ) = X (Fin.last (n + 1)) := by
        change linearShearHom (-c) (X (Fin.last n).succ) = _
        rw [linearShearHom_X_succ]
        simp [hc]
      let e := eliminationHom c P
      let J := RingHom.ker e
      let φ := Ideal.kerLiftAlg e
      let : J.IsPrime := RingHom.ker_isPrime e
      have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
        eliminationKer_isHomogeneous c P hP
      have hXJ : X (Fin.last n) ∉ J := by
        intro hx
        have hx0 : e (X (Fin.last n)) = 0 := hx
        change eliminationHom c P (X (Fin.last n)) = 0 at hx0
        rw [eliminationHom_X, hfix, Ideal.Quotient.eq_zero_iff_mem] at hx0
        exact hX hx0
      obtain ⟨s, hs, g, hinj, hint, hlin, hlast⟩ := ih J hJ hXJ
      refine ⟨s, Nat.le_succ_of_le hs, φ.comp g, ?_, ?_, ?_, ?_⟩
      · exact (φ.coe_comp g) ▸ (Ideal.kerLiftAlg_injective e).comp hinj
      · exact hint.trans g.toRingHom φ.toRingHom
          (eliminationHom_isIntegral c P hf0 hfP hdeg).kerLift
      · intro i
        obtain ⟨l, hl, hgl⟩ := hlin i
        refine ⟨linearShear (-c) (MvPolynomial.rename Fin.succ l),
          isHomogeneous_linearShear (-c) hl.rename_isHomogeneous, ?_⟩
        rw [AlgHom.comp_apply, hgl]
        change e l = _
        exact eliminationHom_apply c P l
      · rw [AlgHom.comp_apply, hlast]
        change eliminationHom c P (X (Fin.last n)) = _
        rw [eliminationHom_X, hfix]

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

theorem exists_integral_injective_linear_quotient_fixed_coordinate [Infinite K]
    {n : ℕ} (P : Ideal (MvPolynomial (Fin (n + 1)) K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K))
    (i : Fin (n + 1)) (hX : X i ∉ P) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin (s + 1)) K →ₐ[K]
      (MvPolynomial (Fin (n + 1)) K ⧸ P),
      Function.Injective g ∧ g.IsIntegral ∧
      (∀ j, ∃ l : MvPolynomial (Fin (n + 1)) K,
        l.IsHomogeneous 1 ∧ g (MvPolynomial.X j) = Ideal.Quotient.mk P l) ∧
      g (X 0) = Ideal.Quotient.mk P (X i) := by
  classical
  let e := MvPolynomial.renameEquiv K (Equiv.swap i (Fin.last n))
  let J := Ideal.comap e.toAlgHom.toRingHom P
  let : J.IsPrime := Ideal.comap_isPrime e.toAlgHom.toRingHom P
  have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
    intro d p hp
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply]
    change MvPolynomial.rename (Equiv.swap i (Fin.last n)) (homogeneousComponent d p) ∈ P
    rw [MvPolynomial.rename_homogeneousComponent]
    exact homogeneousComponent_mem_of_mem hP hp d
  have hlast : X (Fin.last n) ∉ J := by
    change e (X (Fin.last n)) ∉ P
    simpa only [e, renameEquiv_apply, rename_X, Equiv.swap_apply_right] using hX
  have hIJ : P = J.map e.toAlgHom.toRingHom :=
    (Ideal.map_comap_of_surjective e.toAlgHom.toRingHom e.surjective P).symm
  let E := Ideal.quotientEquivAlg J P e hIJ
  have hE : ∀ p, E (Ideal.Quotient.mk J p) = Ideal.Quotient.mk P (e p) := by
    intro p
    exact Ideal.quotientEquivAlg_mk (I := J) (J := P) e hIJ p
  obtain ⟨s, hs, g, hinj, hint, hlin, hfix⟩ :=
    exists_integral_injective_linear_quotient_fixed_last J hJ hlast
  let r := MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin (s + 1)) (Fin.last s))
  refine ⟨s, hs, E.toAlgHom.comp (g.comp r.toAlgHom), ?_, ?_, ?_, ?_⟩
  · exact E.injective.comp (hinj.comp r.injective)
  · have hrint := algEquiv_isIntegral r
    have hEint := algEquiv_isIntegral
      (A := MvPolynomial (Fin (n + 1)) K ⧸ J)
      (B := MvPolynomial (Fin (n + 1)) K ⧸ P) E
    exact (hrint.trans r.toAlgHom.toRingHom g.toRingHom hint).trans _ _ hEint
  · intro j
    obtain ⟨l, hl, hgl⟩ := hlin ((Equiv.swap (0 : Fin (s + 1)) (Fin.last s)) j)
    refine ⟨e l, hl.rename_isHomogeneous, ?_⟩
    change E (g (r (X j))) = Ideal.Quotient.mk P (e l)
    simp only [r, renameEquiv_apply, rename_X]
    rw [hgl]
    exact hE l
  · change E (g (r (X 0))) = Ideal.Quotient.mk P (X i)
    simp only [r, renameEquiv_apply, rename_X, Equiv.swap_apply_left]
    rw [hfix, hE]
    simp only [e, renameEquiv_apply, rename_X, Equiv.swap_apply_right]

theorem finite_of_integral_quotient {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I))
    (hint : g.IsIntegral) : g.Finite := by
  let : Algebra.FiniteType K (MvPolynomial (Fin n) K ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  have h : algebraMap K (MvPolynomial (Fin n) K ⧸ I) =
      g.toRingHom.comp (algebraMap K (MvPolynomial (Fin s) K)) := by
    ext a
    exact (g.commutes a).symm
  exact hint.to_finite
    ((h ▸ RingHom.finiteType_algebraMap.mpr inferInstance).of_comp_finiteType)

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.Geometry

theorem ringKrullDim_eq_of_integral_faithful_goingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] [Algebra.HasGoingDown R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro p q hpq
    exact Ideal.IsIntegral.comap_lt_comap (R := R) (A := S) (I := p.asIdeal) (J := q.asIdeal) hpq
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    apply iSup_le
    intro l
    obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := S) l.last.asIdeal
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P.1
    simpa only [hlen] using Order.LTSeries.length_le_krullDim L

theorem ringKrullDim_eq_of_integral_faithful_normal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] [Algebra.IsIntegral R S] [FaithfulSMul R S] [IsIntegrallyClosed R] :
    ringKrullDim S = ringKrullDim R :=
  ringKrullDim_eq_of_integral_faithful_goingDown

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

theorem ringKrullDim_quotient_eq_normalization_variables {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I))
    (hg : Function.Injective g) (hint : g.IsIntegral) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ I) = s := by
  let : Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    g.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  let : Algebra.IsIntegral (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    (faithfulSMul_iff_algebraMap_injective
      (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I)).mpr hg
  rw [WeightedTorusJets.Geometry.ringKrullDim_eq_of_integral_faithful_normal
    (R := MvPolynomial (Fin s) K)]
  simp

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_finite_linear_normalization_finite_variables
    {K σ : Type*} [Field K] [Infinite K] [Finite σ]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ K))
    (i : σ) (hX : X i ∉ P) :
    ∃ s : ℕ, s + 1 ≤ Nat.card σ ∧
      ∃ g : MvPolynomial (Fin (s + 1)) K →ₐ[K] (MvPolynomial σ K ⧸ P),
        Function.Injective g ∧ g.IsIntegral ∧ g.Finite ∧
        (∀ j, ∃ l : MvPolynomial σ K,
          l.IsHomogeneous 1 ∧ g (MvPolynomial.X j) = Ideal.Quotient.mk P l) ∧
        g (X 0) = Ideal.Quotient.mk P (X i) ∧
        ringKrullDim (MvPolynomial σ K ⧸ P) = (s + 1 : ℕ) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  cases m with
  | zero => exact Fin.elim0 (e i)
  | succ n =>
    let r := MvPolynomial.renameEquiv K e.symm
    let J := Ideal.comap r.toAlgHom.toRingHom P
    let : J.IsPrime := Ideal.comap_isPrime r.toAlgHom.toRingHom P
    have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
      intro d p hp
      rw [← DirectSum.Decomposition.decompose'_eq,
        MvPolynomial.decomposition.decompose'_apply]
      change MvPolynomial.rename e.symm (homogeneousComponent d p) ∈ P
      rw [MvPolynomial.rename_homogeneousComponent]
      exact homogeneousComponent_mem_of_mem hP hp d
    have hXi : X (e i) ∉ J := by
      change r (X (e i)) ∉ P
      simpa only [r, renameEquiv_apply, rename_X, Equiv.symm_apply_apply] using hX
    have hJP : P = J.map r.toAlgHom.toRingHom :=
      (Ideal.map_comap_of_surjective r.toAlgHom.toRingHom r.surjective P).symm
    let E := Ideal.quotientEquivAlg J P r hJP
    have hE : ∀ p, E (Ideal.Quotient.mk J p) = Ideal.Quotient.mk P (r p) := by
      intro p
      exact Ideal.quotientEquivAlg_mk (I := J) (J := P) r hJP p
    obtain ⟨s, hs, g, hinj, hint, hlin, hfix⟩ :=
      exists_integral_injective_linear_quotient_fixed_coordinate J hJ (e i) hXi
    have hcard : Nat.card σ = n + 1 := by
      simpa using Nat.card_congr e
    let G := E.toAlgHom.comp g
    have hEint := algEquiv_isIntegral
      (A := MvPolynomial (Fin (n + 1)) K ⧸ J)
      (B := MvPolynomial σ K ⧸ P) E
    have hGint : G.IsIntegral := hint.trans _ _ hEint
    have hEfin : E.toAlgHom.Finite :=
      RingHom.Finite.of_surjective E.toAlgHom.toRingHom E.surjective
    have hGfin : G.Finite := hEfin.comp (finite_of_integral_quotient J g hint)
    refine ⟨s, by rw [hcard]; omega, G, E.injective.comp hinj, hGint, hGfin, ?_, ?_, ?_⟩
    · intro j
      obtain ⟨l, hl, hgl⟩ := hlin j
      refine ⟨r l, hl.rename_isHomogeneous, ?_⟩
      change E (g (X j)) = _
      rw [hgl]
      exact hE l
    · change E (g (X 0)) = _
      rw [hfix, hE]
      simp only [r, renameEquiv_apply, rename_X, Equiv.symm_apply_apply]
    · rw [← ringKrullDim_eq_of_ringEquiv E.toRingEquiv]
      exact ringKrullDim_quotient_eq_normalization_variables J g hinj hint

end WeightedTorusJets.LinearNormalization

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_FinrankDerivationCardTranscendenceBasis
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section
open Module
open scoped RatFunc

namespace WeightedTorusJets

theorem finiteType_dimension_trdeg {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) ∧ Algebra.trdeg K A = n := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine ⟨n, ?_, ?_⟩
  · rw [Geometry.ringKrullDim_eq_of_integral_faithful_goingDown
      (R := MvPolynomial (Fin n) K)]
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
  · have hz : Algebra.trdeg (MvPolynomial (Fin n) K) A = 0 :=
      trdeg_eq_zero_iff.mpr inferInstance
    have h := lift_trdeg_add_eq K (MvPolynomial (Fin n) K) A
    simpa [hz, MvPolynomial.trdeg_of_isDomain] using h.symm

end WeightedTorusJets

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets

theorem trdeg_eq_of_integral_polynomial_base {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] (n : ℕ)
    (g : MvPolynomial (Fin n) K →ₐ[K] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    Algebra.trdeg K A = n := by
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hz : Algebra.trdeg (MvPolynomial (Fin n) K) A = 0 :=
    trdeg_eq_zero
  have h := lift_trdeg_add_eq K (MvPolynomial (Fin n) K) A
  simpa [hz, MvPolynomial.trdeg_of_isDomain] using h.symm

theorem fractionField_trdeg_eq_nat {K A F : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Field F]
    [Algebra K F] [Algebra A F] [IsScalarTower K A F] [IsFractionRing A F]
    (n : ℕ) (h : Algebra.trdeg K A = n) : Algebra.trdeg K F = n := by
  let : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have hz : Algebra.trdeg A F = 0 := trdeg_eq_zero
  have htower := lift_trdeg_add_eq K A F
  simpa [h, hz] using htower.symm

end WeightedTorusJets
namespace WeightedTorusJets.Geometry

theorem polynomial_prime_height_add_quotient_dim_of_finite
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ K ⧸ p) = Nat.card σ := by
  obtain ⟨t, ht, hmax, _, hheight, _⟩ := exists_coordinate_localization p
  obtain ⟨d, hdim, htr⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := MvPolynomial σ K ⧸ p)
  have hF : Algebra.trdeg K (FractionRing (MvPolynomial σ K ⧸ p)) = d :=
    WeightedTorusJets.fractionField_trdeg_eq_nat d htr
  have hcard : Nat.card t = d := by
    have h := congrArg Cardinal.toNat ht.lift_cardinalMk_eq_trdeg
    simpa [Nat.card, hF] using h
  rw [← hheight, hdim, ← hcard]
  have hsum : Nat.card (tᶜ : Set σ) + Nat.card t = Nat.card σ := by
    simpa only [Nat.card_coe_set_eq] using Set.ncard_compl_add_ncard t
  exact_mod_cast hsum



variable {K σ : Type*} [Field K] [Finite σ]

theorem polynomial_normalization_quotient_dimension_finite {s : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial σ K ⧸ p)
    (hg : Function.Injective g) (hgi : g.IsIntegral) :
    ringKrullDim (MvPolynomial σ K ⧸ p) = (s : WithBot ℕ∞) := by
  obtain ⟨d, hdim, htr⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := MvPolynomial σ K ⧸ p)
  have hs := WeightedTorusJets.trdeg_eq_of_integral_polynomial_base s g hg hgi
  have hd : d = s := by exact_mod_cast htr.symm.trans hs
  simpa only [hd] using hdim

theorem polynomial_normalization_count_add_height_finite {s : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial σ K ⧸ p)
    (hg : Function.Injective g) (hgi : g.IsIntegral) :
    (s : ℕ∞) + p.height = Nat.card σ := by
  have h := polynomial_prime_height_add_quotient_dim_of_finite (K := K) p
  rw [polynomial_normalization_quotient_dimension_finite p g hg hgi] at h
  have hh : p.height + (s : ℕ∞) = Nat.card σ := by exact_mod_cast h
  simpa only [add_comm] using hh


end WeightedTorusJets.Geometry

end
end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GradedIdealQuotient
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section

section

namespace WeightedTorusJets.Geometry

theorem finrank_homogeneousSubmodule_fin (K : Type*) [Field K] (r n : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin r) K n) =
      (r + n - 1).choose n := by
  simpa using finrank_homogeneousSubmodule (σ := Fin r) (K := K) n

end WeightedTorusJets.Geometry

end

section

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem linear_quotient_map_homogeneous_mem
    {K σ τ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (g : MvPolynomial τ K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l)
    {d : ℕ} {p : MvPolynomial τ K} (hp : p.IsHomogeneous d) :
    g p ∈ (homogeneousSubmodule σ K d).map (Ideal.Quotient.mkₐ K I).toLinearMap := by
  classical
  choose l hl hgl using hlin
  have hg : g = (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval l) := by
    ext i
    simpa only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hgl i
  refine ⟨MvPolynomial.aeval l p, ?_, ?_⟩
  · change (MvPolynomial.aeval l p).IsHomogeneous d
    simpa only [one_mul] using hp.aeval l hl
  · rw [hg]
    rfl

theorem linear_quotient_map_gradedSMul
    {K σ τ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (g : MvPolynomial τ K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    SetLike.GradedSMul (homogeneousSubmodule τ K)
      (fun n => (homogeneousSubmodule σ K n).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let _ := g.toRingHom.toAlgebra
  let _ : Module (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toModule
  let _ : SMul (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  constructor
  intro i j p y hp hy
  obtain ⟨a, ha, hga⟩ := linear_quotient_map_homogeneous_mem I g hlin hp
  obtain ⟨b, hb, hgb⟩ := hy
  refine ⟨a * b, ?_, ?_⟩
  · exact SetLike.GradedMul.mul_mem ha hb
  · change Ideal.Quotient.mk I (a * b) = g p * y
    rw [map_mul]
    exact congrArg₂ (· * ·) hga hgb

end WeightedTorusJets.Geometry

end

section

namespace WeightedTorusJets

theorem normalization_quotient_finite_torsionFree_finiteVariables {K σ : Type*} [Field K] [Finite σ] {s : ℕ}
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hg : Function.Injective g) (hint : g.toRingHom.IsIntegral) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    IsScalarTower K (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) ∧
      Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) ∧
      Module.IsTorsionFree (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) := by
  let _ := g.toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toModule
  let _ : SMul (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  let : IsScalarTower K (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    IsScalarTower.of_algHom g
  let : Algebra.FiniteType K (MvPolynomial σ K ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  let : Algebra.FiniteType (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin s) K)
      (MvPolynomial σ K ⧸ I)
  let : Algebra.IsIntegral (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    ⟨hint⟩
  exact ⟨inferInstance, Algebra.IsIntegral.finite,
    Module.isTorsionFree_iff_algebraMap_injective.mpr hg⟩

end WeightedTorusJets

end

section
namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial _root_.Filter

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hilbertPolynomial_normalization_finiteVariables
    {K σ : Type*} [Field K] [Finite σ] {d : ℕ}
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (g : MvPolynomial (Fin (d + 1)) K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hg : Function.Injective g) (hint : g.toRingHom.IsIntegral)
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    (hilbertPolynomial I hI).natDegree = d ∧ projectiveDegree I hI =
      Module.finrank (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) := by
  let _ := g.toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toModule
  let _ : SMul (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  obtain ⟨htower, hfinite, htfree⟩ :=
    WeightedTorusJets.normalization_quotient_finite_torsionFree_finiteVariables I g hg hint
  let 𝓐 := homogeneousSubmodule (Fin (d + 1)) K
  let 𝓜 := degreePiece I
  have : GradedAlgebra 𝓜 := gradedIdealQuotient (homogeneousSubmodule σ K) I hI
  have : SetLike.GradedSMul 𝓐 𝓜 := linear_quotient_map_gradedSMul I g hlin
  have : ∀ m, Module.Finite K (𝓜 m) := by
    intro m
    have : Module.Finite K (homogeneousSubmodule σ K m) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K m)
    exact Module.Finite.map _ _
  have hdim (m : ℕ) : Module.finrank K (𝓐 m) = (m + d).choose d := by
    rw [finrank_homogeneousSubmodule_fin]
    have hm : d + 1 + m - 1 = m + d := by omega
    rw [hm, Nat.choose_symm_add]
  have hP : ∀ᶠ m : ℕ in atTop,
      (Module.finrank K (𝓜 m) : ℚ) = (hilbertPolynomial I hI).eval (m : ℚ) := by
    obtain ⟨N, hN⟩ := hilbertPolynomial_spec I hI
    filter_upwards [eventually_gt_atTop N] with m hm
    exact hN m hm
  have h := hilbertPolynomial_degree_coefficient_eq_rank 𝓐 𝓜
    (a := X (0 : Fin (d + 1))) (X_ne_zero _) (isHomogeneous_X K _) d hdim
    (hilbertPolynomial I hI) hP
  have heq : (projectiveDegree I hI : ℚ) =
      (Module.finrank (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) : ℚ) := by
    rw [projectiveDegree_cast, h.1]
    exact h.2
  exact ⟨h.1, by exact_mod_cast heq⟩

theorem projectiveDegree_eq_normalization_rank_finiteVariables
    {K σ : Type*} [Field K] [Finite σ] {d : ℕ}
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (g : MvPolynomial (Fin (d + 1)) K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hg : Function.Injective g) (hint : g.toRingHom.IsIntegral)
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    projectiveDegree I hI =
      Module.finrank (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
  (hilbertPolynomial_normalization_finiteVariables I hI g hg hint hlin).2

end WeightedTorusJets.Geometry.GradedQuotient
end

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LinearVariableBasis
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open Module TensorProduct

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem quotient_length_congr_ideal
    {R : Type*} [CommRing R] (I J : Ideal R) (h : I = J) :
    Module.length R (R ⧸ I) = Module.length R (R ⧸ J) := by
  subst J
  rfl

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LocalLengthMulProjectiveClosureDegree
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section
namespace WeightedTorusJets.Geometry

open MvPolynomial

attribute [local instance] coneIdeal_isPrime

theorem local_length_mul_projectiveClosure_degree_le
    {K σ : Type*} [Field K] [Infinite K] [Finite σ] {h D : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hp : p.height = h)
    (f : Fin h → MvPolynomial σ K)
    (hf : ∀ i, (f i).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))) *
      (GradedQuotient.projectiveDegree (coneIdeal p) (coneIdeal_isHomogeneous p) : ℕ∞) ≤
        (D ^ h : ℕ) := by
  obtain ⟨d, _, g, hg, hint, hfinite, hlin, _, _⟩ :=
    LinearNormalization.exists_finite_linear_normalization_finite_variables
      (coneIdeal p) (coneIdeal_isHomogeneous p) none (X_none_not_mem_coneIdeal p)
  have hcount : d + 1 + h = Nat.card (Option σ) := by
    have hc := polynomial_normalization_count_add_height_finite
      (coneIdeal p) g hg hint
    rw [coneIdeal_height, hp] at hc
    exact_mod_cast hc
  let F : Fin h → MvPolynomial (Option σ) K := fun i => homogenize (f i)
  have hF (i : Fin h) : (F i).totalDegree ≤ D := by
    simpa only [F, homogenize_totalDegree] using hf i
  have hrad' : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))
        (F i)))).radical = IsLocalRing.maximalIdeal (Localization.AtPrime (coneIdeal p)) := by
    have ha : ((Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def] using hrad
    simpa only [paddedHomogenizedIdeal, pow_zero, one_mul, Ideal.map_span,
      ← Set.range_comp, Function.comp_def, F] using
      cone_padded_local_radical p f (fun _ => 0) ha
  have hlength :
      Module.length (Localization.AtPrime (coneIdeal p))
        (Localization.AtPrime (coneIdeal p) ⧸ Ideal.span (Set.range (fun i =>
          algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))
            (F i)))) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span (Set.range (fun i =>
          algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))) := by
    have hA : (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime p)) =
          Ideal.span (Set.range (fun i =>
            algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i))) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    have hC : (paddedHomogenizedIdeal f (fun _ => 0)).map
        (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))) =
          Ideal.span (Set.range (fun i =>
            algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))
              (F i))) := by
      simp only [paddedHomogenizedIdeal, pow_zero, one_mul, Ideal.map_span,
        ← Set.range_comp, Function.comp_def, F]
    exact (DegreeBezout.quotient_length_congr_ideal _ _ hC).symm.trans
      ((cone_padded_quotient_length p f (fun _ => 0)).trans
        (DegreeBezout.quotient_length_congr_ideal _ _ hA))
  have hdegree := GradedQuotient.projectiveDegree_eq_normalization_rank_finiteVariables
    (coneIdeal p) (coneIdeal_isHomogeneous p) g hg hint hlin
  have hbound := DegreeBezout.linear_normalization_weighted_local_length_le_jb247
    (coneIdeal p) g hg hfinite hlin hcount F hF hrad'
  rw [hlength, ← hdegree] at hbound
  exact hbound

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusRectangleJetIdealParametersProjectiveDegreeBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section
namespace WeightedTorusJets.Geometry

section TorusWeightedParameters

variable {K : Type*} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))

theorem torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247_oai
    (q : Ideal T₄) [q.IsPrime] (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : P₄} (hF : F ∈ polynomialBox K N)
    (hq : q ∈ (rectangleJetIdeal
      (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).minimalPrimes) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
        (IsLocalRing.CotangentSpace (Localization.AtPrime q))) → P₄,
      (∀ i, g i ∈ Submodule.span K
        ((fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j})) ∧
      (∀ i, (g i).totalDegree ≤ 4 * N) ∧
      (Ideal.span (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸
        (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).map
          (algebraMap T₄ (Localization.AtPrime q))) ≤
        Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) *
        (GradedQuotient.projectiveDegree
          (coneIdeal (q.comap (algebraMap P₄ T₄)))
          (coneIdeal_isHomogeneous (q.comap (algebraMap P₄ T₄))) : ℕ∞) ≤
        ((4 * N) ^ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
          (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : ℕ) := by
  obtain ⟨g, hspan, hdeg, hrad, hlength, _⟩ :=
    rectangleJetIdeal_exists_parameters_with_length
      (A := Localization.AtPrime q) q c t b hN hF hq
  let p := q.comap (algebraMap P₄ T₄)
  let : p.IsPrime := Ideal.comap_isPrime _ q
  let : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : P₄))) (Localization.AtPrime q) q
  refine ⟨g, hspan, hdeg, hrad, hlength, ?_⟩
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)
  have hcomm i : e (algebraMap P₄ (Localization.AtPrime q) (g i)) =
      algebraMap P₄ (Localization.AtPrime p) (g i) := e.commutes (g i)
  have hrad' := radical_span_eq_maximalIdeal_of_commuting_images e.toRingEquiv
    (fun i => algebraMap P₄ (Localization.AtPrime q) (g i))
    (fun i => algebraMap P₄ (Localization.AtPrime p) (g i)) hcomm hrad
  rw [quotient_length_eq_of_commuting_images e.toRingEquiv
    (fun i => algebraMap P₄ (Localization.AtPrime q) (g i))
    (fun i => algebraMap P₄ (Localization.AtPrime p) (g i)) hcomm]
  exact local_length_mul_projectiveClosure_degree_le p
    (polynomial_prime_height_eq_cotangent_finrank (A := Localization.AtPrime q) p)
    g hdeg hrad'

end TorusWeightedParameters

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247_oai.{u_1} := @OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247_oai.{u_1}
