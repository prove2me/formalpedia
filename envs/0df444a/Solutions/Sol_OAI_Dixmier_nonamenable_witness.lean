-- Prove2me | solution 1 for OAI.Dixmier.nonamenable_witness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:01:36.592532+00:00
-- url     : https://prove2.me/submissions/49c14ee1-bf98-47d7-a7c8-4c5eac1c2abd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Main.lean:L16-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.nonamenable_witness. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
import Definitions.Def_OAI_Analysis_Unitarizability_Masked
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction
import Theorems.Thm_OAI_Dixmier_DirectSumObstruction_direct_sum_obstruction
import Theorems.Thm_OAI_Dixmier_HilbertSum_separableSpace
import Theorems.Thm_OAI_Dixmier_Masked_difference_norm_le
import Theorems.Thm_OAI_Dixmier_Masked_masked_bound
import Theorems.Thm_OAI_Dixmier_SignMatrix_frames_for_fintype
import Theorems.Thm_OAI_Dixmier_dimension_ratio_tendsto
import Theorems.Thm_OAI_Dixmier_exists_contracting_sum
import Theorems.Thm_OAI_Dixmier_kernel_energy_ge_card
import Theorems.Thm_OAI_Dixmier_sparse_mask_for_words

-- ---- from OAI.Analysis.Unitarizability.Regular ----
namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*}

variable [Group G]

theorem word_card {I : Type*} [Fintype I] (n : ℕ) :
    Fintype.card (Word I n) = (Fintype.card I) ^ n := by
  induction n with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (I × Word I n) = _
    rw [Fintype.card_prod, ih, pow_succ']

end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Contracting ----
namespace OAI

/-! Contracting averages and sparse splitting for nonamenable groups. -/
noncomputable section
namespace Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- Sparse splitting from nonamenability. A single S and ρ work for every
positive word length; all words remain separate labels, even when their group products agree. -/
theorem sparse_splitting_of_nonamenable (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ ℓ : ℕ, 0 < ℓ → ∃ a : G → Word S ℓ → Bool,
        (∀ x, (rowOnes a x).card ≤ ⌈(S.card : ℝ)^ℓ * ρ^ℓ⌉₊) ∧
        ∀ y, (columnZeros a (wordProduct (fun s : S => (s : G)) ℓ) y).card ≤
          ⌈(S.card : ℝ)^ℓ * ρ^ℓ⌉₊ := by
  classical
  obtain ⟨S, h1, hd, ρ, hρ, hρ1, hsum⟩ := exists_contracting_sum hG
  refine ⟨S, h1, hd, ρ, hρ, hρ1, fun ℓ hℓ => ?_⟩
  have hsum' : ‖∑ g : S, rightRegular (g : G)‖ ≤ (Fintype.card S : ℝ) * ρ := by
    simpa only [Fintype.card_coe, Finset.sum_coe_sort] using hsum
  simpa only [Fintype.card_coe] using
    sparse_mask_for_words (fun s : S => (s : G)) hρ.le hsum' ℓ hℓ

end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Parameters ----
namespace OAI

/-! Ceiling parameters and dimension-ratio asymptotics. -/
noncomputable section
namespace Dixmier
open Filter Topology

theorem endpointCapacity_pos {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (ℓ : ℕ) :
    0 < endpointCapacity d ρ ℓ := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (pow_pos (by exact_mod_cast (by omega : 0 < d)) _) (pow_pos hρ _)

theorem fiberDimension_pos {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (ℓ : ℕ) :
    0 < fiberDimension d ρ ℓ := by
  have hr : (0 : ℝ) < endpointCapacity d ρ ℓ := by exact_mod_cast endpointCapacity_pos hd hρ ℓ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hn1 : (1 : ℝ) ≤ (d : ℝ)^ℓ := one_le_pow₀ hdR
  have hlog : 0 < Real.log (2 * (d : ℝ)^ℓ) := Real.log_pos (by nlinarith)
  apply Nat.ceil_pos.mpr
  exact mul_pos (mul_pos (by norm_num) hr) hlog

/-- Reciprocal dimension ratio used by the direct-sum obstruction. -/
theorem reciprocal_dimension_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (d : ℝ)^ℓ / (fiberDimension d ρ ℓ : ℝ)) atTop atTop := by
  have ht : Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ)
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨dimension_ratio_tendsto hd hρ.le hρ1, Filter.Eventually.of_forall (fun ℓ => ?_)⟩
    change 0 < (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ
    apply div_pos
    · exact_mod_cast fiberDimension_pos hd hρ ℓ
    · exact pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp ht

end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.KernelObstruction ----
namespace OAI

/-! Coordinate maps and the invariant-kernel obstruction.
The Hilbert space is the lp space with finite Euclidean fibres. -/
noncomputable section
namespace Dixmier
namespace KernelObstruction
open scoped ComplexConjugate
open Finset
variable {G K : Type*} [Fintype K]
attribute [local instance] OAI.Dixmier.KernelObstruction.instDecidableEq_oAI_1
theorem inclusion_opNorm_le (x : G) : ‖inclusion (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem evaluation_opNorm_le (x : G) : ‖evaluation (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) ξ x

variable [Group G]

omit [Group G] in
theorem row_norm_le (F : Op G K) (x : G) : ‖row F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (evaluation_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem col_norm_le (F : Op G K) (x : G) : ‖col F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (inclusion_opNorm_le (K := K) x) (norm_nonneg F))

end KernelObstruction
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Cocycle ----
namespace OAI

/-! Cocycle algebra in an arbitrary ring, specializing to bounded complex Hilbert-space operators. -/
namespace Dixmier
section Ring
variable {G R : Type*} [Group G] [Ring R]

theorem conjugate_eq_self_iff_commute (U : G →* R) (g : G) (T : R) :
    conjugate U g T = T ↔ Commute (U g) T := by
  have hinv : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  have hginv : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  constructor
  · intro h
    have hh := congrArg (fun x : R => x * U g) h
    change U g * T = T * U g
    simpa [conjugate, mul_assoc, hinv] using hh
  · intro h
    change U g * T * U g⁻¹ = T
    rw [h.eq, mul_assoc, hginv, mul_one]

end Ring
end Dixmier

end OAI

-- ---- from OAI.Analysis.Unitarizability.MaskAlgebra ----
namespace OAI

/-! Sparse masks yield operator conjugation identities, and the
constant mask has a rank-one collision kernel. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
attribute [local instance] OAI.Dixmier.Masked.instDecidableEq_oAI_3
/-- The masked operator bound in finite-cardinality form. -/
theorem masked_bound_of_frame (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v p b)
    (hr : ∀ x, (rowSet c x).card ≤ p) (hcol : ∀ y, (columnSet s c y).card ≤ p) :
    ‖operator v s c hc‖ ≤ b^2 :=
  masked_bound v s c hc hb (fun x => hv _ (hr x)) (fun y => hv _ (hcol y))

theorem operator_sub (v : I → Fibre K) (s : I → G) (c d : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (hd : ∀ x i, ‖d x i‖ ≤ 1)
    (hcd : ∀ x i, ‖c x i - d x i‖ ≤ 1) :
    operator v s c hc - operator v s d hd = operator v s (fun x i => c x i-d x i) hcd := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change operator v s c hc ξ x - operator v s d hd ξ x = _
  simp only [operator_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

theorem conjugate_operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (g : G) :
    conjugate KernelObstruction.translation g (operator v s c hc) =
      operator v s (fun x i => c (g⁻¹*x) i) (fun _ i => hc _ i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change KernelObstruction.translation g (operator v s c hc (KernelObstruction.translation g⁻¹ ξ)) x = _
  simp only [KernelObstruction.translation_apply, operator_apply, inv_inv,
    ← mul_assoc, mul_inv_cancel, one_mul]

theorem constant_commutant (v : I → Fibre K) (s : I → G) :
    constant v s ∈ KernelObstruction.Commutant := by
  intro g
  apply Commute.symm
  apply (conjugate_eq_self_iff_commute KernelObstruction.translation g (constant v s)).mp
  exact conjugate_operator v s (fun _ _ => 1) (fun _ _ => by simp) g

theorem basis_inner_right (v : Fibre K) (b : K) :
    inner ℂ v (EuclideanSpace.basisFun K ℂ b) = conj (v b) := by
  rw [← EuclideanSpace.basisFun_inner K ℂ v b, inner_conj_symm]

theorem constant_kernel (v : I → Fibre K) (s : I → G) (g : G) :
    KernelObstruction.coefficients (KernelObstruction.block (constant v s) 1 g) =
      kernelCoefficients v s g := by
  apply (WithLp.equiv 2 ((K × K) → ℂ)).injective
  funext ab
  rcases ab with ⟨a,b⟩
  change (constant v s (lp.single (E := fun _ : G => Fibre K) 2 g (EuclideanSpace.basisFun K ℂ b)) 1) a = kernelCoefficients v s g (a,b)
  simp only [constant, operator_apply, one_mul, kernelCoefficients,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : s i = g
  · simp only [h, lp.single_apply_self, ite_true]
    change inner ℂ (v i) (EuclideanSpace.basisFun K ℂ b) * v i a = v i a * conj (v i b)
    rw [basis_inner_right, mul_comm]
  · simp [h]

theorem constant_energy_ge_card (v : I → Fibre K) (hv : ∀ i, ‖v i‖ = 1) (s : I → G) :
    (Fintype.card I : ℝ) ≤ KernelObstruction.energy (constant v s) := by
  unfold KernelObstruction.energy
  simp_rw [constant_kernel]
  exact kernel_energy_ge_card v hv s

end Masked
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.LocalBounds ----
namespace OAI

/-! Individual block row and column bounds from the endpoint assignment. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
attribute [local instance] OAI.Dixmier.Masked.instDecidableEq_oAI_5
theorem support_bound (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v p b) (J : Finset I) (hJ : J.card ≤ p)
    (hs : ∀ x i, c x i ≠ 0 → i ∈ J) : ‖operator v s c hc‖ ≤ b^2 := by
  apply masked_bound_of_frame _ _ _ _ hb hv
  · intro x
    exact (Finset.card_le_card (fun i hi => hs x i (Finset.mem_filter.mp hi).2)).trans hJ
  · intro y
    exact (Finset.card_le_card (fun i hi => hs _ i (Finset.mem_filter.mp hi).2)).trans hJ

omit [Group G] in
theorem rowMask_support (a : G → I → Bool) (x₀ x : G) (i : I) (h : rowMask a x₀ x i ≠ 0) :
    i ∈ rowOnes a x₀ := by
  unfold rowMask at h
  split_ifs at h with he
  · subst x
    cases ha : a x₀ i <;> simp_all [boolComplex, rowOnes]
  · exact (h rfl).elim

theorem columnMask_support (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I)
    (h : columnMask a s y₀ x i ≠ 0) : i ∈ columnZeros a s y₀ := by
  unfold columnMask at h
  split_ifs at h with he
  · have hx : y₀ * (s i)⁻¹ = x := by rw [← he, mul_inv_cancel_right]
    cases ha : a x i <;> simp_all [boolComplex, columnZeros]
  · exact (h rfl).elim

theorem row_localization (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (x₀ : G) :
    KernelObstruction.row (oriented v s a) x₀ =
      KernelObstruction.row (operator v s (rowMask a x₀) (rowMask_norm a x₀)) x₀ := by
  ext ξ z
  change (oriented v s a ξ x₀) z = (operator v s (rowMask a x₀) (rowMask_norm a x₀) ξ x₀) z
  simp [oriented, operator_apply, rowMask]

theorem column_localization (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (y₀ : G) :
    KernelObstruction.col (constant v s - oriented v s a) y₀ =
      KernelObstruction.col (operator v s (columnMask a s y₀) (columnMask_norm a s y₀)) y₀ := by
  have hsub : constant v s - oriented v s a =
      operator v s (fun x i => 1 - boolComplex (a x i)) (complement_norm a) :=
    operator_sub _ _ _ _ _ _ _
  rw [hsub]
  apply ContinuousLinearMap.ext
  intro z
  apply lp.ext
  funext x
  change operator v s (fun x i => 1 - boolComplex (a x i)) (complement_norm a) (lp.single 2 y₀ z) x =
    operator v s (columnMask a s y₀) (columnMask_norm a s y₀) (lp.single 2 y₀ z) x
  simp only [operator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x * s i = y₀
  · simp [columnMask, h]
  · rw [lp.single_apply_ne _ _ _ h]
    simp [columnMask, h]

theorem local_row_bound (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (x₀ : G) :
    ‖KernelObstruction.row (oriented v s a) x₀‖ ≤ b^2 := by
  have hJ : (rowOnes a x₀).card ≤ min (2*r) (Fintype.card I) :=
    le_min ((hr x₀).trans (by omega)) (Finset.card_le_univ _)
  have h := support_bound v s (rowMask a x₀) (rowMask_norm a x₀) hb hv (rowOnes a x₀) hJ
    (rowMask_support a x₀)
  rw [row_localization]
  exact (KernelObstruction.row_norm_le _ _).trans h

theorem local_column_bound (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hc : ∀ y, (columnZeros a s y).card ≤ r) (y₀ : G) :
    ‖KernelObstruction.col (constant v s - oriented v s a) y₀‖ ≤ b^2 := by
  have hJ : (columnZeros a s y₀).card ≤ min (2*r) (Fintype.card I) :=
    le_min ((hc y₀).trans (by omega)) (Finset.card_le_univ _)
  have h := support_bound v s (columnMask a s y₀) (columnMask_norm a s y₀) hb hv (columnZeros a s y₀) hJ
    (columnMask_support a s y₀)
  rw [column_localization]
  exact (KernelObstruction.col_norm_le _ _).trans h

end Masked
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.SumObstruction ----
namespace OAI

/-! The operator-theoretic direct-sum obstruction, constructed from stage operators
without any uniform bound on their norms. -/
noncomputable section
namespace Dixmier
namespace DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

omit [Group G] in
/-- The concrete carrier is separable when the group is countable. -/
theorem carrier_separable [Countable G] (k : ℕ → ℕ) :
    TopologicalSpace.SeparableSpace (Carrier G k) := by
  have (j : ℕ) : TopologicalSpace.SeparableSpace (Stage G k j) := HilbertSum.separableSpace
  have : TopologicalSpace.SeparableSpace (Total G k) := HilbertSum.separableSpace
  infer_instance

end DirectSumObstruction
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Main ----
namespace OAI

/-! The uniformly bounded nonunitarizable representation of a countable
nonamenable group, assembled from sparse masks, frames, and the direct-sum obstruction. -/
noncomputable section
namespace Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]

/-- A uniformly 101-bounded representation on a separable Hilbert space,
not similar to a unitary representation, constructed from nonamenability. -/
theorem nonamenable_witness (hG : ¬ Amenable G) : NonamenableWitness.{u,u} G := by
  classical
  obtain ⟨S, hS, hd, ρ, hρ, hρ1, hmask⟩ := sparse_splitting_of_nonamenable hG
  let d := S.card
  let k : ℕ → ℕ := fun j => fiberDimension d ρ (j+1)
  let r : ℕ → ℕ := fun j => endpointCapacity d ρ (j+1)
  let Labels : ℕ → Type u := fun j => Word S (j+1)
  let s : ∀ j, Labels j → G := fun j => wordProduct (fun x : S => (x : G)) (j+1)
  have hlabel (j : ℕ) : Fintype.card (Labels j) = d^(j+1) := by
    simp [Labels, word_card, d]
  have hn (j : ℕ) : 2 ≤ Fintype.card (Labels j) := by
    rw [hlabel]
    have hp : 1 ≤ d^j := one_le_pow₀ (by omega : 1 ≤ d)
    rw [pow_succ']
    dsimp [d] at *
    nlinarith
  have hr (j : ℕ) : 1 ≤ r j := endpointCapacity_pos hd hρ (j+1)
  have hk (j : ℕ) : 0 < k j := fiberDimension_pos hd hρ (j+1)
  have hdim (j : ℕ) : FrameParameters.dimension (Fintype.card (Labels j)) (r j) = k j := by
    simp [FrameParameters.dimension, hlabel, k, fiberDimension, r, Nat.cast_pow]
  have hframes (j : ℕ) : ∃ v : Labels j → EuclideanSpace ℂ (Fin (k j)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (min (2*r j) (Fintype.card (Labels j))) 10 := by
    have h := SignMatrix.frames_for_fintype (hn j) (hr j)
    rw [hdim j] at h
    exact h
  choose v hvunit hvframe using hframes
  have hmasks (j : ℕ) : ∃ a : G → Labels j → Bool,
      (∀ x, (rowOnes a x).card ≤ r j) ∧ ∀ y, (columnZeros a (s j) y).card ≤ r j :=
    hmask (j+1) (by omega)
  choose a har hac using hmasks
  let A : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.constant (v j) (s j)
  let T : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.oriented (v j) (s j) (a j)
  have hA (j : ℕ) : A j ∈ KernelObstruction.Commutant := Masked.constant_commutant _ _
  have hrow (j : ℕ) : ‖KernelObstruction.row (T j) 1‖ ≤ 100 := by
    have h := Masked.local_row_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) 1
    norm_num at h
    exact h
  have hcol (j : ℕ) : ‖KernelObstruction.col (A j-T j) 1‖ ≤ 100 := by
    have h := Masked.local_column_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (hac j) 1
    norm_num at h
    exact h
  have hdiff (j : ℕ) (g : G) : ‖coboundary KernelObstruction.translation (T j) g‖ ≤ 100 := by
    have h := Masked.difference_norm_le (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) (hac j) g
    norm_num at h
    exact h
  have henergy (j : ℕ) : (d : ℝ)^(j+1) ≤ KernelObstruction.energy (A j) := by
    have h := Masked.constant_energy_ge_card (v j) (hvunit j) (s j)
    rw [hlabel] at h
    simpa only [Nat.cast_pow] using h
  have hratio : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop := by
    have hbase := (reciprocal_dimension_ratio_tendsto hd hρ hρ1).comp (tendsto_add_atTop_nat 1)
    apply tendsto_atTop_mono _ hbase
    intro j
    exact div_le_div_of_nonneg_right (henergy j) (Nat.cast_nonneg _)
  obtain ⟨π, hπbound, hπnot⟩ := DirectSumObstruction.direct_sum_obstruction k hk A T hA
    (by norm_num : (0 : ℝ) ≤ 100) hrow hcol hdiff hratio
  let : TopologicalSpace.SeparableSpace (DirectSumObstruction.Carrier G k) :=
    DirectSumObstruction.carrier_separable k
  refine ⟨DirectSumObstruction.Carrier G k, inferInstance, inferInstance, inferInstance, inferInstance,
    π, ?_, hπnot⟩
  intro g
  convert hπbound g using 1
  norm_num

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]

theorem solution (hG : ¬ Amenable G) : NonamenableWitness.{u,u} G := by
  first
    | exact OAI.Dixmier.nonamenable_witness hG
    | exact OAI.Dixmier.nonamenable_witness
    | (apply OAI.Dixmier.nonamenable_witness <;> assumption)
    | (intros; apply OAI.Dixmier.nonamenable_witness <;> assumption)
