-- Prove2me | solution 1 for OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:59:20.359179+00:00
-- url     : https://prove2.me/submissions/990c8b3c-ed41-4364-ab8a-b19761684daf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SumObstruction.lean:L25-L71
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_Triangular_implementer_of_similar
import Theorems.Thm_OAI_Dixmier_equal_coboundaries_iff_commute_sub

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

theorem coefficients_norm_sq (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B‖^2 = ∑ b : K, ‖B (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, coefficients_apply]
  exact Finset.sum_comm

theorem space_summable (ξ : Space G K) : Summable (fun x => ‖ξ x‖^2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem column_summable (L : Fibre K →L[ℂ] Space G K) :
    Summable (fun x => ‖coefficients ((evaluation x).comp L)‖^2) := by
  simp_rw [coefficients_norm_sq]
  exact summable_sum (fun b _ => space_summable (L (EuclideanSpace.basisFun K ℂ b)))

theorem column_energy (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 =
      ∑ b : K, ‖L (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp_rw [coefficients_norm_sq]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro b hb
    exact (space_norm_sq _).symm
  · intro b hb
    exact space_summable _

theorem column_energy_le (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 ≤
      (Fintype.card K : ℝ) * ‖L‖^2 := by
  rw [column_energy]
  calc
    _ ≤ ∑ b : K, ‖L‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have h := L.le_opNorm (EuclideanSpace.basisFun K ℂ b)
      simp only [(EuclideanSpace.basisFun K ℂ).norm_eq_one, mul_one] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by simp [nsmul_eq_mul]

theorem coefficients_adjoint_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B.adjoint (a,b) = conj (coefficients B (b,a)) := by
  simp only [coefficients_apply]
  rw [← EuclideanSpace.basisFun_inner, ← EuclideanSpace.basisFun_inner]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem coefficients_adjoint_norm (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B.adjoint‖ = ‖coefficients B‖ := by
  have h : ‖coefficients B.adjoint‖^2 = ‖coefficients B‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      coefficients_adjoint_apply, RCLike.norm_conj]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (coefficients B.adjoint), norm_nonneg (coefficients B)]

theorem row_block_norm (R : Space G K →L[ℂ] Fibre K) (x : G) :
    ‖coefficients (R.comp (inclusion x))‖ =
      ‖coefficients ((evaluation x).comp R.adjoint)‖ := by
  rw [← coefficients_adjoint_norm (R.comp (inclusion x)),
    ContinuousLinearMap.adjoint_comp, inclusion_adjoint]

theorem row_summable (R : Space G K →L[ℂ] Fibre K) :
    Summable (fun x => ‖coefficients (R.comp (inclusion x))‖^2) := by
  simp_rw [row_block_norm]
  exact column_summable R.adjoint

theorem row_energy_le (R : Space G K →L[ℂ] Fibre K) :
    ∑' x, ‖coefficients (R.comp (inclusion x))‖^2 ≤
      (Fintype.card K : ℝ) * ‖R‖^2 := by
  simp_rw [row_block_norm]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using column_energy_le R.adjoint

variable [Group G]

theorem block_invariant {F : Op G K} (hF : F ∈ Commutant) (g x y : G) :
    block F (g*x) (g*y) = block F x y := by
  ext v a
  have h := congrArg (fun B : Op G K => B (inclusion y v) (g*x)) (hF g).eq
  simp only [mul_apply_eq_comp, translation_inclusion, translation_apply,
    inv_mul_cancel_left] at h
  exact congrArg (fun v : Fibre K => v a) h

theorem block_kernel {F : Op G K} (hF : F ∈ Commutant) (x y : G) :
    block F x y = block F 1 (x⁻¹*y) := by
  simpa only [mul_one, mul_inv_cancel_left] using block_invariant hF x 1 (x⁻¹*y)

theorem commutant_sub {A C : Op G K} (hA : A ∈ Commutant) (hC : C ∈ Commutant) :
    A-C ∈ Commutant := by
  intro g
  change (A-C) * translation g = translation g * (A-C)
  simp only [sub_mul, mul_sub, (hA g).eq, (hC g).eq]

theorem energy_summable (A : Op G K) :
    Summable (fun s => ‖coefficients (block A 1 s)‖^2) :=
  row_summable (row A 1)

theorem energy_le_row (A : Op G K) :
    energy A ≤ (Fintype.card K : ℝ) * ‖row A 1‖^2 :=
  row_energy_le (row A 1)

theorem energy_eq_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A = ∑' x, ‖coefficients ((evaluation x).comp (col A 1))‖^2 := by
  change (∑' s, ‖coefficients (block A 1 s)‖^2) = ∑' x, ‖coefficients (block A x 1)‖^2
  simp_rw [block_kernel hA _ 1, mul_one]
  exact ((Equiv.inv G).tsum_eq (fun s => ‖coefficients (block A 1 s)‖^2)).symm

theorem energy_le_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A ≤ (Fintype.card K : ℝ) * ‖col A 1‖^2 := by
  rw [energy_eq_column hA]
  exact column_energy_le _

omit [Group G] in
theorem row_norm_le (F : Op G K) (x : G) : ‖row F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (evaluation_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem col_norm_le (F : Op G K) (x : G) : ‖col F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (inclusion_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem row_difference_bound (T C : Op G K) (x : G) :
    ‖row C x‖ ≤ ‖row T x‖ + ‖T-C‖ := by
  have h : row C x = row T x - row (T-C) x := by ext v a; simp [row]
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) (row_norm_le _ _))

omit [Group G] in
theorem col_difference_bound (A T C : Op G K) (x : G) :
    ‖col (A-C) x‖ ≤ ‖col (A-T) x‖ + ‖T-C‖ := by
  have h : col (A-C) x = col (A-T) x + col (T-C) x := by
    ext v y a
    simp [col]
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (le_refl _) (col_norm_le _ _))

theorem energy_split_le (A C : Op G K) : energy A ≤ 2 * energy C + 2 * energy (A-C) := by
  have hp (s : G) : ‖coefficients (block A 1 s)‖^2 ≤
      2 * ‖coefficients (block C 1 s)‖^2 + 2 * ‖coefficients (block (A-C) 1 s)‖^2 := by
    rw [block_sub, coefficients_sub]
    have ht := norm_add_le (coefficients (block C 1 s))
      (coefficients (block A 1 s) - coefficients (block C 1 s))
    rw [add_sub_cancel] at ht
    nlinarith [norm_nonneg (coefficients (block A 1 s)),
      norm_nonneg (coefficients (block C 1 s)),
      norm_nonneg (coefficients (block A 1 s) - coefficients (block C 1 s)),
      sq_nonneg (‖coefficients (block C 1 s)‖ -
        ‖coefficients (block A 1 s) - coefficients (block C 1 s)‖)]
  have hs := ((energy_summable C).mul_left 2).add ((energy_summable (A-C)).mul_left 2)
  have h := (energy_summable A).tsum_le_tsum hp hs
  rw [((energy_summable C).mul_left 2).tsum_add ((energy_summable (A-C)).mul_left 2),
    tsum_mul_left, tsum_mul_left] at h
  exact h

/-- The kernel-energy obstruction, proved from coordinate estimates and commutation. -/
theorem kernel_obstruction {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (_hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ)
    {C : Op G K} (hC : C ∈ Commutant) :
    energy A ≤ 4 * (Fintype.card K : ℝ) * (κ + ‖T-C‖)^2 := by
  have hR : ‖row C 1‖ ≤ κ + ‖T-C‖ :=
    (row_difference_bound T C 1).trans (add_le_add hr (le_refl _))
  have hL : ‖col (A-C) 1‖ ≤ κ + ‖T-C‖ :=
    (col_difference_bound A T C 1).trans (add_le_add hc (le_refl _))
  have heC := (energy_le_row C).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hR 2) (Nat.cast_nonneg (Fintype.card K)))
  have heAC := (energy_le_column (commutant_sub hA hC)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hL 2) (Nat.cast_nonneg (Fintype.card K)))
  nlinarith [energy_split_le A C]

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

theorem conjugate_mul (U : G →* R) (g h : G) (T : R) :
    conjugate U (g * h) T = conjugate U g (conjugate U h T) := by
  simp [conjugate, map_mul, mul_assoc]

theorem conjugate_sub (U : G →* R) (g : G) (A B : R) :
    conjugate U g (A - B) = conjugate U g A - conjugate U g B := by
  simp [conjugate, mul_sub, sub_mul]

/-- The coboundary cocycle identity, before taking direct sums. -/
theorem coboundary_cocycle (U : G →* R) (T : R) (g h : G) :
    coboundary U T (g * h) = coboundary U T g + conjugate U g (coboundary U T h) := by
  simp only [coboundary, conjugate_mul, conjugate_sub]
  abel

end Ring
end Dixmier

end OAI

-- ---- from OAI.Analysis.Unitarizability.HilbertSum ----
namespace OAI

/-! Uniformly bounded Hilbert direct sums. The component implementers
are never summed and need not be uniformly bounded. -/
noncomputable section
namespace Dixmier
namespace HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
attribute [local instance] OAI.Dixmier.HilbertSum.instDecidableEq_oAI
theorem boundedSum_norm_le (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) : ‖boundedSum T hκ hT‖ ≤ κ :=
  lp.norm_mapCLM_le 2 T hκ hT

theorem representation_norm_map (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) :
    ‖representation U hU g x‖ = ‖x‖ := by
  have hs : ‖representation U hU g x‖^2 = ‖x‖^2 := by
    have norm_sq (y : Space E) : ‖y‖^2 = ∑' i, ‖y i‖^2 := by
      simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) y
    simp only [norm_sq, representation_apply, hU]
  nlinarith [norm_nonneg (representation U hU g x), norm_nonneg x]

theorem cocycle_one (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (h1 : ∀ i, D i 1 = 0) :
    cocycle D hκ hb 1 = 0 := by ext x i; simp [h1]

theorem cocycle_identity (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ)
    (hD : ∀ i g h, D i (g*h) = D i g + conjugate (U i) g (D i h)) (g h : G) :
    cocycle D hκ hb (g*h) = cocycle D hκ hb g +
      conjugate (representation U hU) g (cocycle D hκ hb h) := by
  ext x i
  change D i (g*h) (x i) = D i g (x i) + U i g (D i h (U i g⁻¹ (x i)))
  rw [hD]
  rfl

theorem representation_inclusion (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (i : I) (x : E i) :
    representation U hU g (inclusion i x) = inclusion i (U i g x) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

theorem compression_norm_le (B : Space E →L[ℂ] Space E) (i : I) : ‖compression B i‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  change ‖B (lp.single 2 i x) i‖ ≤ ‖B‖ * ‖x‖
  calc
    _ ≤ ‖B (lp.single 2 i x)‖ := lp.norm_apply_le_norm (by norm_num) _ i
    _ ≤ ‖B‖ * ‖lp.single 2 i x‖ := B.le_opNorm _
    _ = _ := by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem compression_conjugate (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (B : Space E →L[ℂ] Space E) (i : I) (g : G) :
    compression (conjugate (representation U hU) g B) i =
      conjugate (U i) g (compression B i) := by
  ext x
  change (representation U hU g (B (representation U hU g⁻¹ (inclusion i x)))) i = _
  rw [representation_inclusion, representation_apply]
  rfl

theorem compression_implementer (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (B : Space E →L[ℂ] Space E)
    (hB : ∀ g, cocycle D hκ hb g = coboundary (representation U hU) B g) (i : I) (g : G) :
    D i g = coboundary (U i) (compression B i) g := by
  have h := congrArg (fun T => compression T i) (hB g)
  have hc : compression (cocycle D hκ hb g) i = D i g := by
    ext x
    change D i g (lp.single 2 i x i) = D i g x
    rw [lp.single_apply_self]
  have hs (A C : Space E →L[ℂ] Space E) : compression (A-C) i = compression A i - compression C i := by
    ext x; rfl
  rwa [hc, coboundary, hs, compression_conjugate] at h

end HilbertSum
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Triangular ----
namespace OAI

/-! Bounded Hilbert sums and triangular representations. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem diagonal_norm_map (U : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) (x : Double H) :
    ‖diagonal U x‖ = ‖x‖ := by
  have h : ‖diagonal U x‖^2 = ‖x‖^2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, diagonal_fst, diagonal_snd, hU]
  nlinarith [norm_nonneg (diagonal U x), norm_nonneg x]

theorem operator_norm_le (U D : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) :
    ‖operator U D‖ ≤ 1 + ‖D‖ := by
  have hd : ‖diagonal U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [diagonal_norm_map U hU]
  have hn : ‖inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))‖ ≤ ‖D‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro x
    change ‖inl (D (U x.snd))‖ ≤ ‖D‖ * ‖x‖
    rw [inl_norm]
    calc
      ‖D (U x.snd)‖ ≤ ‖D‖ * ‖U x.snd‖ := D.le_opNorm _
      _ = ‖D‖ * ‖x.snd‖ := by rw [hU]
      _ ≤ ‖D‖ * ‖x‖ := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le H x) (norm_nonneg D)
  exact (norm_add_le (diagonal U) (inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H))))).trans
    (add_le_add hd hn)

theorem representation_bound (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) {κ : ℝ} (hb : ∀ g, ‖D g‖ ≤ κ) (g : G) :
    ‖representation U D h1 hD g‖ ≤ 1 + κ :=
  (operator_norm_le (U g) (D g) (hU g)).trans (add_le_add (le_refl _) (hb g))

end Triangular
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

theorem stage_unitary (k : ℕ → ℕ) (j : ℕ) (g : G) (x : Stage G k j) :
    ‖KernelObstruction.translation g x‖ = ‖x‖ :=
  KernelObstruction.reindex_norm (Equiv.mulLeft g⁻¹) x

/-- The direct-sum obstruction with its representation and bound.
The stage operators A_j and T_j need not be uniformly bounded. -/
theorem direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π := by
  let U : ∀ j, G →* (Stage G k j →L[ℂ] Stage G k j) := fun _ => KernelObstruction.translation
  have hU : ∀ j g x, ‖U j g x‖ = ‖x‖ := stage_unitary k
  let D : ∀ j, G → (Stage G k j →L[ℂ] Stage G k j) := fun j => coboundary (U j) (T j)
  have h1 : ∀ j, D j 1 = 0 := fun j => coboundary_one (U j) (T j)
  have hD : ∀ j g h, D j (g*h) = D j g + conjugate (U j) g (D j h) :=
    fun j => coboundary_cocycle (U j) (T j)
  let V := HilbertSum.representation U hU
  let δ := HilbertSum.cocycle D hκ hb
  have hδ1 : δ 1 = 0 := HilbertSum.cocycle_one D hκ hb h1
  have hδ : ∀ g h, δ (g*h) = δ g + conjugate V g (δ h) :=
    HilbertSum.cocycle_identity U hU D hκ hb hD
  let π := Triangular.representation V δ hδ1 hδ
  have hδb : ∀ g, ‖δ g‖ ≤ κ := fun g => HilbertSum.boundedSum_norm_le _ hκ _
  refine ⟨π, Triangular.representation_bound V δ hδ1 hδ
    (HilbertSum.representation_norm_map U hU) hδb, ?_⟩
  intro hπ
  rcases Triangular.implementer_of_similar V δ hδ1 hδ hπ with ⟨B, hB⟩
  have hbound (j : ℕ) : KernelObstruction.energy (A j) / k j ≤ 4 * (κ + ‖B‖)^2 := by
    let Bj := HilbertSum.compression B j
    have hBj (g : G) : D j g = coboundary (U j) Bj g :=
      HilbertSum.compression_implementer U hU D hκ hb B hB j g
    have hC : T j - Bj ∈ KernelObstruction.Commutant := by
      intro g
      exact ((equal_coboundaries_iff_commute_sub (U j) (T j) Bj g).mp (hBj g)).symm
    have henergy := KernelObstruction.kernel_obstruction (hA j) hκ (hr j) (hc j) hC
    simp only [Fintype.card_fin, sub_sub_cancel] at henergy
    have hnorm : ‖Bj‖ ≤ ‖B‖ := HilbertSum.compression_norm_le B j
    have hs : (κ + ‖Bj‖)^2 ≤ (κ + ‖B‖)^2 :=
      pow_le_pow_left₀ (add_nonneg hκ (norm_nonneg _)) (add_le_add (le_refl _) hnorm) 2
    have henergy' : KernelObstruction.energy (A j) ≤ 4 * (k j : ℝ) * (κ + ‖B‖)^2 :=
      henergy.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hk j))).mpr
    nlinarith [henergy']
  obtain ⟨j, hj⟩ := (he.eventually (eventually_gt_atTop (4 * (κ + ‖B‖)^2))).exists
  exact (not_lt_of_ge (hbound j)) hj

end DirectSumObstruction
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

theorem solution (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π := by
  first
    | exact OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction k hk A T hA hκ hr hc hb he
    | exact OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction
    | (apply OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction <;> assumption)
    | (intros; apply OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction <;> assumption)
