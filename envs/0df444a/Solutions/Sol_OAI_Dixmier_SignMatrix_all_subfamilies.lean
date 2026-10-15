-- Prove2me | solution 1 for OAI.Dixmier.SignMatrix.all_subfamilies
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:08.698019+00:00
-- url     : https://prove2.me/submissions/6de9124c-9fd7-4957-969f-01dd3369eeec

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Frames.lean:L41-L68
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.SignMatrix.all_subfamilies. The node keeps its source
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

-- ---- from OAI.Analysis.Unitarizability.SignMatrix ----
namespace OAI

/-! Normalized sign matrices and their finite-dimensional bilinear
tests. The coordinate selections are injective and retain label identities. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
attribute [local instance] OAI.Dixmier.SignMatrix.instDecidableEq_oAI_2
theorem sum_on_embedding {R : Type*} [AddCommMonoid R] (e : J ↪ I) (f : I → R)
    (hf : ∀ i, (¬ ∃ j, e j = i) → f i = 0) : ∑ i, f i = ∑ j, f (e j) := by
  calc
    _ = ∑ i ∈ univ.map e, f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hn
      apply hf i
      simpa using hn
    _ = _ := by rw [Finset.sum_map]

omit [Fintype I] [Fintype J] in
theorem extend_off (e : J ↪ I) (z : J → ℝ) (i : I) (hi : ¬ ∃ j, e j = i) : extend e z i = 0 :=
  Function.extend_apply' z _ i hi

theorem sum_extend_sq (e : J ↪ I) (z : J → ℝ) : ∑ i, (extend e z i)^2 = ∑ j, (z j)^2 := by
  rw [sum_on_embedding e _ (fun i hi => by rw [extend_off e z i hi]; simp)]
  simp only [extend_apply]

end SignMatrix
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.ComplexFrames ----
namespace OAI

/-! Complexification preserves real synthesis norm bounds.
The real and imaginary coefficient vectors are handled separately. -/
noncomputable section
namespace Dixmier
namespace ComplexFrames
open Finset
variable {I K : Type*} [Fintype K]
theorem norm_sq_split (z : EuclideanSpace ℂ K) :
    ‖z‖^2 = ‖realPart z‖^2 + ‖imagPart z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, realPart, imagPart,
    Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem synthesis_realPart (v : I → EuclideanSpace ℝ K) (J : Finset I) (z : EuclideanSpace ℂ J) :
    realPart (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z) =
      ∑ i : J, (realPart z) i • v i := by
  ext a
  simp only [FiniteSynthesis.synthesis_apply, realPart, ofReal, WithLp.ofLp_toLp,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem synthesis_imagPart (v : I → EuclideanSpace ℝ K) (J : Finset I) (z : EuclideanSpace ℂ J) :
    imagPart (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z) =
      ∑ i : J, (imagPart z) i • v i := by
  ext a
  simp only [FiniteSynthesis.synthesis_apply, imagPart, ofReal, WithLp.ofLp_toLp,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Complex.im_sum,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

theorem synthesis_bound (v : I → EuclideanSpace ℝ K) (J : Finset I) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ z : EuclideanSpace ℝ J, ‖∑ i : J, z i • v i‖ ≤ b*‖z‖) :
    ‖FiniteSynthesis.synthesis (fun i => ofReal (v i)) J‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro z
  have hr := pow_le_pow_left₀ (norm_nonneg _) (h (realPart z)) 2
  have hi := pow_le_pow_left₀ (norm_nonneg _) (h (imagPart z)) 2
  have hsq : ‖FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z‖^2 ≤ b^2*‖z‖^2 := by
    rw [norm_sq_split, synthesis_realPart, synthesis_imagPart, norm_sq_split z]
    nlinarith [hr, hi]
  nlinarith [norm_nonneg (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z),
    norm_nonneg z, mul_nonneg hb (norm_nonneg z)]

end ComplexFrames
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Frames ----
namespace OAI

/-! Frame existence with prescribed dimensions and bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
theorem extendVector_norm (e : J ↪ L) (z : EuclideanSpace ℝ J) : ‖extendVector e z‖ = ‖z‖ := by
  have h : ‖extendVector e z‖^2 = ‖z‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, extendVector, Real.norm_eq_abs, sq_abs]
    exact sum_extend_sq e z
  nlinarith [norm_nonneg (extendVector e z), norm_nonneg z]

omit [Fintype I] in
theorem synthesis_extendVector (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L)
    (z : EuclideanSpace ℝ J) : synthesis σ e (extendVector f z) = synthesis σ (f.trans e) z := by
  simp only [synthesis_apply, extendVector]
  rw [sum_on_embedding f _ (fun i hi => by rw [extend_off f z i hi]; simp)]
  simp only [extend_apply, Function.Embedding.trans_apply]

omit [Fintype I] in
theorem synthesis_restrict_norm (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L) :
    ‖synthesis σ (f.trans e)‖ ≤ ‖synthesis σ e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  rw [← synthesis_extendVector]
  exact ((synthesis σ e).le_opNorm _).trans_eq (by rw [extendVector_norm])

/-- Extend each smaller subset to size p, then restrict a coordinate synthesis operator. -/
theorem all_subfamilies {k p : ℕ} (hp : p ≤ Fintype.card I) (σ : Fin k × I → Bool)
    (hσ : ∀ e : Fin p ↪ I, ‖synthesis σ e‖ ≤ 10) :
    ∀ J : Finset I, J.card ≤ p →
      ‖FiniteSynthesis.synthesis (fun i => ComplexFrames.ofReal (vector σ i)) J‖ ≤ 10 := by
  classical
  intro J hJ
  obtain ⟨L, hJL, hLu, hLc⟩ := Finset.exists_subsuperset_card_eq (s := J) (t := univ)
    (Finset.subset_univ _) hJ (by simpa using hp)
  let eL : L ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  let q : L ≃ Fin p := L.equivFinOfCardEq hLc
  let e : Fin p ↪ I := q.symm.toEmbedding.trans eL
  have he : q.toEmbedding.trans e = eL := by ext i; simp [e]
  have hL : ‖synthesis σ eL‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ e q.toEmbedding
    rw [he] at h
    exact h.trans (hσ e)
  let f : J ↪ L := ⟨fun i => ⟨i.1, hJL i.2⟩, by intro a b h; exact Subtype.ext (congrArg (fun x : L => (x : I)) h)⟩
  let eJ : J ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hf : f.trans eL = eJ := by ext i; rfl
  have hJnorm : ‖synthesis σ eJ‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ eL f
    rw [hf] at h
    exact h.trans hL
  apply ComplexFrames.synthesis_bound _ J (by norm_num : (0 : ℝ) ≤ 10)
  intro z
  have h := (synthesis σ eJ).le_of_opNorm_le hJnorm z
  simpa only [synthesis_apply, eJ, Function.Embedding.coeFn_mk] using h

end SignMatrix
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
private noncomputable local instance instDecidableEq_oAI_3 : DecidableEq I := Classical.decEq I
private noncomputable local instance instDecidableEq_oAI_4 : DecidableEq J := Classical.decEq J
private noncomputable local instance instDecidableEq_oAI_5 : DecidableEq L := Classical.decEq L
private noncomputable local instance instDecidableEq_oAI_6 : DecidableEq K := Classical.decEq K

theorem solution {k p : ℕ} (hp : p ≤ Fintype.card I) (σ : Fin k × I → Bool)
    (hσ : ∀ e : Fin p ↪ I, ‖synthesis σ e‖ ≤ 10) :
    ∀ J : Finset I, J.card ≤ p →
      ‖FiniteSynthesis.synthesis (fun i => ComplexFrames.ofReal (vector σ i)) J‖ ≤ 10 := by
  first
    | exact OAI.Dixmier.SignMatrix.all_subfamilies hp σ hσ
    | exact OAI.Dixmier.SignMatrix.all_subfamilies
    | (apply OAI.Dixmier.SignMatrix.all_subfamilies <;> assumption)
    | (intros; apply OAI.Dixmier.SignMatrix.all_subfamilies <;> assumption)
