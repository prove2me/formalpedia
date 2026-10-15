-- Prove2me | solution 1 for OAI.Dixmier.SignMatrix.exists_sign_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:48:14.777092+00:00
-- url     : https://prove2.me/submissions/07b3c02b-c891-42c3-9777-83b79645cae6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FrameSelection.lean:L18-L87
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.SignMatrix.exists_sign_matrix. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_FiniteSigns_two_sided_tail
import Theorems.Thm_OAI_Dixmier_SphereNet_exists_quarter_net
import Theorems.Thm_OAI_Dixmier_SphereNet_operator_norm_le_ten

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

theorem testCoefficients_sq [Nonempty K] (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J)
    (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    ∑ ai, (testCoefficients e w z ai)^2 = 1 / (Fintype.card K : ℝ) := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hw' : ∑ a, (w a)^2 = 1 := by
    have h : ‖w‖^2 = 1 := by rw [hw]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hz' : ∑ j, (z j)^2 = 1 := by
    have h : ‖z‖^2 = 1 := by rw [hz]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  simp only [testCoefficients, Fintype.sum_prod_type, mul_pow,
    div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, sum_extend_sq, hw', hz', mul_one, one_mul]
  rw [inv_pow, Real.sq_sqrt hk.le]

theorem bilinear_test (σ : K × I → Bool) (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J) :
    inner ℝ (synthesis σ e z) w = FiniteSigns.value (testCoefficients e w z) σ := by
  rw [synthesis_apply]
  simp only [sum_inner, inner_smul_left, RCLike.conj_to_real, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Pi.star_apply, star_trivial, vector_apply, FiniteSigns.value, testCoefficients,
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_on_embedding e _ (fun i hi => by rw [extend_off e z i hi]; simp)]
  simp only [extend_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The tail bound for each fixed pair of real unit test vectors and
an injective coordinate selection, on the full sign-matrix sample space. -/
theorem bilinear_tail [Nonempty K] (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J)
    (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    (((univ.filter fun σ : K × I → Bool => (5 : ℝ) < |inner ℝ (synthesis σ e z) w|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card (K × I) ≤ 2 * Real.exp (-(Fintype.card K : ℝ)*25/2) := by
  simp_rw [bilinear_test]
  have h := FiniteSigns.two_sided_tail (k := (Fintype.card K : ℝ)) (u := 5) (testCoefficients e w z)
    (Nat.cast_pos.mpr (Fintype.card_pos (α := K))) (by norm_num : (0 : ℝ) < 5)
    (testCoefficients_sq e w z hw hz)
  convert h using 1 <;> try norm_num
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end SignMatrix
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.FrameSelection ----
namespace OAI

/-! The finite union bound chooses one sign matrix that passes every real
net test for every injective subfamily of the prescribed size. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset

theorem embedding_card_le (n p : ℕ) : Fintype.card (Fin p ↪ Fin n) ≤ n^p := by
  have h := Fintype.card_le_of_injective (fun e : Fin p ↪ Fin n => (e : Fin p → Fin n))
    (by intro e f h; apply Function.Embedding.ext; intro i; exact congrFun h i)
  simpa using h

/-- A real sign-matrix realization for all size-p subfamilies. The proof
uses the actual finite sign sample space, cardinality bounds, and net tests. -/
theorem exists_sign_matrix {n k p : ℕ} (hk : 0 < k)
    (hf : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1) :
    ∃ σ : Fin k × Fin n → Bool, ∀ e : Fin p ↪ Fin n, ‖synthesis σ e‖ ≤ 10 := by
  classical
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨s, hs, hsc, hsnet⟩ := SphereNet.exists_quarter_net (E := EuclideanSpace ℝ (Fin p))
  obtain ⟨t, ht, htc, htnet⟩ := SphereNet.exists_quarter_net (E := EuclideanSpace ℝ (Fin k))
  simp only [finrank_euclideanSpace_fin] at hsc htc
  let Ω := Fin k × Fin n → Bool
  let L := (Fin p ↪ Fin n) × s × t
  let bad : L → Finset Ω := fun l => univ.filter (fun σ =>
    (5 : ℝ) < |inner ℝ (synthesis σ l.1 l.2.1) l.2.2|)
  let B : Finset Ω := univ.biUnion bad
  let N : ℝ := 2 ^ Fintype.card (Fin k × Fin n)
  let q : ℝ := 2 * Real.exp (-25*(k : ℝ)/2)
  have hN : 0 < N := by positivity
  have hq : 0 ≤ q := by positivity
  have hb (l : L) : ((bad l).card : ℝ) ≤ q * N := by
    have h := bilinear_tail l.1 l.2.2 l.2.1 (ht _ l.2.2.2) (hs _ l.2.1.2)
    simp only [Fintype.card_fin] at h
    have he : -(k : ℝ)*25/2 = -25*(k : ℝ)/2 := by ring
    rw [he] at h
    apply (div_le_iff₀ hN).mp
    convert h using 1
    try rfl
    apply congrArg (fun m : ℕ => (m : ℝ) / N)
    apply congrArg Finset.card
    ext σ
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  have hB : (B.card : ℝ) ≤ (Fintype.card L : ℝ) * (q*N) := by
    have hc := Finset.card_biUnion_le (s := (univ : Finset L)) (t := bad)
    calc
      _ ≤ ∑ l : L, ((bad l).card : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ _l : L, q*N := Finset.sum_le_sum (fun l _ => hb l)
      _ = _ := by simp
  have hL : (Fintype.card L : ℝ) ≤ (n : ℝ)^p * 9^p * 9^k := by
    have hc : Fintype.card L = Fintype.card (Fin p ↪ Fin n) * s.card * t.card := by
      simp [L, mul_assoc]
    rw [hc, Nat.cast_mul, Nat.cast_mul]
    exact mul_le_mul (mul_le_mul (by exact_mod_cast embedding_card_le n p) (by exact_mod_cast hsc)
      (by positivity) (by positivity)) (by exact_mod_cast htc) (by positivity) (by positivity)
  have hB' : (B.card : ℝ) < N := by
    have hle := hB.trans (mul_le_mul_of_nonneg_right hL (mul_nonneg hq hN.le))
    have hid : (n : ℝ)^p * 9^p * 9^k * (q*N) =
        (2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2)) * N := by
      dsimp [q]
      rw [pow_add]
      ring
    rw [hid] at hle
    exact hle.trans_lt (by simpa using mul_lt_mul_of_pos_right hf hN)
  have hcard : B.card < (univ : Finset Ω).card := by
    have hNcard : N = (Fintype.card Ω : ℝ) := by simp [N, Ω]
    rw [hNcard] at hB'
    exact_mod_cast hB'
  have hnotall : ∃ σ : Ω, σ ∉ B := by
    by_contra hh
    push Not at hh
    have hle := Finset.card_le_card (show (univ : Finset Ω) ⊆ B from fun σ _ => hh σ)
    omega
  obtain ⟨σ, hnσ⟩ := hnotall
  refine ⟨σ, ?_⟩
  intro e
  apply SphereNet.operator_norm_le_ten (synthesis σ e) s t hs ht hsnet htnet
  intro z hz w hw
  by_contra hnot
  have hbad : σ ∈ bad (e, ⟨z,hz⟩, ⟨w,hw⟩) := by
    exact mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hnot⟩
  exact hnσ (mem_biUnion.mpr ⟨(e, ⟨z,hz⟩, ⟨w,hw⟩), mem_univ _, hbad⟩)

end SignMatrix
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.SignMatrix
open Finset

theorem solution {n k p : ℕ} (hk : 0 < k)
    (hf : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1) :
    ∃ σ : Fin k × Fin n → Bool, ∀ e : Fin p ↪ Fin n, ‖synthesis σ e‖ ≤ 10 := by
  first
    | exact OAI.Dixmier.SignMatrix.exists_sign_matrix hk hf
    | exact OAI.Dixmier.SignMatrix.exists_sign_matrix
    | (apply OAI.Dixmier.SignMatrix.exists_sign_matrix <;> assumption)
    | (intros; apply OAI.Dixmier.SignMatrix.exists_sign_matrix <;> assumption)
