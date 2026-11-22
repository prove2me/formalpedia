-- Prove2me | solution 1 for MasulloRepair.hilbertSchmidt_comp_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T20:06:43.991509+00:00
-- url     : https://prove2.me/submissions/846c7934-2b85-4024-a818-58c462de88cd

import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 800000

open MasulloGRH ContinuousLinearMap
open scoped InnerProductSpace

-- Basis countability and Parseval follow marozols's accepted kernel proof
-- 6bbec8a8-12d8-421e-9b7e-56b5183db337, with the nuclear product argument supplied here.
private theorem basis_countable {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (b : HilbertBasis ι ℂ H) : Countable ι := by
  have hd : Pairwise (Function.onFun Disjoint (fun i => Metric.ball (b i) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have hsq := norm_sub_sq (𝕜 := ℂ) (b i) (b j)
    rw [b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one,
      b.orthonormal.inner_eq_zero hij] at hsq
    norm_num at hsq
    nlinarith [norm_nonneg (b i - b j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)

private theorem parseval_norm {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖inner ℂ x (b i)‖ ^ 2) (‖x‖ ^ 2) := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner x x)
  rw [inner_self_eq_norm_sq_to_K] at h
  convert! h using 1
  · funext i
    rw [← inner_conj_symm (b i) x, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  · change ‖x‖ ^ 2 = ((‖x‖ : ℂ) ^ 2).re
    simp [pow_two, Complex.mul_re]

private theorem adjoint_energy {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hs : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    Summable (fun i => ‖T.adjoint (b i)‖ ^ 2) ∧
      (∑' i, ‖T.adjoint (b i)‖ ^ 2) = ∑' i, ‖T (b i)‖ ^ 2 := by
  let f : ι × ι → ℝ := fun p => ‖inner ℂ (T (b p.1)) (b p.2)‖ ^ 2
  have hrow (i : ι) : HasSum (fun j => f (i, j)) (‖T (b i)‖ ^ 2) :=
    parseval_norm b (T (b i))
  have hcol (j : ι) : HasSum (fun i => f (i, j)) (‖T.adjoint (b j)‖ ^ 2) := by
    have heq : (fun i => f (i, j)) =
        (fun i => ‖inner ℂ (T.adjoint (b j)) (b i)‖ ^ 2) := by
      funext i
      change ‖inner ℂ (T (b i)) (b j)‖ ^ 2 = _
      rw [← adjoint_inner_right, norm_inner_symm]
    rw [heq]
    exact parseval_norm b (T.adjoint (b j))
  have hf : Summable f := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i => ∑' j, f (i, j)) = (fun i => ‖T (b i)‖ ^ 2) :=
      funext fun i => (hrow i).tsum_eq
    rw [heq]
    exact hs
  constructor
  · have h := hf.prod_symm.prod
    change Summable (fun j => ∑' i, f (i, j)) at h
    have heq : (fun j => ∑' i, f (i, j)) = (fun j => ‖T.adjoint (b j)‖ ^ 2) :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq] at h
  · calc
      _ = ∑' j, ∑' i, f (i, j) := tsum_congr fun j => (hcol j).tsum_eq.symm
      _ = ∑' i, ∑' j, f (i, j) :=
        Summable.tsum_comm (f := fun i j => f (i, j)) hf
      _ = _ := tsum_congr fun i => (hrow i).tsum_eq

private theorem nuclear_of_countable_series {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (T : H →L[ℂ] H) (x y : ι → H)
    (hs : Summable (fun i => ‖x i‖ * ‖y i‖))
    (hxy : ∀ u, HasSum (fun i => inner ℂ (x i) u • y i) (T u)) :
    IsNuclearOperator T ∧ traceNorm T ≤ ∑' i, ‖x i‖ * ‖y i‖ := by
  classical
  letI : Encodable ι := Encodable.ofCountable ι
  let e : ι → ℕ := Encodable.encode
  have he : Function.Injective e := Encodable.encode_injective
  let x' : ℕ → H := Function.extend e x 0
  let y' : ℕ → H := Function.extend e y 0
  have hcost : (fun n => ‖x' n‖ * ‖y' n‖) =
      Function.extend e (fun i => ‖x i‖ * ‖y i‖) 0 := by
    funext n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      simp only [x', y', he.extend_apply]
    · simp only [x', y', Function.extend_apply' _ _ _ hn, Pi.zero_apply,
        norm_zero, zero_mul]
  have hsc : Summable (fun n => ‖x' n‖ * ‖y' n‖) := by
    rw [hcost]
    exact (summable_extend_zero he).mpr hs
  have hrep (u : H) : HasSum (fun n => inner ℂ (x' n) u • y' n) (T u) := by
    have heq : (fun n => inner ℂ (x' n) u • y' n) =
        Function.extend e (fun i => inner ℂ (x i) u • y i) 0 := by
      funext n
      by_cases hn : ∃ i, e i = n
      · obtain ⟨i, rfl⟩ := hn
        simp only [x', y', he.extend_apply]
      · simp only [x', y', Function.extend_apply' _ _ _ hn, Pi.zero_apply,
          inner_zero_left, zero_smul]
    rw [heq]
    exact (hasSum_extend_zero he).mpr (hxy u)
  refine ⟨⟨x', y', hsc, hrep⟩, ?_⟩
  have h := traceNorm_le_nuclear_series T x' y' hsc hrep
  rwa [hcost, tsum_extend_zero he] at h

theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (A B : H →L[ℂ] H) (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsNuclearOperator (A ∘L B) ∧
      traceNorm (A ∘L B) ≤ hilbertSchmidtNorm A * hilbertSchmidtNorm B := by
  classical
  let b := chosenHilbertBasis H
  letI : Countable (exists_hilbertBasis ℂ H).choose := basis_countable b
  have hA' : Summable (fun i => ‖A (b i)‖ ^ 2) := hA
  obtain ⟨hB', hBeq⟩ := adjoint_energy b B hB
  have hbound (s : Finset (exists_hilbertBasis ℂ H).choose) :
      ∑ i ∈ s, ‖B.adjoint (b i)‖ * ‖A (b i)‖ ≤
        Real.sqrt (∑' i, ‖B.adjoint (b i)‖ ^ 2) *
          Real.sqrt (∑' i, ‖A (b i)‖ ^ 2) := by
    apply (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · exact Real.sqrt_le_sqrt (hB'.sum_le_tsum s (fun _ _ => sq_nonneg _))
    · exact Real.sqrt_le_sqrt (hA'.sum_le_tsum s (fun _ _ => sq_nonneg _))
  have hs : Summable (fun i => ‖B.adjoint (b i)‖ * ‖A (b i)‖) :=
    summable_of_sum_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
  have hrep (u : H) : HasSum (fun i => inner ℂ (B.adjoint (b i)) u • A (b i))
      ((A ∘L B) u) := by
    have h := (b.hasSum_repr (B u)).mapL A
    simpa only [map_smul, HilbertBasis.repr_apply_apply, adjoint_inner_left,
      ContinuousLinearMap.comp_apply] using h
  obtain ⟨hn, hnorm⟩ := nuclear_of_countable_series (A ∘L B)
    (fun i => B.adjoint (b i)) (fun i => A (b i)) hs hrep
  refine ⟨hn, hnorm.trans ?_⟩
  have htotal : (∑' i, ‖B.adjoint (b i)‖ * ‖A (b i)‖) ≤
      Real.sqrt (∑' i, ‖B.adjoint (b i)‖ ^ 2) *
        Real.sqrt (∑' i, ‖A (b i)‖ ^ 2) := Real.tsum_le_of_sum_le
    (fun i => mul_nonneg (norm_nonneg (B.adjoint (b i))) (norm_nonneg (A (b i)))) hbound
  rw [hBeq] at htotal
  change (∑' i, ‖B.adjoint (b i)‖ * ‖A (b i)‖) ≤
    Real.sqrt (∑' i, ‖A (b i)‖ ^ 2) * Real.sqrt (∑' i, ‖B (b i)‖ ^ 2)
  exact htotal.trans_eq (mul_comm _ _)

#print axioms solution
