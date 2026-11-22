-- Prove2me | solution 1 for MasulloGRH.traceNorm_norm_properties
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:47:02.332523+00:00
-- url     : https://prove2.me/submissions/372322e5-b359-4ea1-91e6-c6180ed858b1

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear
import Theorems.Thm_MasulloGRH_nuclear_trace_hasSum_hilbertBasis

open Filter Topology MeasureTheory
set_option autoImplicit false

namespace Sol_MasulloGRH_traceNorm_norm_properties

open MasulloGRH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If `‖A x‖ ≤ ‖T x‖` for all `x`, then `A = S T` for a contraction `S`. -/
theorem exists_contraction_mul_eq_of_norm_le
    (T A : H →L[ℂ] H) (h : ∀ x, ‖A x‖ ≤ ‖T x‖) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ 1 ∧ S * T = A := by
  let K := (LinearMap.range T.toLinearMap).topologicalClosure
  let e : H →ₗ[ℂ] K := T.toLinearMap.codRestrict K fun x ↦
    (LinearMap.range T.toLinearMap).le_topologicalClosure (LinearMap.mem_range_self _ x)
  have he : DenseRange e := by
    apply Topology.IsInducing.subtypeVal.dense_iff.mpr
    intro x
    rw [← Set.range_comp]
    exact x.property
  have hbound (x : H) : ‖A.toLinearMap x‖ ≤ 1 * ‖e x‖ := by
    rw [one_mul, ← Submodule.norm_coe]
    exact h x
  let S := A.toLinearMap.extendOfNorm e
  refine ⟨S.comp K.orthogonalProjectionOnto, ?_, ?_⟩
  · calc
      _ ≤ ‖S‖ * ‖K.orthogonalProjectionOnto‖ := S.opNorm_comp_le _
      _ ≤ 1 * 1 := mul_le_mul (LinearMap.opNorm_extendOfNorm_le he zero_le_one hbound)
        K.orthogonalProjectionOnto_norm_le (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · ext x
    change S (K.orthogonalProjectionOnto (e x : H)) = A x
    rw [K.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact LinearMap.extendOfNorm_eq he ⟨1, hbound⟩ x

theorem nuclear_mul_left (U T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsNuclearOperator (U * T) := by
  obtain ⟨x, y, hs, hxy⟩ := hT
  refine ⟨x, fun m => U (y m), ?_, fun u => ?_⟩
  · refine (hs.mul_left ‖U‖).of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    calc ‖x m‖ * ‖U (y m)‖ ≤ ‖x m‖ * (‖U‖ * ‖y m‖) := by
          gcongr; exact U.le_opNorm _
      _ = ‖U‖ * (‖x m‖ * ‖y m‖) := by ring
  · have := U.hasSum (hxy u)
    show HasSum _ (U (T u))
    simpa only [map_smul] using this

theorem nuclear_smul (a : ℂ) (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsNuclearOperator (a • T) := by
  obtain ⟨x, y, hs, hxy⟩ := hT
  refine ⟨x, fun m => a • y m, ?_, fun u => ?_⟩
  · refine (hs.mul_left ‖a‖).congr (fun m => ?_)
    rw [norm_smul]; ring
  · have := (hxy u).const_smul a
    rw [smul_apply]
    refine this.congr_fun (fun m => ?_)
    rw [smul_comm]

theorem nuclear_add (S T : H →L[ℂ] H) (hS : IsNuclearOperator S) (hT : IsNuclearOperator T) :
    IsNuclearOperator (S + T) := by
  obtain ⟨x, y, hs, hxy⟩ := hS
  obtain ⟨x', y', hs', hxy'⟩ := hT
  have he (k : ℕ) : (2 * k) % 2 = 0 ∧ (2 * k) / 2 = k := by omega
  have ho (k : ℕ) : ¬ ((2 * k + 1) % 2 = 0) ∧ (2 * k + 1) / 2 = k := by omega
  have interleave (p q : ℕ → H) : ∃ r : ℕ → H, (∀ k, r (2 * k) = p k) ∧ ∀ k, r (2 * k + 1) = q k :=
    ⟨fun n => if n % 2 = 0 then p (n / 2) else q (n / 2),
      fun k => by simp only [if_pos (he k).1, (he k).2],
      fun k => by simp only [if_neg (ho k).1, (ho k).2]⟩
  obtain ⟨z, hz0, hz1⟩ := interleave x x'
  obtain ⟨w, hw0, hw1⟩ := interleave y y'
  refine ⟨z, w, ?_, fun u => ?_⟩
  · have h0 : HasSum (fun k => ‖z (2 * k)‖ * ‖w (2 * k)‖) (∑' m, ‖x m‖ * ‖y m‖) := by
      simpa only [hz0, hw0] using hs.hasSum
    have h1 : HasSum (fun k => ‖z (2 * k + 1)‖ * ‖w (2 * k + 1)‖) (∑' m, ‖x' m‖ * ‖y' m‖) := by
      simpa only [hz1, hw1] using hs'.hasSum
    exact (HasSum.even_add_odd (f := fun n => ‖z n‖ * ‖w n‖) h0 h1).summable
  · rw [ContinuousLinearMap.add_apply]
    have h0 : HasSum (fun k => inner ℂ (z (2 * k)) u • w (2 * k)) (S u) := by
      simpa only [hz0, hw0] using hxy u
    have h1 : HasSum (fun k => inner ℂ (z (2 * k + 1)) u • w (2 * k + 1)) (T u) := by
      simpa only [hz1, hw1] using hxy' u
    exact HasSum.even_add_odd (f := fun n => inner ℂ (z n) u • w n) h0 h1

theorem abs_nonneg' (T : H →L[ℂ] H) : 0 ≤ operatorAbs T := CFC.sqrt_nonneg _

theorem abs_mul_self (T : H →L[ℂ] H) : operatorAbs T * operatorAbs T = star T * T :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)

theorem abs_adjoint (T : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (operatorAbs T) = operatorAbs T :=
  (IsSelfAdjoint.of_nonneg (abs_nonneg' T)).star_eq

theorem norm_abs_apply (T : H →L[ℂ] H) (x : H) : ‖operatorAbs T x‖ = ‖T x‖ := by
  rw [ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right,
    ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right, abs_adjoint,
    ← ContinuousLinearMap.mul_def, abs_mul_self, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def]

theorem nuclear_abs (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsNuclearOperator (operatorAbs T) := by
  obtain ⟨V, -, hV⟩ := exists_contraction_mul_eq_of_norm_le T (operatorAbs T)
    (fun x => (norm_abs_apply T x).le)
  rw [← hV]
  exact nuclear_mul_left V T hT

theorem hasSum_trace {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (hT : IsNuclearOperator T) :
    HasSum (fun i => inner ℂ (b i) (T (b i))) (operatorTrace T) :=
  (nuclear_trace_hasSum_hilbertBasis T hT b).2

theorem hasSum_re_trace {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (hT : IsNuclearOperator T) :
    HasSum (fun i => (inner ℂ (b i) (T (b i))).re) (operatorTrace T).re :=
  Complex.reCLM.hasSum (hasSum_trace b T hT)

theorem hasSum_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (hT : IsNuclearOperator T) :
    HasSum (fun i => (inner ℂ (b i) (operatorAbs T (b i))).re) (traceNorm T) :=
  hasSum_re_trace b _ (nuclear_abs T hT)

theorem hasSum_norm_sq_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (hT : IsNuclearOperator T) :
    HasSum (fun i => ‖CFC.sqrt (operatorAbs T) (b i)‖ ^ 2) (traceNorm T) := by
  let B := CFC.sqrt (operatorAbs T)
  have hB : ContinuousLinearMap.adjoint B = B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (operatorAbs T))).star_eq
  refine (hasSum_traceNorm b T hT).congr_fun fun i ↦ ?_
  change ‖B (b i)‖ ^ 2 = (inner ℂ (b i) (operatorAbs T (b i))).re
  rw [B.apply_norm_sq_eq_inner_adjoint_right, hB, ← ContinuousLinearMap.mul_def,
    CFC.sqrt_mul_sqrt_self _ (abs_nonneg' T)]
  rfl


set_option maxHeartbeats 800000 in
/-- For a contraction `U`, the real part of the diagonal sum of `U T` is at most `‖T‖_Tr`. -/
theorem exists_hasSum_re_mul_le_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) :
    ∃ r, HasSum (fun i => (inner ℂ (b i) ((U * T) (b i))).re) r ∧ r ≤ traceNorm T := by
  let S := operatorAbs T
  let B := CFC.sqrt S
  have hB : ContinuousLinearMap.adjoint B = B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg S)).star_eq
  have hsq : B * B = S := CFC.sqrt_mul_sqrt_self _ (abs_nonneg' T)
  obtain ⟨W, hW, hWT⟩ := exists_contraction_mul_eq_of_norm_le S T
    (fun x ↦ (norm_abs_apply T x).ge)
  let A := U * W
  have hA : ‖A‖ ≤ 1 :=
    (norm_mul_le U W).trans ((mul_le_of_le_one_left (norm_nonneg W) hU).trans hW)
  have hTs : HasSum (fun i ↦ ‖B (b i)‖ ^ 2) (traceNorm T) := hasSum_norm_sq_traceNorm b T hT
  have hfactor : A * (B * B) = U * T := by
    calc
      A * (B * B) = A * S := by rw [hsq]
      _ = U * (W * S) := mul_assoc U W S
      _ = U * T := by rw [hWT]
  clear_value A B
  have hparseval (x : H) : HasSum (fun i ↦ ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
    simpa [b.repr_apply_apply] using
      (lp.hasSum_norm (p := 2) (by norm_num) (b.repr x))
  -- Summing the squared entries of `A B` by columns and by rows.
  let a (j i : ι) := ‖inner ℂ (b i) (A (B (b j)))‖ ^ 2
  have hcol (j : ι) : HasSum (a j) (‖A (B (b j))‖ ^ 2) := hparseval (A (B (b j)))
  have hbound (j : ι) : ‖A (B (b j))‖ ^ 2 ≤ ‖B (b j)‖ ^ 2 := by
    have h := (ContinuousLinearMap.opNorm_le_iff (show (0 : ℝ) ≤ 1 by norm_num)).mp hA (B (b j))
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (by simpa only [one_mul] using h)
  have ha : Summable (Function.uncurry a) := by
    refine (summable_prod_of_nonneg (fun p ↦ sq_nonneg _)).mpr ⟨fun j ↦ (hcol j).summable, ?_⟩
    refine hTs.summable.of_nonneg_of_le (fun j ↦ tsum_nonneg fun i ↦ sq_nonneg _) (fun j ↦ ?_)
    rw [(hcol j).tsum_eq]
    exact hbound j
  have hrow (i : ι) : HasSum (fun j ↦ a j i)
      (‖B (ContinuousLinearMap.adjoint A (b i))‖ ^ 2) := by
    refine (hparseval (B (ContinuousLinearMap.adjoint A (b i)))).congr_fun fun j ↦ ?_
    change ‖inner ℂ (b i) (A (B (b j)))‖ ^ 2 =
      ‖inner ℂ (b j) (B (ContinuousLinearMap.adjoint A (b i)))‖ ^ 2
    have hentry := ContinuousLinearMap.adjoint_inner_right B (b j)
      (ContinuousLinearMap.adjoint A (b i))
    rw [hB] at hentry
    rw [hentry, ContinuousLinearMap.adjoint_inner_right]
    exact congrArg (fun r : ℝ ↦ r ^ 2) (norm_inner_symm (𝕜 := ℂ) (b i) (A (B (b j))))
  have hrow_sum : Summable (fun i ↦ ‖B (ContinuousLinearMap.adjoint A (b i))‖ ^ 2) :=
    ha.prod_symm.prod.congr fun i ↦ (hrow i).tsum_eq
  have hrow_bound : (∑' i, ‖B (ContinuousLinearMap.adjoint A (b i))‖ ^ 2) ≤ traceNorm T := by
    calc
      _ = ∑' i, ∑' j, a j i := tsum_congr fun i ↦ (hrow i).tsum_eq.symm
      _ = ∑' j, ∑' i, a j i := ha.tsum_comm
      _ ≤ traceNorm T := by
        rw [hTs.tsum_eq.symm]
        exact ha.prod.tsum_le_tsum (fun j ↦ (hcol j).tsum_eq ▸ hbound j) hTs.summable
  have hreal := hasSum_re_trace b _ (nuclear_mul_left U T hT)
  refine ⟨_, hreal, (hasSum_le (fun i ↦ ?_) hreal ((hTs.add hrow_sum.hasSum).div_const 2)).trans ?_⟩
  · rw [← hfactor]
    change (inner ℂ (b i) (A (B (B (b i))))).re ≤ _
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left B, hB]
    exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by
      nlinarith [sq_nonneg (‖B (b i)‖ - ‖B (ContinuousLinearMap.adjoint A (b i))‖)]))
  · linarith

/-- The absolute value scales by the modulus of the scalar. -/
theorem abs_smul' (c : ℂ) (T : H →L[ℂ] H) :
    operatorAbs (c • T) = ‖c‖ • operatorAbs T := by
  unfold operatorAbs
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, ← pow_two, CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T),
      star_smul, smul_mul_smul_comm, ← Complex.coe_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  · exact smul_nonneg (norm_nonneg _) (CFC.sqrt_nonneg _)

end Sol_MasulloGRH_traceNorm_norm_properties

open MasulloGRH in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hS : IsNuclearOperator S) (hT : IsNuclearOperator T) (a : ℂ) :
    IsNuclearOperator (S + T) ∧ IsNuclearOperator (a • T) ∧
      traceNorm (S + T) ≤ traceNorm S + traceNorm T ∧
      traceNorm (a • T) = ‖a‖ * traceNorm T ∧
      0 ≤ traceNorm T ∧ (traceNorm T = 0 ↔ T = 0) ∧
      operatorTrace (S + T) = operatorTrace S + operatorTrace T ∧
      operatorTrace (a • T) = a * operatorTrace T ∧
      ‖operatorTrace T‖ ≤ traceNorm T := by
  open Sol_MasulloGRH_traceNorm_norm_properties in
  let b := chosenHilbertBasis H
  have hST : IsNuclearOperator (S + T) := nuclear_add S T hS hT
  have haT : IsNuclearOperator (a • T) := nuclear_smul a T hT
  refine ⟨hST, haT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- triangle inequality
    obtain ⟨U, hU, hUX⟩ := exists_contraction_mul_eq_of_norm_le (S + T) (operatorAbs (S + T))
      (fun x ↦ (norm_abs_apply (S + T) x).le)
    obtain ⟨r, hr, hrle⟩ := exists_hasSum_re_mul_le_traceNorm b S hS U hU
    obtain ⟨s, hs, hsle⟩ := exists_hasSum_re_mul_le_traceNorm b T hT U hU
    have hsum : HasSum (fun i ↦ (inner ℂ (b i) (operatorAbs (S + T) (b i))).re) (r + s) := by
      refine (hr.add hs).congr_fun fun i ↦ ?_
      rw [← hUX, mul_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    rw [(hasSum_traceNorm b (S + T) hST).unique hsum]
    exact add_le_add hrle hsle
  · -- homogeneity
    refine (hasSum_traceNorm b (a • T) haT).unique
      (((hasSum_traceNorm b T hT).mul_left ‖a‖).congr_fun fun i ↦ ?_)
    rw [abs_smul']
    simp only [ContinuousLinearMap.smul_apply, ← Complex.coe_smul, inner_smul_right,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  · -- nonnegativity
    rw [← (hasSum_norm_sq_traceNorm b T hT).tsum_eq]
    exact tsum_nonneg fun i ↦ sq_nonneg _
  · -- definiteness
    constructor
    · intro hz
      let B := CFC.sqrt (operatorAbs T)
      have hsum : HasSum (fun i ↦ ‖B (b i)‖ ^ 2) 0 := hz ▸ hasSum_norm_sq_traceNorm b T hT
      have hb (i) : B (b i) = 0 := by
        have hi := hsum.summable.le_tsum i (fun j _ ↦ sq_nonneg _)
        rw [hsum.tsum_eq] at hi
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg (B (b i))])
      have hzero (x : H) : B x = 0 := by
        have h := B.hasSum (b.hasSum_repr x)
        simpa only [map_smul, hb, smul_zero, tsum_zero] using h.tsum_eq.symm
      ext x
      change T x = 0
      apply norm_eq_zero.mp
      rw [← norm_abs_apply]
      rw [show operatorAbs T = B * B from (CFC.sqrt_mul_sqrt_self _ (abs_nonneg' T)).symm]
      exact norm_eq_zero.mpr (by
        change B (B x) = 0
        exact hzero _)
    · rintro rfl
      simp [traceNorm, operatorTrace, operatorAbs, CFC.sqrt_zero]
  · -- additivity of the trace
    refine (hasSum_trace b (S + T) hST).unique
      (((hasSum_trace b S hS).add (hasSum_trace b T hT)).congr_fun fun i ↦ ?_)
    rw [ContinuousLinearMap.add_apply, inner_add_right]
  · -- homogeneity of the trace
    refine (hasSum_trace b (a • T) haT).unique
      (((hasSum_trace b T hT).mul_left a).congr_fun fun i ↦ ?_)
    rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  · -- |Tr T| ≤ ‖T‖_Tr
    let z := operatorTrace T
    let c : ℂ := star z / (‖z‖ : ℂ)
    have hc : ‖c‖ ≤ 1 := by
      dsimp only [c]
      rw [norm_div, Complex.star_def, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg z)]
      exact div_self_le_one _
    have hcz : (c * z).re = ‖z‖ := by
      dsimp only [c]
      rw [div_mul_eq_mul_div, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two, mul_self_div_self,
        Complex.ofReal_re]
    let U : H →L[ℂ] H := c • ContinuousLinearMap.id ℂ H
    have hU : ‖U‖ ≤ 1 := by
      dsimp only [U]
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans hc
    obtain ⟨r, hr, hr_le⟩ := exists_hasSum_re_mul_le_traceNorm b T hT U hU
    have hreal : HasSum (fun i ↦ (inner ℂ (b i) ((U * T) (b i))).re) (c * z).re := by
      have h := Complex.reCLM.hasSum ((hasSum_trace b T hT).mul_left c)
      refine h.congr_fun fun i ↦ ?_
      show (inner ℂ (b i) ((c • ContinuousLinearMap.id ℂ H) (T (b i)))).re =
        Complex.reCLM (c * inner ℂ (b i) (T (b i)))
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_smul_right,
        Complex.reCLM_apply]
    rw [← hcz, hreal.unique hr]
    exact hr_le

