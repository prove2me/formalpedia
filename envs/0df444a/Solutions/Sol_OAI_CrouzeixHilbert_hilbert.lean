-- Prove2me | solution 1 for OAI.CrouzeixHilbert.hilbert
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:54:53.93071+00:00
-- url     : https://prove2.me/submissions/d69a8880-8b7d-41da-9abc-670ad91b99f0

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_MilnorDynamics_locally_bounded_holomorphic_subseq_locally_uniform
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_holomorphic_bound
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_injOn_of_tendstoLocallyUniformlyOn
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_riemann_biholomorphic_bounded
import Theorems.Thm_OAI_CrouzeixHilbert_exists_polynomial_uniform_approx
import Theorems.Thm_OAI_CrouzeixHilbert_matrixHolomorphicEval_matrixRationalFunction
import Theorems.Thm_OAI_CrouzeixHilbert_sum_integral_eq_zero_of_null_homology

section
-- module Solutions.OAIQW_CrouzeixHilbert.NumericalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact numerical closure, supremum norms, and spectral containment. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_le_of_mem_numericalRange (A : Operator H) {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ := by rw [hx]; ring

theorem numericalRange_subset_closedBall (A : Operator H) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_le_of_mem_numericalRange A hz

theorem numericalClosure_subset_closedBall (A : Operator H) :
    numericalClosure A ⊆ Metric.closedBall 0 ‖A‖ :=
  closure_minimal (numericalRange_subset_closedBall A) Metric.isClosed_closedBall

theorem isCompact_numericalClosure (A : Operator H) : IsCompact (numericalClosure A) :=
  (isCompact_closedBall (0 : ℂ) ‖A‖).of_isClosed_subset isClosed_closure
    (numericalClosure_subset_closedBall A)

theorem numericalRange_nonempty [Nontrivial H] (A : Operator H) :
    (numericalRange A).Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟪x, A x⟫_ℂ, x, hx, rfl⟩

theorem numericalClosure_nonempty [Nontrivial H] (A : Operator H) :
    (numericalClosure A).Nonempty :=
  (numericalRange_nonempty A).mono subset_closure

theorem zeroConclusion [Subsingleton H] (A : Operator H) : ZeroConclusion A := by
  have hemp := numericalRange_eq_empty A
  have hzero : ∀ m (T : Operator (Amplification H m)), T = 0 := by
    intro m T
    exact Subsingleton.elim _ _
  refine ⟨hemp, ?_, ?_, ?_⟩
  · intro m d B
    rw [hzero m (polynomialEval A B), hemp, supNorm_empty]
    simp
  · intro m U F
    rw [hzero m (matrixHolomorphicEval A U F), hemp, supNorm_empty]
    simp
  · intro m R
    rw [hzero m (matrixRationalEval A R), hemp, supNorm_empty]
    simp

theorem supNorm_le {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} {C : ℝ} (hC : 0 ≤ C) (hF : ∀ z ∈ S, ‖F z‖ ≤ C) :
    supNorm S F ≤ C := by
  apply csSup_le ⟨0, by simp⟩
  intro b hb
  rcases hb with rfl | ⟨z, hz, rfl⟩
  · exact hC
  · exact hF z hz

theorem supNorm_bddAbove {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hS : IsCompact S) (hF : ContinuousOn F S) :
    BddAbove (insert 0 ((fun z => ‖F z‖) '' S)) :=
  (hS.bddAbove_image hF.norm).insert 0

theorem supNorm_nonneg {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' S))) :
    0 ≤ supNorm S F :=
  le_csSup hb (by simp)

theorem norm_le_supNorm {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' S)))
    {z : ℂ} (hz : z ∈ S) : ‖F z‖ ≤ supNorm S F :=
  le_csSup hb (Set.mem_insert_of_mem 0 ⟨z, hz, rfl⟩)

theorem supNorm_mono {E : Type*} [NormedAddCommGroup E] {S T : Set ℂ}
    {F : ℂ → E} (hST : S ⊆ T)
    (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' T))) :
    supNorm S F ≤ supNorm T F := by
  apply csSup_le_csSup hb ⟨0, by simp⟩
  exact Set.insert_subset_insert (Set.image_mono hST)

theorem supNorm_attained {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hS : IsCompact S) (hne : S.Nonempty) (hF : ContinuousOn F S) :
    ∃ z ∈ S, supNorm S F = ‖F z‖ := by
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn hne hF.norm
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · exact supNorm_le (norm_nonneg _) hmax
  · exact norm_le_supNorm (supNorm_bddAbove hS hF) hz

theorem supNorm_closure {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hS : IsCompact (closure S)) (hF : ContinuousOn F (closure S)) :
    supNorm S F = supNorm (closure S) F := by
  have hbK := supNorm_bddAbove hS hF
  have hsub : insert 0 ((fun z => ‖F z‖) '' S) ⊆
      insert 0 ((fun z => ‖F z‖) '' closure S) :=
    Set.insert_subset_insert (Set.image_mono subset_closure)
  have hbS := hbK.mono hsub
  apply le_antisymm (supNorm_mono subset_closure hbK)
  have hc : IsClosed (closure S ∩ (fun z => ‖F z‖) ⁻¹' Iic (supNorm S F)) :=
    hF.norm.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hs : S ⊆ closure S ∩ (fun z => ‖F z‖) ⁻¹' Iic (supNorm S F) := by
    intro z hz
    exact ⟨subset_closure hz, norm_le_supNorm hbS hz⟩
  apply supNorm_le (supNorm_nonneg hbS)
  intro z hz
  exact (closure_minimal hs hc hz).2

theorem continuous_matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    Continuous (matrixPolynomial B) := by
  unfold matrixPolynomial
  exact continuous_finsetSum _ fun k _ => (continuous_id.pow _).smul continuous_const

theorem polynomial_sup_eq_max [Nontrivial H] (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    supNorm (numericalRange A) (matrixPolynomial B) =
      supNorm (numericalClosure A) (matrixPolynomial B) ∧
    ∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixPolynomial B) = ‖matrixPolynomial B z‖ := by
  have hc : ContinuousOn (matrixPolynomial B) (numericalClosure A) :=
    (continuous_matrixPolynomial B).continuousOn
  exact ⟨supNorm_closure (isCompact_numericalClosure A) hc,
    supNorm_attained (isCompact_numericalClosure A) (numericalClosure_nonempty A) hc⟩

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.FiniteCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact polynomial compression on spans of finitely many operator iterates. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem compression_inner (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) :
    ⟪x, compression A E x⟫_ℂ = ⟪(x : H), A (x : H)⟫_ℂ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x (A x)

theorem numericalRange_compression_subset (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] : numericalRange (compression A E) ⊆ numericalRange A := by
  rintro z ⟨x, hx, hz⟩
  exact ⟨(x : H), hx, (compression_inner A E x).symm.trans hz⟩

theorem coe_compression_apply (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) (hx : A (x : H) ∈ E) :
    (compression A E x : H) = A (x : H) := by
  have hh := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨A x, hx⟩ : E)
  exact congrArg (fun v : E => (v : H)) hh

theorem coe_compression_pow (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) (k : ℕ)
    (hx : ∀ j : ℕ, j ≤ k → (A ^ j) (x : H) ∈ E) :
    (((compression A E) ^ k) x : H) = (A ^ k) (x : H) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := ih (fun j hj => hx j (hj.trans (Nat.le_succ k)))
    have hmem : A (((compression A E) ^ k) x : H) ∈ E := by
      rw [hk]
      simpa only [pow_succ', mul_apply_eq_comp] using hx (k + 1) le_rfl
    simpa only [pow_succ', mul_apply_eq_comp] using
      (coe_compression_apply A E (((compression A E) ^ k) x) hmem).trans (congrArg A hk)

theorem iterate_mem_iterateSpan (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H)
    (j : Fin l) (k : ℕ) (hk : k ≤ d) : (A ^ k) (ξ j) ∈ iterateSpan A d ξ := by
  apply Submodule.subset_span
  exact ⟨(⟨k, Nat.lt_succ_of_le hk⟩, j), rfl⟩

theorem mem_iterateSpan (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H)
    (j : Fin l) : ξ j ∈ iterateSpan A d ξ := by
  simpa using iterate_mem_iterateSpan A d ξ j 0 (Nat.zero_le _)

theorem norm_amplificationInclusion (E : Submodule ℂ H) (m : ℕ)
    (x : Amplification E m) : ‖amplificationInclusion E m x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (amplificationInclusion E m).continuous.norm continuous_norm) ?_
  intro a
  simp only [amplificationInclusion, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe]
  rw [TensorProduct.mapL_apply]
  change ‖TensorProduct.map E.subtypeₗᵢ.toLinearMap
    (LinearIsometry.id : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)).toLinearMap a‖ = ‖a‖
  exact (TensorProduct.mapIsometry E.subtypeₗᵢ (LinearIsometry.id :
    EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))).norm_map a

theorem polynomialEval_tmul (A : Operator H) {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (x : H) (y : EuclideanSpace ℂ (Fin m)) :
    polynomialEval A B (↑(x ⊗ₜ[ℂ] y)) =
      ∑ k : Fin (d + 1), (↑(((A ^ (k : ℕ)) x) ⊗ₜ[ℂ]
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (B k) y)) : Amplification H m) := by
  simp only [polynomialEval, sum_apply, tensorOperator,
    ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

theorem polynomial_compression_tmul (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (x : E) (y : EuclideanSpace ℂ (Fin m))
    (hx : ∀ j : ℕ, j ≤ d → (A ^ j) (x : H) ∈ E) :
    polynomialEval A B (amplificationInclusion E m (↑(x ⊗ₜ[ℂ] y))) =
      amplificationInclusion E m (polynomialEval (compression A E) B (↑(x ⊗ₜ[ℂ] y))) := by
  simp only [amplificationInclusion_tmul, polynomialEval_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [coe_compression_pow A E x k (fun j hj => hx j (hj.trans (Nat.le_of_lt_succ k.isLt)))]

theorem completion_coe_finsetSum {V : Type*} [NormedAddCommGroup V]
    {ι : Type*} (s : Finset ι) (f : ι → V) :
    (↑(∑ i ∈ s, f i) : UniformSpace.Completion V) =
      ∑ i ∈ s, (↑(f i) : UniformSpace.Completion V) :=
  map_sum (UniformSpace.Completion.toCompl : V →+ UniformSpace.Completion V) f s

theorem polynomial_bound_of_finite_compressions (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) {C : ℝ} (hC : 0 ≤ C)
    (hfin : ∀ (E : Submodule ℂ H) [FiniteDimensional ℂ E],
      ‖polynomialEval (compression A E) B‖ ≤ C) :
    ‖polynomialEval A B‖ ≤ C := by
  apply (polynomialEval A B).opNorm_le_bound hC
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (polynomialEval A B).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro a
  obtain ⟨l, ξ, η, ha⟩ := TensorProduct.exists_sum_tmul_eq a
  let E := iterateSpan A d ξ
  let xE (j : Fin l) : E := ⟨ξ j, mem_iterateSpan A d ξ j⟩
  let v : Amplification E m := ∑ j : Fin l, (↑(xE j ⊗ₜ[ℂ] η j) : Amplification E m)
  have hav : (↑a : Amplification H m) = amplificationInclusion E m v := by
    rw [ha, completion_coe_finsetSum]
    simp only [v, map_sum, amplificationInclusion_tmul]
    rfl
  have hinter : polynomialEval A B (amplificationInclusion E m v) =
      amplificationInclusion E m (polynomialEval (compression A E) B v) := by
    simp only [v, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply polynomial_compression_tmul
    intro k hk
    exact iterate_mem_iterateSpan A d ξ j k hk
  calc
    ‖polynomialEval A B (↑a)‖ =
        ‖amplificationInclusion E m (polynomialEval (compression A E) B v)‖ := by
      rw [hav, hinter]
    _ = ‖polynomialEval (compression A E) B v‖ := norm_amplificationInclusion E m _
    _ ≤ ‖polynomialEval (compression A E) B‖ * ‖v‖ :=
      (polynomialEval (compression A E) B).le_opNorm v
    _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hfin E) (norm_nonneg _)
    _ = C * ‖(↑a : Amplification H m)‖ := by rw [hav, norm_amplificationInclusion]

theorem polynomial_inequality_of_finite_compressions (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (hfin : ∀ (E : Submodule ℂ H) [FiniteDimensional ℂ E],
      ‖polynomialEval (compression A E) B‖ ≤
        2 * supNorm (numericalRange (compression A E)) (matrixPolynomial B)) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) := by
  have hbK := supNorm_bddAbove (isCompact_numericalClosure A)
    (continuous_matrixPolynomial B).continuousOn
  have hbW : BddAbove (insert 0 ((fun z => ‖matrixPolynomial B z‖) '' numericalRange A)) :=
    hbK.mono (Set.insert_subset_insert (Set.image_mono subset_closure))
  apply polynomial_bound_of_finite_compressions A B
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (supNorm_nonneg hbW))
  intro E _
  exact (hfin E).trans (mul_le_mul_of_nonneg_left
    (supNorm_mono (numericalRange_compression_subset A E) hbW) (by norm_num))

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem norm_amplificationMap (e : H →ₗᵢ[ℂ] G) (m : ℕ)
    (x : Amplification H m) : ‖amplificationMap e m x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (amplificationMap e m).continuous.norm continuous_norm) ?_
  intro a
  simp only [amplificationMap, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe, TensorProduct.mapL_apply]
  exact (TensorProduct.mapIsometry e (LinearIsometry.id :
    EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))).norm_map a

theorem numericalRange_conjugateOperator (e : H ≃ₗᵢ[ℂ] G) (A : Operator H) :
    numericalRange (conjugateOperator e A) = numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, by simpa using hx, ?_⟩
    simpa using (e.inner_map_map (e.symm x) (A (e.symm x))).symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, by simpa using hx, by simp [e.inner_map_map]⟩

theorem polynomialEval_conjugateOperator_apply (e : H ≃ₗᵢ[ℂ] G) (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) (v : Amplification H m) :
    polynomialEval (conjugateOperator e A) B (amplificationMap e.toLinearIsometry m v) =
      amplificationMap e.toLinearIsometry m (polynomialEval A B v) := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((polynomialEval (conjugateOperator e A) B).continuous.comp
      (amplificationMap e.toLinearIsometry m).continuous)
      ((amplificationMap e.toLinearIsometry m).continuous.comp
        (polynomialEval A B).continuous)) ?_
  intro a
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x y =>
    simp only [amplificationMap_tmul, polynomialEval_tmul, conjugateOperator_pow_apply,
      map_sum, LinearIsometryEquiv.coe_toLinearIsometry]
  | add a b ha hb =>
    simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

theorem norm_polynomialEval_le_conjugateOperator (e : H ≃ₗᵢ[ℂ] G) (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ ‖polynomialEval (conjugateOperator e A) B‖ := by
  apply (polynomialEval A B).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [← norm_amplificationMap e.toLinearIsometry m (polynomialEval A B v),
    ← polynomialEval_conjugateOperator_apply]
  simpa only [norm_amplificationMap] using
    (polynomialEval (conjugateOperator e A) B).le_opNorm (amplificationMap e.toLinearIsometry m v)

theorem norm_polynomialEval_conjugateOperator (e : H ≃ₗᵢ[ℂ] G) (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval (conjugateOperator e A) B‖ = ‖polynomialEval A B‖ := by
  apply le_antisymm _ (norm_polynomialEval_le_conjugateOperator e A B)
  have he : conjugateOperator e.symm (conjugateOperator e A) = A := by ext x; simp
  simpa only [he] using
    norm_polynomialEval_le_conjugateOperator e.symm (conjugateOperator e A) B

open scoped Kronecker

theorem finiteDimensional_polynomial_bound [FiniteDimensional ℂ H]
    (hfin : FiniteMatrixPolynomialBound) (A : Operator H)
    {m d : ℕ} (hm : 0 < m) (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) := by
  cases subsingleton_or_nontrivial H with
  | inl h =>
    have := h
    exact ((zeroConclusion A).2.1 m d B).2.2
  | inr h =>
    have := h
    let e := (stdOrthonormalBasis ℂ H).repr
    let M : Coeff (Module.finrank ℂ H) :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (conjugateOperator e A)
    have he : Matrix.toEuclideanCLM (𝕜 := ℂ) M = conjugateOperator e A :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _
    have hb := hfin (Module.finrank ℂ H) Module.finrank_pos M m hm d B
    simpa only [he, norm_polynomialEval_conjugateOperator,
      numericalRange_conjugateOperator] using hb

theorem polynomial_bound_of_finite_matrix_bound (hfin : FiniteMatrixPolynomialBound)
    (A : Operator H) {m d : ℕ} (hm : 0 < m) (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) := by
  apply polynomial_inequality_of_finite_compressions
  intro E _
  exact finiteDimensional_polynomial_bound hfin (compression A E) hm B

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Existence. -/

noncomputable section

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

open Set Filter Metric

namespace CrouzeixHilbert

theorem sub_div_sub_mem_slitPlane {a b w : ℂ} (hw : w ∉ segment ℝ a b) :
    (w - a) / (w - b) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hwb : w - b ≠ 0 := by
    intro he
    exact hw ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  let r : ℝ := ((w - a) / (w - b)).re
  have hr : r ≤ 0 := h.1
  have hrc : (r : ℂ) = (w - a) / (w - b) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using h.2.symm
  have hmul : (r : ℂ) * (w - b) = w - a := by rw [hrc, div_mul_cancel₀ _ hwb]
  have hp : 0 < 1 - r := by linarith
  have hpn : (1 - (r : ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
  apply hw
  refine ⟨(1 - r)⁻¹, -r / (1 - r), inv_nonneg.mpr hp.le,
    div_nonneg (neg_nonneg.mpr hr) hp.le, ?_, ?_⟩
  · field_simp
    ring
  · simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg]
    apply (mul_right_cancel₀ hpn)
    field_simp
    linear_combination hmul

theorem SmoothContour.intervalIntegrable_indexIntegrand (Γ : SmoothContour) {a : ℂ}
    (ha : a ∉ Γ.path '' Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => deriv Γ.path t / (Γ.path t - a))
      MeasureTheory.volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  apply Γ.smooth.continuous_deriv_one.continuousOn.div
    (Γ.smooth.continuous.sub continuous_const).continuousOn
  intro t ht he
  exact ha ⟨t, ht, sub_eq_zero.mp he⟩

theorem SmoothContour.index_eq_of_segment_avoids (Γ : SmoothContour) {a b : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, Γ.path t ∉ segment ℝ a b) :
    Γ.index a = Γ.index b := by
  have hnza (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ left_mem_segment ℝ a b)
  have hnzb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - b ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnza t ht (sub_eq_zero.mpr he)
  have hb : b ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnzb t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log ((Γ.path t - a) / (Γ.path t - b)))
        (deriv Γ.path t / (Γ.path t - a) - deriv Γ.path t / (Γ.path t - b)) t := by
    have hg := (Γ.smooth.differentiable (by norm_num) t).hasDerivAt
    have he := ((hg.sub_const a).div (hg.sub_const b) (hnzb t ht)).clog_real
      (sub_div_sub_mem_slitPlane (h t ht))
    simp only [Pi.div_apply] at he
    convert! he using 1
    field_simp [hnza t ht, hnzb t ht]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    ((Γ.intervalIntegrable_indexIntegrand ha).sub (Γ.intervalIntegrable_indexIntegrand hb))
  rw [Γ.closed, sub_self, intervalIntegral.integral_sub
    (Γ.intervalIntegrable_indexIntegrand ha) (Γ.intervalIntegrable_indexIntegrand hb)] at he
  unfold SmoothContour.index
  rw [sub_eq_zero.mp he]

theorem SmoothContour.index_eq_zero_of_re_pos (Γ : SmoothContour) {a c : ℂ}
    (hc : c ≠ 0) (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c * (Γ.path t - a)).re) :
    Γ.index a = 0 := by
  have hnz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    simpa only [he, mul_zero, Complex.zero_re, lt_self_iff_false] using h t ht
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnz t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log (c * (Γ.path t - a)))
        (deriv Γ.path t / (Γ.path t - a)) t := by
    have he := (((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.sub_const a).const_mul c).clog_real
      (Complex.mem_slitPlane_iff.mpr (Or.inl (h t ht)))
    simpa only [mul_div_mul_left _ _ hc] using he
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (Γ.intervalIntegrable_indexIntegrand ha)
  rw [Γ.closed, sub_self] at he
  simp only [SmoothContour.index, he, mul_zero]

theorem SmoothContour.index_eq_zero_of_convex (Γ : SmoothContour) {V : Set ℂ}
    (hV : Convex ℝ V) (hVc : IsClosed V) (hΓ : Γ.path '' Icc (0 : ℝ) 1 ⊆ V)
    {a : ℂ} (ha : a ∉ V) :
    Γ.index a = 0 := by
  obtain ⟨l, r, hla, hlV⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) hV hVc ha
  have hl (z : ℂ) : l z = l 1 * z := by
    calc
      l z = l (z • (1 : ℂ)) := by simp
      _ = z • l 1 := l.map_smul z 1
      _ = l 1 * z := by simp [mul_comm]
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < (l 1 * (Γ.path t - a)).re := by
    rw [← hl, map_sub, Complex.sub_re]
    exact sub_pos.mpr (hla.trans (hlV _ (hΓ ⟨t, ht, rfl⟩)))
  apply Γ.index_eq_zero_of_re_pos ?_ hp
  intro he
  have := hp 0 ⟨le_rfl, zero_le_one⟩
  simp only [he, zero_mul, Complex.zero_re, lt_self_iff_false] at this

theorem exists_smooth_radial_frontier_approx {V : Set ℂ}
    (hV : Convex ℝ V) (hV0 : V ∈ 𝓝 (0 : ℂ)) (hVb : Bornology.IsBounded V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℂ → ℝ, ContDiff ℝ 1 q ∧ (∀ z, 0 < q z) ∧
      ∀ z : ℂ, ‖z‖ = 1 → ∃ w ∈ frontier V, dist (q z • z) w < ε := by
  obtain ⟨R, hR, hVR⟩ := hVb.subset_closedBall_lt 0 0
  let r : ℂ → ℝ := fun z => (max R⁻¹ (gauge V z))⁻¹
  have hrp (z : ℂ) : 0 < r z := inv_pos.mpr ((inv_pos.mpr hR).trans_le (le_max_left _ _))
  have hrc : Continuous r :=
    (continuous_const.max (continuous_gauge hV hV0)).inv₀ (fun z => ((inv_pos.mpr hR).trans_le (le_max_left _ _)).ne')
  obtain ⟨q, hq, hqr, -⟩ := hrc.exists_contDiff_approx 1
    (continuous_const.min (hrc.div_const 2)) (fun z => lt_min hε (half_pos (hrp z)))
  refine ⟨q, by simpa using hq, ?_, ?_⟩
  · intro z
    have he := (abs_lt.mp (hqr z)).1
    have := min_le_right ε (r z / 2)
    linarith [hrp z]
  · intro z hz
    have hg : R⁻¹ ≤ gauge V z := by
      simpa only [hz, one_div] using
        (le_gauge_of_subset_closedBall (absorbent_nhds_zero hV0) hR.le hVR (x := z))
    have hr : r z = (gauge V z)⁻¹ := inv_inj.mpr (max_eq_right hg)
    have hgz : gauge V z ≠ 0 := ne_of_gt ((inv_pos.mpr hR).trans_le hg)
    refine ⟨r z • z, (gauge_eq_one_iff_mem_frontier hV hV0).mp ?_, ?_⟩
    · rw [gauge_smul_of_nonneg (hrp z).le, smul_eq_mul, hr, inv_mul_cancel₀ hgz]
    · calc
        dist (q z • z) (r z • z) = |q z - r z| := by
          rw [dist_eq_norm, ← sub_smul, norm_smul, hz, mul_one, Real.norm_eq_abs]
        _ < min ε (r z / 2) := hqr z
        _ ≤ ε := min_le_left _ _

theorem unitCirclePath_ne_zero (t : ℝ) : unitCirclePath t ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [unitCirclePath_norm]
  norm_num

theorem hasDerivAt_unitCirclePath (t : ℝ) :
    HasDerivAt unitCirclePath (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) t := by
  convert! (hasDerivAt_circleMap 0 1 (2 * Real.pi * t)).scomp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi)) using 1
  simp only [unitCirclePath, mul_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem radialContour_index_center (a : ℂ) (q : ℂ → ℝ) (hq : ContDiff ℝ 1 q)
    (hqp : ∀ z, 0 < q z) : (radialContour a q hq).index a = 1 := by
  let f : ℝ → ℝ := fun t => q (unitCirclePath t)
  have hf : ContDiff ℝ 1 f := hq.comp unitCirclePath_smooth
  have hfp (t : ℝ) : f t ≠ 0 := (hqp _).ne'
  have hfc : f 0 = f 1 := by dsimp [f]; rw [unitCirclePath_closed]
  have hdiff (t : ℝ) : HasDerivAt f (deriv f t) t :=
    (hf.differentiable (by norm_num) t).hasDerivAt
  have hd (t : ℝ) : deriv (radialContour a q hq).path t =
      f t • (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) +
        deriv f t • unitCirclePath t :=
    ((hdiff t).smul (hasDerivAt_unitCirclePath t)).const_add a |>.deriv
  have hi : IntervalIntegrable (fun t => deriv f t / f t) MeasureTheory.volume (0 : ℝ) 1 :=
    (hf.continuous_deriv_one.div hf.continuous hfp).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => (hdiff t).log (hfp t)) hi
  rw [← hfc, sub_self] at he
  have heq (t : ℝ) : deriv (radialContour a q hq).path t /
      ((radialContour a q hq).path t - a) =
        ((deriv f t / f t : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I := by
    rw [hd]
    change ((f t : ℂ) * (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) +
      ((deriv f t : ℝ) : ℂ) * unitCirclePath t) /
      (a + (f t : ℂ) * unitCirclePath t - a) = _
    rw [add_sub_cancel_left, Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr (hfp t), unitCirclePath_ne_zero t]
    ring
  have hic : IntervalIntegrable (fun t => ((deriv f t / f t : ℝ) : ℂ))
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Complex.continuous_ofReal.comp (hf.continuous_deriv_one.div hf.continuous hfp)).intervalIntegrable 0 1
  simp only [SmoothContour.index, heq]
  rw [intervalIntegral.integral_add hic intervalIntegrable_const,
    intervalIntegral.integral_ofReal, he, Complex.ofReal_zero, zero_add,
    intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  apply inv_mul_cancel₀
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

theorem exists_calculusContour {K U : Set ℂ} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : K ⊆ U) :
    Nonempty (CalculusContour K U) := by
  obtain ⟨a, ha⟩ := hKne
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  let e : ℂ ≃ₜ ℂ := Homeomorph.addLeft a
  let V : Set ℂ := e ⁻¹' (cthickening (ε / 2) K)
  have hV : Convex ℝ V := by
    convert! (hKc.cthickening (ε / 2)).translate (-a) using 1
    ext z
    constructor
    · intro hz
      exact ⟨a + z, hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      change a + (-a + w) ∈ cthickening (ε / 2) K
      simpa using hw
  have hV0 : V ∈ 𝓝 (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    change 0 ∈ interior (e ⁻¹' (cthickening (ε / 2) K))
    rw [← e.preimage_interior]
    change a + 0 ∈ interior (cthickening (ε / 2) K)
    rw [add_zero]
    exact thickening_subset_interior_cthickening _ _ (self_subset_thickening (half_pos hε) _ ha)
  have hVb : Bornology.IsBounded V := (e.isCompact_preimage.mpr hK.cthickening).isBounded
  obtain ⟨q, hq, hqp, hqV⟩ := exists_smooth_radial_frontier_approx hV hV0 hVb
    (div_pos hε (by norm_num : (0 : ℝ) < 4))
  let Γ : SmoothContour := radialContour a q hq
  have hΓ (t : ℝ) : Γ.path t ∈ cthickening ε K ∧ Γ.path t ∉ K := by
    obtain ⟨w, hw, hd⟩ := hqV (unitCirclePath t) (unitCirclePath_norm t)
    have hw' : a + w ∈ frontier (cthickening (ε / 2) K) := by
      change w ∈ e ⁻¹' frontier (cthickening (ε / 2) K)
      rw [e.preimage_frontier]
      exact hw
    have hiw : infDist (a + w) K = ε / 2 := by
      unfold infDist
      rw [frontier_cthickening_subset K hw', ENNReal.toReal_ofReal (half_pos hε).le]
    have hd' : dist (Γ.path t) (a + w) < ε / 4 := by
      simpa only [Γ, radialContour, dist_add_left] using hd
    have hi : infDist (Γ.path t) K < ε := by
      have hle := infDist_le_infDist_add_dist (s := K) (x := Γ.path t) (y := a + w)
      rw [hiw] at hle
      linarith
    refine ⟨thickening_subset_cthickening ε K ((mem_thickening_iff_infDist_lt ⟨a, ha⟩).mpr hi), ?_⟩
    intro htK
    have hle := infDist_le_infDist_add_dist (s := K) (x := a + w) (y := Γ.path t)
    rw [hiw, infDist_zero_of_mem htK, zero_add, dist_comm] at hle
    linarith
  refine ⟨{ toSmoothContour := Γ, avoids := ?_, index_inside := ?_, index_outside := ?_ }⟩
  · intro t _ht
    exact ⟨hεU (hΓ t).1, (hΓ t).2⟩
  · intro z hz
    calc
      Γ.index z = Γ.index a := Γ.index_eq_of_segment_avoids (fun t _ht htz =>
        (hΓ t).2 (hKc.segment_subset hz ha htz))
      _ = 1 := radialContour_index_center a q hq hqp
  · intro z hz
    exact Γ.index_eq_zero_of_convex (hKc.cthickening ε) isClosed_cthickening
      (by rintro _ ⟨t, _ht, rfl⟩; exact (hΓ t).1) (fun he => hz (hεU he))

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic continuity, pole-free rational evaluation, and tensor norm bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem holomorphic_sup_attained [Nontrivial H] (A : Operator H)
    {m : ℕ} {U : Set ℂ} {F : ℂ → Coeff m}
    (hU : numericalClosure A ⊆ U) (hF : EntrywiseHolomorphic U F) :
    ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) F = ‖F z‖ :=
  supNorm_attained (isCompact_numericalClosure A) (numericalClosure_nonempty A)
    (hF.continuousOn.mono hU)

theorem isUnit_polynomial_aeval [CompleteSpace H] [Nontrivial H]
    (A : Operator H) (p : Polynomial ℂ)
    (hp : ∀ z ∈ numericalClosure A, p.eval z ≠ 0) :
    IsUnit (Polynomial.aeval A p) := by
  apply spectrum.isUnit_of_zero_notMem ℂ
  rw [spectrum.map_polynomial_aeval A p]
  rintro ⟨z, hz, heq⟩
  exact hp z (spectrum_subset_numericalClosure A hz) heq

theorem rational_denominators_isUnit [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {m : ℕ} (R : RationalMatrix m)
    (hR : PolesOutside (numericalClosure A) R) :
    ∀ i j, IsUnit (Polynomial.aeval A (R i j).denom) :=
  fun i j => isUnit_polynomial_aeval A (R i j).denom (hR i j)

theorem rational_holomorphic_neighborhood {m : ℕ} {K : Set ℂ}
    (R : RationalMatrix m) (hR : PolesOutside K R) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) := by
  let U : Set ℂ := ⋂ i, ⋂ j, {z : ℂ | (R i j).denom.eval z ≠ 0}
  have hne : ∀ z ∈ U, ∀ i j, (R i j).denom.eval z ≠ 0 := by
    intro z hz i j
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hz i) j
  refine ⟨U, ?_, ?_, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne.preimage (R i j).denom.continuous
  · intro z hz
    exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun j => hR i j z hz))
  · intro i j
    simp only [matrixRationalFunction, RatFunc.eval, Polynomial.eval₂_id]
    exact DifferentiableOn.div (𝕜 := ℂ) (𝕜' := ℂ)
      (R i j).num.differentiableOn (R i j).denom.differentiableOn
      (fun z hz => hne z hz i j)

theorem rational_sup_attained [Nontrivial H] (A : Operator H)
    {m : ℕ} (R : RationalMatrix m) (hR : PolesOutside (numericalClosure A) R) :
    ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) (matrixRationalFunction R) =
      ‖matrixRationalFunction R z‖ := by
  obtain ⟨U, _, hU, hF⟩ := rational_holomorphic_neighborhood R hR
  exact holomorphic_sup_attained A hU hF

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_contourKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    ContinuousOn (contourKernel A Γ.toSmoothContour) (Icc (0 : ℝ) 1) := by
  apply Γ.smooth.continuous_deriv_one.continuousOn.smul
  exact (continuousOn_resolvent A).comp Γ.smooth.continuous.continuousOn
    (fun t ht => (Γ.avoids t ht).2)

theorem contourEval_eq_kernel (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) :
    contourEval A Γ f = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∫ t in (0 : ℝ)..1, f (Γ.path t) • contourKernel A Γ t := by
  unfold contourEval contourKernel
  simp only [smul_smul, mul_comm (f _)]

theorem intervalIntegrable_contourIntegrand [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace) :
    IntervalIntegrable (fun t => f (Γ.path t) • contourKernel A Γ.toSmoothContour t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hcont := hfc.smul (continuousOn_contourKernel A Γ)
  rw [← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hcont
  exact hcont.intervalIntegrable

theorem tendsto_contourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {f : ℂ → ℂ} {fs : ℕ → ℂ → ℂ}
    (hc : ∀ n, ContinuousOn (fs n) Γ.toSmoothContour.trace)
    (hu : TendstoUniformlyOn fs f atTop Γ.toSmoothContour.trace) :
    Tendsto (fun n => contourEval A Γ.toSmoothContour (fs n)) atTop
      (𝓝 (contourEval A Γ.toSmoothContour f)) := by
  let k := contourKernel A Γ.toSmoothContour
  have hk : ContinuousOn k (Icc (0 : ℝ) 1) := continuousOn_contourKernel A Γ
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hk.norm
  let M := max C 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hkb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖k t‖ ≤ M :=
    (hC (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have huc : TendstoUniformlyOn (fun n t => fs n (Γ.path t) • k t)
      (fun t => f (Γ.path t) • k t) atTop (Icc (0 : ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / M) (div_pos hε hM)]
      with n hn
    intro t ht
    have hn' := hn (Γ.path t) (mem_image_of_mem _ ht)
    calc
      dist (f (Γ.path t) • k t) (fs n (Γ.path t) • k t) =
          ‖f (Γ.path t) - fs n (Γ.path t)‖ * ‖k t‖ := by
            rw [dist_eq_norm, ← sub_smul, norm_smul]
      _ ≤ ‖f (Γ.path t) - fs n (Γ.path t)‖ * M :=
        mul_le_mul_of_nonneg_left (hkb t ht) (norm_nonneg _)
      _ < (ε / M) * M := mul_lt_mul_of_pos_right (by simpa only [dist_eq_norm] using hn') hM
      _ = ε := div_mul_cancel₀ _ hM.ne'
  have hcon (n : ℕ) : ContinuousOn (fun t => fs n (Γ.path t) • k t)
      (Icc (0 : ℝ) 1) :=
    ((hc n).comp Γ.smooth.continuous.continuousOn
      (fun t ht => mem_image_of_mem _ ht)).smul hk
  have hi : Tendsto (fun n => ∫ t in (0 : ℝ)..1, fs n (Γ.path t) • k t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f (Γ.path t) • k t)) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · exact Eventually.of_forall (fun n => by simpa only [uIcc_of_le zero_le_one] using hcon n)
    · simpa only [uIcc_of_le zero_le_one] using huc
  simpa only [contourEval_eq_kernel] using hi.const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)

theorem tendsto_matrixContourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m : ℕ} {F : ℂ → Coeff m} {Fs : ℕ → ℂ → Coeff m}
    (hc : ∀ n, ContinuousOn (Fs n) Γ.toSmoothContour.trace)
    (hu : TendstoUniformlyOn Fs F atTop Γ.toSmoothContour.trace) :
    Tendsto (fun n => matrixContourEval A Γ.toSmoothContour (Fs n)) atTop
      (𝓝 (matrixContourEval A Γ.toSmoothContour F)) := by
  unfold matrixContourEval
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  have hsc : ∀ n, ContinuousOn (fun z => Fs n z i j) Γ.toSmoothContour.trace :=
    fun n => (matrixEntryCLM i j).continuous.comp_continuousOn (hc n)
  have hsu : TendstoUniformlyOn (fun n z => Fs n z i j) (fun z => F z i j)
      atTop Γ.toSmoothContour.trace :=
    (matrixEntryCLM i j).uniformContinuous.comp_tendstoUniformlyOn hu
  exact (tensorOperatorCLM (H := H) (Matrix.single i j 1)).continuous.continuousAt.tendsto.comp
    (tendsto_contourEval A Γ hsc hsu)

theorem supNorm_le_add_of_dist_le {E : Type*} [NormedAddCommGroup E]
    {S : Set ℂ} {F G : ℂ → E} {ε : ℝ} (hε : 0 ≤ ε)
    (hG : BddAbove (insert 0 ((fun z => ‖G z‖) '' S)))
    (hFG : ∀ z ∈ S, dist (F z) (G z) ≤ ε) :
    supNorm S F ≤ supNorm S G + ε := by
  apply supNorm_le (add_nonneg (supNorm_nonneg hG) hε)
  intro z hz
  have h₁ := norm_sub_norm_le (F z) (G z)
  have h₂ : ‖F z - G z‖ ≤ ε := by simpa only [dist_eq_norm] using hFG z hz
  have h₃ := norm_le_supNorm hG hz
  linarith

theorem abs_supNorm_sub_le_of_dist_le {E : Type*} [NormedAddCommGroup E]
    {S : Set ℂ} {F G : ℂ → E} {ε : ℝ} (hε : 0 ≤ ε)
    (hF : BddAbove (insert 0 ((fun z => ‖F z‖) '' S)))
    (hG : BddAbove (insert 0 ((fun z => ‖G z‖) '' S)))
    (hFG : ∀ z ∈ S, dist (F z) (G z) ≤ ε) :
    |supNorm S F - supNorm S G| ≤ ε := by
  have h₁ := supNorm_le_add_of_dist_le hε hG hFG
  have h₂ := supNorm_le_add_of_dist_le hε hF
    (fun z hz => (dist_comm (G z) (F z)).trans_le (hFG z hz))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tendsto_supNorm_of_uniform {E : Type*} [NormedAddCommGroup E]
    {S : Set ℂ} (hS : IsCompact S) {F : ℂ → E} {Fs : ℕ → ℂ → E}
    (hc : ∀ n, ContinuousOn (Fs n) S) (hF : ContinuousOn F S)
    (hu : TendstoUniformlyOn Fs F atTop S) :
    Tendsto (fun n => supNorm S (Fs n)) atTop (𝓝 (supNorm S F)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)]
    with n hn
  have h := abs_supNorm_sub_le_of_dist_le (half_pos hε).le
    (supNorm_bddAbove hS (hc n)) (supNorm_bddAbove hS hF)
    (fun z hz => (dist_comm (Fs n z) (F z)).trans_le (hn z hz).le)
  have hd : dist (supNorm S (Fs n)) (supNorm S F) ≤ ε / 2 := by
    simpa only [Real.dist_eq] using h
  exact hd.trans_lt (by linarith)

theorem contour_bound_of_polynomial_approximation [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ}
    (F : ℂ → Coeff m)
    (hF : ContinuousOn F (numericalClosure A))
    (hpoly : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B))
    (hcalc : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      matrixContourEval A Γ.toSmoothContour (matrixPolynomial B) = polynomialEval A B)
    (degrees : ℕ → ℕ) (B : (n : ℕ) → Fin (degrees n + 1) → Coeff m)
    (happrox : TendstoUniformlyOn (fun n => matrixPolynomial (B n)) F atTop
      (numericalClosure A ∪ Γ.toSmoothContour.trace)) :
    ‖matrixContourEval A Γ.toSmoothContour F‖ ≤ 2 * supNorm (numericalClosure A) F := by
  have hev := tendsto_matrixContourEval A Γ
    (fun n => (continuous_matrixPolynomial (B n)).continuousOn)
    (happrox.mono subset_union_right)
  have hmax := tendsto_supNorm_of_uniform (isCompact_numericalClosure A)
    (fun n => (continuous_matrixPolynomial (B n)).continuousOn) hF
    (happrox.mono subset_union_left)
  have htwo : Tendsto (fun n => 2 * supNorm (numericalClosure A) (matrixPolynomial (B n)))
      atTop (𝓝 (2 * supNorm (numericalClosure A) F)) := tendsto_const_nhds.mul hmax
  apply le_of_tendsto_of_tendsto hev.norm htwo
  filter_upwards [] with n
  rw [hcalc]
  have heq : supNorm (numericalRange A) (matrixPolynomial (B n)) =
      supNorm (numericalClosure A) (matrixPolynomial (B n)) :=
    supNorm_closure (isCompact_numericalClosure A) (continuous_matrixPolynomial (B n)).continuousOn
  rw [← heq]
  exact hpoly _ _

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HomologicalCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homological Cauchy. -/

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology

namespace CrouzeixHilbert

theorem null_homology_integral {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).trace ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ∑ i, c i • (Γ i).integral f = 0 :=
  sum_integral_eq_zero_of_null_homology Γ c hU hΓ hnull hf

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Automorphism. -/

noncomputable section

open Set Filter Metric Topology Function

open scoped ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem diskShift_den_ne {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj w * z ≠ 0 := by
  intro h
  have he : conj w * z = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖conj w * z‖ < 1 := by
    calc
      ‖conj w * z‖ = ‖w‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < 1 := by simpa using hw
  simp [he] at hn

theorem diskShift_norm_identity (w z : ℂ) :
    ‖1 - conj w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem diskShift_into_disk {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskShift w z‖ < 1 := by
  have hpos : 0 < (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg w, norm_nonneg z]
  rw [diskShift, norm_div, div_lt_one₀ (norm_pos_iff.mpr (diskShift_den_ne hw hz.le))]
  have := diskShift_norm_identity w z
  nlinarith [norm_nonneg (1 - conj w * z), norm_nonneg (z - w)]

theorem diskShift_eq_zero_iff {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskShift w z = 0 ↔ z = w := by
  simp [diskShift, div_eq_zero_iff, diskShift_den_ne hw hz, sub_eq_zero]

theorem diskShift_injOn {w : ℂ} (hw : ‖w‖ < 1) :
    InjOn (diskShift w) (closedBall 0 1) := by
  intro z hz v hv he
  have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hv' : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
  have hm : w * conj w ≠ 1 := by
    intro he'
    have hh := congrArg norm he'
    rw [norm_mul, Complex.norm_conj, norm_one] at hh
    nlinarith [norm_nonneg w]
  have he' := (div_eq_div_iff (diskShift_den_ne hw hz') (diskShift_den_ne hw hv')).mp he
  have hh : (z - v) * (1 - w * conj w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hm.symm))

theorem hasDerivAt_diskShift {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    HasDerivAt (diskShift w) ((1 - conj w * w) / (1 - conj w * z) ^ 2) z := by
  convert! ((hasDerivAt_id z).sub_const w).div
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul (conj w)))
    (diskShift_den_ne hw hz) using 1
  congr 1
  dsimp
  ring

theorem norm_deriv_diskShift_zero {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskShift w) 0‖ = 1 - ‖w‖ ^ 2 := by
  rw [(hasDerivAt_diskShift hw (by simp : ‖(0 : ℂ)‖ ≤ 1)).deriv]
  simp only [mul_zero, sub_zero, one_pow, div_one]
  rw [mul_comm (conj w) w, Complex.mul_conj, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq, abs_of_pos]
  nlinarith [norm_nonneg w]

theorem norm_deriv_diskShift_self {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskShift w) w‖ = (1 - ‖w‖ ^ 2)⁻¹ := by
  rw [(hasDerivAt_diskShift hw hw.le).deriv]
  have he : (1 - conj w * w) / (1 - conj w * w) ^ 2 = (1 - conj w * w)⁻¹ := by
    field_simp
  rw [he, norm_inv]
  congr 1
  rw [mul_comm (conj w) w, Complex.mul_conj, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq, abs_of_pos]
  nlinarith [norm_nonneg w]

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Montel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Montel. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem norm_deriv_le_on_half_ball {f : ℂ → ℂ} {U : Set ℂ}
    (_hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hb : ∀ z ∈ U, ‖f z‖ ≤ 1) {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : ball x R ⊆ U) {y : ℂ} (hy : y ∈ ball x (R / 2)) :
    ‖deriv f y‖ ≤ 1 / (R / 2) := by
  have hsub : closedBall y (R / 2) ⊆ U := by
    intro z hz
    apply hRU
    have hy' : dist y x < R / 2 := hy
    have hz' : dist z y ≤ R / 2 := hz
    exact (dist_triangle z y x).trans_lt (by linarith)
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
  · exact (hf.mono (by simpa [closure_ball _ (by positivity : R / 2 ≠ 0)] using hsub)).diffContOnCl
  · exact fun z hz => hb z (hsub (sphere_subset_closedBall hz))

theorem montel {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → ℂ)
    (hd : ∀ n, DifferentiableOn ℂ (F n) U)
    (hb : ∀ n z, z ∈ U → ‖F n z‖ ≤ 1) :
    ∃ (f : ℂ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (F ∘ φ) f atTop U ∧
      DifferentiableOn ℂ f U ∧ ∀ z ∈ U, ‖f z‖ ≤ 1 := by
  obtain ⟨φ, hφ, g, -, hconv⟩ :=
    MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform U hU F hd
      (fun K hK _ => ⟨1, fun n z hz => hb n z (hK hz)⟩)
  refine ⟨g, φ, hφ, hconv, hconv.differentiableOn (Eventually.of_forall (fun n => hd (φ n))) hU, ?_⟩
  intro z hz
  exact le_of_tendsto' (hconv.tendsto_at hz).norm (fun n => hb (φ n) z hz)

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Riemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Riemann. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem derivative_values_bddAbove {U : Set ℂ} {a : ℂ} (hU : IsOpen U) (ha : a ∈ U) :
    BddAbove {v : ℝ | ∃ f, DiskEmbedding U a f ∧ ‖deriv f a‖ = v} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU a ha
  refine ⟨1 / (r / 2), ?_⟩
  rintro v ⟨f, hf, rfl⟩
  exact norm_deriv_le_on_half_ball hU hf.holomorphic
    (fun z hz => (hf.into_disk z hz).le) hr hsub (mem_ball_self (by positivity))

theorem exists_extremal {U : Set ℂ} {a : ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (ha : a ∈ U) {g : ℂ → ℂ}
    (hg : DiskEmbedding U a g) (hgd : deriv g a ≠ 0) :
    ∃ f, DiskEmbedding U a f ∧ deriv f a ≠ 0 ∧
      ∀ q, DiskEmbedding U a q → ‖deriv q a‖ ≤ ‖deriv f a‖ := by
  classical
  let S : Set ℝ := {v | ∃ f, DiskEmbedding U a f ∧ ‖deriv f a‖ = v}
  have hS : S.Nonempty := ⟨‖deriv g a‖, g, hg, rfl⟩
  have hSb : BddAbove S := derivative_values_bddAbove hU ha
  have hα : 0 < sSup S := (norm_pos_iff.mpr hgd).trans_le (le_csSup hSb ⟨g, hg, rfl⟩)
  obtain ⟨v, _, hv, hvS⟩ := exists_seq_tendsto_sSup hS hSb
  choose F hF hFv using hvS
  obtain ⟨f, φ, hφ, hl, hd, hnorm⟩ := montel hU F (fun n => (hF n).holomorphic)
    (fun n z hz => ((hF n).into_disk z hz).le)
  have hderiv : ‖deriv f a‖ = sSup S := by
    have hlim := ((hl.deriv (Eventually.of_forall (fun n => (hF (φ n)).holomorphic)) hU).tendsto_at ha).norm
    have heq : (fun n => ‖deriv ((F ∘ φ) n) a‖) = v ∘ φ := by
      funext n
      exact hFv (φ n)
    change Tendsto (fun n => ‖deriv ((F ∘ φ) n) a‖) atTop (𝓝 ‖deriv f a‖) at hlim
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim (hv.comp hφ.tendsto_atTop)
  have hfd : deriv f a ≠ 0 := norm_pos_iff.mp (hderiv ▸ hα)
  have hnc : ¬ ∃ c, EqOn f (fun _ => c) U := by
    rintro ⟨c, he⟩
    apply hfd
    have hfe : f =ᶠ[𝓝 a] fun _ => c := he.eventuallyEq_of_mem (hU.mem_nhds ha)
    exact hfe.deriv_eq.trans (deriv_const _ _)
  have hinto : ∀ z ∈ U, ‖f z‖ < 1 := by
    intro z hz
    apply lt_of_le_of_ne (hnorm z hz)
    intro he
    apply hnc
    refine ⟨f z, Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc hU hd hz ?_⟩
    intro w hw
    exact (hnorm w hw).trans he.ge
  have hzero : f a = 0 := by
    apply tendsto_nhds_unique (hl.tendsto_at ha)
    have he : (fun n => (F ∘ φ) n a) = fun _ => (0 : ℂ) := by
      funext n
      exact (hF (φ n)).normalized
    rw [he]
    exact tendsto_const_nhds
  refine ⟨f, ⟨hd, injOn_of_tendstoLocallyUniformlyOn hU hc hl
    (fun n => (hF (φ n)).holomorphic) (fun n => (hF (φ n)).injective) hnc, hinto, hzero⟩,
    hfd, ?_⟩
  intro q hq
  rw [hderiv]
  exact le_csSup hSb ⟨q, hq, rfl⟩

theorem exists_holomorphic_square_root {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hz : ∀ z ∈ U, q z ≠ 0) :
    ∃ h : ℂ → ℂ, (∀ z, h z ^ 2 = q z) ∧
      (∀ z ∈ U, h z ≠ 0) ∧
      ∀ z ∈ U, HasDerivAt h (deriv q z / (2 * h z)) z := by
  have hnot : 0 ∉ q '' U := by
    rintro ⟨z, hzu, he⟩
    exact hz z hzu he
  obtain ⟨h, hh, he⟩ := Complex.exists_continuousOn_pow_eq hc hU hq.continuousOn hnot two_ne_zero
  have hn : ∀ z ∈ U, h z ≠ 0 := by
    intro z hzu he'
    apply hz z hzu
    rw [← he, he', zero_pow two_ne_zero]
  refine ⟨h, he, hn, ?_⟩
  intro z hzu
  have hp : HasDerivAt (fun x : ℂ => x ^ 2) (2 * h z) (h z) := by
    simpa using hasDerivAt_pow 2 (h z)
  exact HasDerivAt.of_comp_left (hh.continuousAt (hU.mem_nhds hzu)) hp
    ((hq z hzu).differentiableAt (hU.mem_nhds hzu)).hasDerivAt
    (mul_ne_zero two_ne_zero (hn z hzu)) (Eventually.of_forall he)

theorem exists_improved_of_omitted {U : Set ℂ} {a : ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) (ha : a ∈ U) {f : ℂ → ℂ}
    (hf : DiskEmbedding U a f) (hfd : deriv f a ≠ 0)
    {w : ℂ} (hw : ‖w‖ < 1) (hwo : w ∉ f '' U) :
    ∃ ψ, DiskEmbedding U a ψ ∧ ‖deriv f a‖ < ‖deriv ψ a‖ := by
  let q := diskShift w ∘ f
  have hqnorm : ∀ z ∈ U, ‖q z‖ < 1 := fun z hz => diskShift_into_disk hw (hf.into_disk z hz)
  have hqhol : DifferentiableOn ℂ q U := by
    intro z hz
    exact ((hasDerivAt_diskShift hw (hf.into_disk z hz).le).comp z
      ((hf.holomorphic z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt).differentiableAt.differentiableWithinAt
  have hqinj : InjOn q U := (diskShift_injOn hw).comp hf.injective
    (fun z hz => mem_closedBall_zero_iff.mpr (hf.into_disk z hz).le)
  have hqzero : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz he
    exact hwo ⟨z, hz, (diskShift_eq_zero_iff hw (hf.into_disk z hz).le).mp he⟩
  obtain ⟨h, hsq, hhn, hhd⟩ := exists_holomorphic_square_root hU hc hqhol hqzero
  have hhnorm : ∀ z ∈ U, ‖h z‖ < 1 := by
    intro z hz
    have hn : ‖h z‖ ^ 2 < 1 := by rw [← norm_pow, hsq]; exact hqnorm z hz
    nlinarith [norm_nonneg (h z)]
  have hhinj : InjOn h U := by
    intro z hz v hv he
    apply hqinj hz hv
    rw [← hsq, ← hsq, he]
  let ψ := diskShift (h a) ∘ h
  have hψder : HasDerivAt ψ
      (deriv (diskShift (h a)) (h a) * (deriv q a / (2 * h a))) a :=
    (hasDerivAt_diskShift (hhnorm a ha) (hhnorm a ha).le).differentiableAt.hasDerivAt.comp a (hhd a ha)
  have hψ : DiskEmbedding U a ψ := by
    constructor
    · intro z hz
      exact ((hasDerivAt_diskShift (hhnorm a ha) (hhnorm z hz).le).comp z
        (hhd z hz)).differentiableAt.differentiableWithinAt
    · exact (diskShift_injOn (hhnorm a ha)).comp hhinj
        (fun z hz => mem_closedBall_zero_iff.mpr (hhnorm z hz).le)
    · exact fun z hz => diskShift_into_disk (hhnorm a ha) (hhnorm z hz)
    · exact diskShift_self _
  refine ⟨ψ, hψ, ?_⟩
  have hqa : q a = -w := by simp [q, hf.normalized]
  have hsqa : ‖h a‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hsq, hqa, norm_neg]
  have hqd : ‖deriv q a‖ = (1 - ‖w‖ ^ 2) * ‖deriv f a‖ := by
    rw [deriv_comp a (hasDerivAt_diskShift hw (hf.into_disk a ha).le).differentiableAt
      ((hf.holomorphic a ha).differentiableAt (hU.mem_nhds ha)), norm_mul,
      hf.normalized, norm_deriv_diskShift_zero hw]
  have hψnorm : ‖deriv ψ a‖ = (1 - ‖h a‖ ^ 2)⁻¹ *
      ((1 - ‖w‖ ^ 2) * ‖deriv f a‖ / (2 * ‖h a‖)) := by
    rw [hψder.deriv, norm_mul, norm_deriv_diskShift_self (hhnorm a ha),
      norm_div, hqd, norm_mul]
    norm_num
  have hr0 : 0 < ‖h a‖ := norm_pos_iff.mpr (hhn a ha)
  have hr1 : ‖h a‖ < 1 := hhnorm a ha
  have ha0 : 0 < ‖deriv f a‖ := norm_pos_iff.mpr hfd
  have hden : 0 < 1 - ‖h a‖ ^ 2 := by nlinarith
  rw [hψnorm, ← hsqa]
  have he : (1 - ‖h a‖ ^ 2)⁻¹ *
      ((1 - (‖h a‖ ^ 2) ^ 2) * ‖deriv f a‖ / (2 * ‖h a‖)) =
      (1 + ‖h a‖ ^ 2) * ‖deriv f a‖ / (2 * ‖h a‖) := by
    field_simp
    ring
  rw [he, lt_div_iff₀ (by positivity)]
  have hgain : 0 < (1 - ‖h a‖) ^ 2 * ‖deriv f a‖ :=
    mul_pos (sq_pos_of_pos (sub_pos.mpr hr1)) ha0
  nlinarith

theorem exists_diskEmbedding_of_bounded {U : Set ℂ} (hb : Bornology.IsBounded U) (a : ℂ) :
    ∃ f, DiskEmbedding U a f ∧ deriv f a ≠ 0 := by
  obtain ⟨r, hr, hsub⟩ := hb.subset_ball_lt 0 a
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let f : ℂ → ℂ := fun z => (z - a) / r
  have hd : ∀ z, HasDerivAt f (1 / r) z := fun z => ((hasDerivAt_id z).sub_const a).div_const (r : ℂ)
  refine ⟨f, ⟨fun z _ => (hd z).differentiableAt.differentiableWithinAt, ?_, ?_, ?_⟩, ?_⟩
  · intro z _ w _ he
    have he' : z - a = w - a := (div_left_inj' hrC).mp he
    exact sub_left_injective he'
  · intro z hz
    change ‖(z - a) / (r : ℂ)‖ < 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_one₀ hr]
    exact (dist_eq_norm z a) ▸ hsub hz
  · simp [f]
  · rw [(hd a).deriv]
    exact div_ne_zero one_ne_zero hrC

theorem riemann_mapping_bounded {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U) :
    ∃ f, DiskEmbedding U a f ∧ deriv f a ≠ 0 ∧ BijOn f U (ball 0 1) := by
  obtain ⟨g, hg, hgd⟩ := exists_diskEmbedding_of_bounded hb a
  obtain ⟨f, hf, hfd, hext⟩ := exists_extremal hU hc.isPathConnected.isConnected.isPreconnected ha hg hgd
  refine ⟨f, hf, hfd, ⟨fun z hz => mem_ball_zero_iff.mpr (hf.into_disk z hz), hf.injective, ?_⟩⟩
  intro w hw
  by_contra hwo
  obtain ⟨ψ, hψ, hh⟩ := exists_improved_of_omitted hU hc ha hf hfd
    (mem_ball_zero_iff.mp hw) hwo
  exact (hext ψ hψ).not_gt hh

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Univalent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Univalent. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem hasStrictDerivAt_invFunOn {U V : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) {w : ℂ} (hw : w ∈ V) :
    HasStrictDerivAt (invFunOn f U) (deriv f (invFunOn f U w))⁻¹ w := by
  obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
  have hinv := hbij.invOn_invFunOn
  have he : ∀ᶠ v in 𝓝 z, invFunOn f U (f v) = v := by
    filter_upwards [hU.mem_nhds hz] with v hv
    exact hinv.1 hv
  rw [hinv.1 hz]
  exact ((hf.analyticOnNhd hU z hz).hasStrictDerivAt).to_local_left_inverse
    (deriv_ne_zero_of_injOn hU hf hbij.injOn hz) he

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Modulus. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

attribute [local instance] Classical.propDecidable

theorem isCompact_preimage_closedBall {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    {r : ℝ} (hr : r < 1) : IsCompact (U ∩ f ⁻¹' closedBall 0 r) := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr
  have hd : DifferentiableOn ℂ (invFunOn f U) (ball 0 1) :=
    fun w hw => (hasStrictDerivAt_invFunOn hU hf hbij hw).hasDerivAt.differentiableAt.differentiableWithinAt
  have he : U ∩ f ⁻¹' closedBall 0 r = invFunOn f U '' closedBall 0 r := by
    ext z
    constructor
    · rintro ⟨hzu, hz⟩
      exact ⟨f z, hz, hbij.invOn_invFunOn.1 hzu⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(hbij.symm hbij.invOn_invFunOn.symm).mapsTo (hsub hw),
        by simpa only [mem_preimage, hbij.invOn_invFunOn.2 (hsub hw)] using hw⟩
  rw [he]
  exact (isCompact_closedBall 0 r).image_of_continuousOn (hd.continuousOn.mono hsub)

theorem tendsto_norm_one_at_frontier {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    {p : ℂ} (hp : p ∈ frontier U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hK := isCompact_preimage_closedBall hU hf hbij (sub_lt_self (1 : ℝ) hε)
  have hpn : p ∉ U ∩ f ⁻¹' closedBall 0 (1 - ε) := by
    intro he
    exact hp.2 (hU.interior_eq.symm ▸ he.1)
  filter_upwards [Filter.mem_inf_of_left (hK.isClosed.isOpen_compl.mem_nhds hpn),
    self_mem_nhdsWithin] with z hz₁ hz₂
  have hsmall : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hbij.mapsTo hz₂)
  have hlarge : 1 - ε < ‖f z‖ := by
    by_contra h
    exact hz₁ ⟨hz₂, mem_closedBall_zero_iff.mpr (le_of_not_gt h)⟩
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem continuousOn_closed_modulus {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1)) :
    ContinuousOn (fun z => if z ∈ U then ‖f z‖ else 1) (closure U) := by
  classical
  intro p hp
  by_cases hpU : p ∈ U
  · apply (hf.continuousOn.norm.continuousAt (hU.mem_nhds hpU)).continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.mem_inf_of_left (hU.mem_nhds hpU)] with z hz
      simp only [ite_eq_left hz]
    · simp only [ite_eq_left hpU]
  · have hpf : p ∈ frontier U := ⟨hp, by simpa only [hU.interior_eq] using hpU⟩
    have ht := tendsto_norm_one_at_frontier hU hf hbij hpf
    rw [ContinuousWithinAt, ite_eq_right hpU]
    let : DecidablePred U := fun z => Classical.propDecidable _
    exact (ht.mono_left (nhdsWithin_mono p inter_subset_right)).if_nhdsWithin tendsto_const_nhds

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PoissonExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson Extension. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem schwarzExtension_re {R : ℝ} {u : ℂ → ℝ} (hu : CircleIntegrable u 0 R)
    {w : ℂ} (hw : w ∈ ball 0 R) : (schwarzExtension R u w).re = poissonExtension R u w := by
  simpa only [schwarzExtension, poissonExtension, poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.mul_def] using
    re_circleAverage_herglotzRieszKernel_smul hu hw

theorem analyticOnNhd_schwarzExtension {R : ℝ} {u : ℂ → ℝ} (hR : 0 ≤ R)
    (hu : ContinuousOn u (sphere 0 R)) : AnalyticOnNhd ℂ (schwarzExtension R u) (ball 0 R) := by
  intro w hw
  exact analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    (ContinuousOn.circleIntegrable hR (continuous_ofReal.comp_continuousOn hu)) w hw

theorem harmonicOnNhd_poissonExtension {R : ℝ} {u : ℂ → ℝ} (hR : 0 ≤ R)
    (hu : ContinuousOn u (sphere 0 R)) : HarmonicOnNhd (poissonExtension R u) (ball 0 R) := by
  intro w hw
  have he : (fun z => (schwarzExtension R u z).re) =ᶠ[𝓝 w] poissonExtension R u := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    exact schwarzExtension_re (ContinuousOn.circleIntegrable hR hu) hz
  exact (harmonicAt_congr_nhds he).mp (analyticOnNhd_schwarzExtension hR hu w hw).harmonicAt_re

theorem poissonKernel_nonneg {R : ℝ} {w ζ : ℂ} (hw : w ∈ ball 0 R)
    (hζ : ζ ∈ sphere 0 R) : 0 ≤ poissonKernel 0 w ζ := by
  have hR := pos_of_mem_ball hw
  have hwN := mem_ball_zero_iff.mp hw
  have hζN := mem_sphere_zero_iff_norm.mp hζ
  simp only [poissonKernel, sub_zero, hζN]
  exact div_nonneg (by nlinarith [norm_nonneg w]) (sq_nonneg _)

theorem continuousOn_poissonKernel {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)

theorem circleAverage_poissonKernel {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    circleAverage (poissonKernel 0 w) 0 R = 1 := by
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, mul_one, Pi.one_apply, Pi.mul_def] using
    (harmonicContOnCl_const (c := (1 : ℝ)) (s := ball (0 : ℂ) R)).circleAverage_poissonKernel_smul hw

theorem tendsto_poissonExtension_at_sphere {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) {p : ℂ} (hp : p ∈ sphere 0 R) :
    Tendsto (poissonExtension R u) (𝓝[ball 0 R] p) (𝓝 (u p)) := by
  have hpN : ‖p‖ = R := mem_sphere_zero_iff_norm.mp hp
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hu.sub continuousOn_const : ContinuousOn (fun t => u t - u p) (sphere 0 R))
  have hB0 : 0 ≤ B := (norm_nonneg (u p - u p)).trans (hB p hp)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousWithinAt_iff.mp (hu p hp) (ε / 2) (by positivity)
  let c : ℂ → ℝ := fun w => B * (R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2
  have hc : Tendsto c (𝓝 p) (𝓝 0) := by
    have hc' : Continuous c := by dsimp [c]; fun_prop
    simpa only [c, hpN, sub_self, mul_zero, zero_div] using hc'.continuousAt.tendsto (x := p)
  filter_upwards [Filter.mem_inf_of_left (ball_mem_nhds p (half_pos hδ)),
      Filter.mem_inf_of_left (hc.eventually (gt_mem_nhds (half_pos hε))),
      self_mem_nhdsWithin] with w hwp hcε hw
  have hc0 : 0 ≤ c w := by
    have hwn := mem_ball_zero_iff.mp hw
    dsimp [c]
    exact div_nonneg (mul_nonneg hB0 (by nlinarith [norm_nonneg w])) (sq_nonneg _)
  have hPc := continuousOn_poissonKernel hw
  rw [abs_of_pos hR] at hPc
  have huP : ContinuousOn (fun t => poissonKernel 0 w t * (u t - u p)) (sphere 0 R) :=
    hPc.mul (hu.sub continuousOn_const)
  have hpoint : ∀ t ∈ sphere (0 : ℂ) R,
      |poissonKernel 0 w t * (u t - u p)| ≤ poissonKernel 0 w t * (ε / 2) + c w := by
    intro t ht
    have hPn := poissonKernel_nonneg hw ht
    rw [abs_mul, abs_of_nonneg hPn]
    by_cases htp : dist t p < δ
    · have hm := hmod ht htp
      rw [Real.dist_eq] at hm
      exact (mul_le_mul_of_nonneg_left hm.le hPn).trans (le_add_of_nonneg_right hc0)
    · have hdist : δ / 2 ≤ ‖t - w‖ := by
        have htδ := le_of_not_gt htp
        have hd := dist_triangle t w p
        rw [mem_ball] at hwp
        rw [dist_eq_norm t w] at hd
        linarith
      have hn : 0 ≤ R ^ 2 - ‖w‖ ^ 2 := by
        have := mem_ball_zero_iff.mp hw
        nlinarith [norm_nonneg w]
      have hPK : poissonKernel 0 w t ≤ (R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2 := by
        simp only [poissonKernel, sub_zero, mem_sphere_zero_iff_norm.mp ht]
        apply div_le_div_of_nonneg_left hn (sq_pos_of_pos (half_pos hδ))
        exact pow_le_pow_left₀ (le_of_lt (half_pos hδ)) hdist 2
      have htB : |u t - u p| ≤ B := by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hB t ht
      calc
        _ ≤ poissonKernel 0 w t * B := mul_le_mul_of_nonneg_left htB hPn
        _ ≤ (R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2 * B := mul_le_mul_of_nonneg_right hPK hB0
        _ = c w := by dsimp [c]; ring
        _ ≤ poissonKernel 0 w t * (ε / 2) + c w := le_add_of_nonneg_left (by positivity)
  have hint : CircleIntegrable (fun t => poissonKernel 0 w t * (u t - u p)) 0 R :=
    ContinuousOn.circleIntegrable hR.le huP
  have hiabs : CircleIntegrable (fun t => |poissonKernel 0 w t * (u t - u p)|) 0 R :=
    ContinuousOn.circleIntegrable hR.le huP.abs
  have hiup : CircleIntegrable (fun t => poissonKernel 0 w t * (ε / 2) + c w) 0 R :=
    ContinuousOn.circleIntegrable hR.le ((hPc.mul_const _).add continuousOn_const)
  have heq : poissonExtension R u w - u p =
      circleAverage (fun t => poissonKernel 0 w t * (u t - u p)) 0 R := by
    simp_rw [mul_sub]
    rw [circleAverage_fun_sub (f₁ := fun t => poissonKernel 0 w t * u t)
      (f₂ := fun t => poissonKernel 0 w t * u p)
      (ContinuousOn.circleIntegrable hR.le (hPc.mul hu))
      (ContinuousOn.circleIntegrable hR.le (hPc.mul_const _))]
    have hm : circleAverage (fun t => poissonKernel 0 w t * u p) 0 R = u p := by
      simp_rw [mul_comm _ (u p), ← smul_eq_mul]
      rw [circleAverage_fun_smul, circleAverage_poissonKernel hw, smul_eq_mul, mul_one]
    rw [hm]
    rfl
  have hupeq : circleAverage (fun t => poissonKernel 0 w t * (ε / 2) + c w) 0 R = ε / 2 + c w := by
    rw [circleAverage_fun_add (ContinuousOn.circleIntegrable hR.le (hPc.mul_const _))
      (ContinuousOn.circleIntegrable hR.le continuousOn_const), circleAverage_const]
    simp_rw [mul_comm _ (ε / 2), ← smul_eq_mul]
    rw [circleAverage_fun_smul, circleAverage_poissonKernel hw, smul_eq_mul, mul_one]
  rw [Real.dist_eq, heq]
  calc
    _ ≤ circleAverage (fun t => |poissonKernel 0 w t * (u t - u p)|) 0 R :=
      abs_circleAverage_le_circleAverage_abs
    _ ≤ circleAverage (fun t => poissonKernel 0 w t * (ε / 2) + c w) 0 R :=
      circleAverage_mono hiabs hiup (by simpa only [abs_of_pos hR] using hpoint)
    _ = ε / 2 + c w := hupeq
    _ < ε := by linarith

theorem dirichletExtension_eq_on_sphere {R : ℝ} {u : ℂ → ℝ} :
    EqOn (dirichletExtension R u) u (sphere 0 R) := by
  intro p hp
  exact piecewise_eq_of_notMem _ _ _ (not_lt.mpr (mem_sphere.mp hp).ge)

theorem dirichletExtension_eventuallyEq {R : ℝ} {u : ℂ → ℝ} {p : ℂ}
    (hp : p ∈ ball 0 R) : dirichletExtension R u =ᶠ[𝓝 p] poissonExtension R u := by
  filter_upwards [isOpen_ball.mem_nhds hp] with z hz
  exact piecewise_eq_of_mem _ _ _ hz

theorem harmonicContOnCl_dirichletExtension {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    HarmonicContOnCl (dirichletExtension R u) (ball 0 R) := by
  refine HarmonicContOnCl.mk_ball (fun p hp => ?_) ?_
  · exact (harmonicAt_congr_nhds (dirichletExtension_eventuallyEq hp)).mpr
      (harmonicOnNhd_poissonExtension hR.le hu p hp)
  · intro p hp
    rcases lt_or_eq_of_le (mem_closedBall.mp hp) with hi | hb
    · exact ((harmonicOnNhd_poissonExtension hR.le hu p hi).1.continuousAt.congr
        (dirichletExtension_eventuallyEq hi).symm).continuousWithinAt
    · have hs : p ∈ sphere (0 : ℂ) R := hb
      have he := dirichletExtension_eq_on_sphere (u := u) hs
      have hball : ContinuousWithinAt (dirichletExtension R u) (ball 0 R) p := by
        rw [ContinuousWithinAt, he]
        apply (tendsto_poissonExtension_at_sphere hR hu hs).congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (piecewise_eq_of_mem _ _ _ hz).symm
      have hsphere : ContinuousWithinAt (dirichletExtension R u) (sphere 0 R) p :=
        (hu p hs).congr dirichletExtension_eq_on_sphere he
      simpa only [ball_union_sphere] using hball.union hsphere

theorem circleAverage_comp_conj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R : ℝ) : circleAverage (fun z => f (conj z)) 0 R = circleAverage f 0 R := by
  rw [circleAverage_eq_circleAverage_zero_one, circleAverage_eq_circleAverage_zero_one (f := f)]
  calc
    _ = circleAverage (fun z => f ((R : ℂ) * z⁻¹ + 0)) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      have hzN : ‖z‖ = 1 := by simpa only [abs_one] using mem_sphere_zero_iff_norm.mp hz
      simp only [Complex.inv_eq_conj hzN, map_add, map_mul, Complex.conj_ofReal, map_zero]
    _ = _ := circleAverage_zero_one_congr_inv (f := fun z => f ((R : ℂ) * z + 0))

theorem poissonExtension_conj {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ∀ z ∈ sphere 0 R, u (conj z) = -u z) (w : ℂ) :
    poissonExtension R u (conj w) = -poissonExtension R u w := by
  unfold poissonExtension
  rw [← circleAverage_comp_conj (fun z => poissonKernel 0 (conj w) z * u z) R]
  calc
    _ = circleAverage (fun z => (-1 : ℝ) • (poissonKernel 0 w z * u z)) 0 R := by
      apply circleAverage_congr_sphere
      intro z hz
      have he : poissonKernel 0 (conj w) (conj z) = poissonKernel 0 w z := by
        simp only [poissonKernel, sub_zero, ← map_sub, Complex.norm_conj]
      dsimp only
      rw [he, hu z (by simpa only [abs_of_nonneg hR] using hz)]
      simp
    _ = _ := by rw [circleAverage_fun_smul, neg_one_smul]

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HarmonicMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harmonic Maximum. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

namespace CrouzeixHilbert.Conformal

theorem harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {p : ℂ}
    (hu : HarmonicAt u p) (hm : IsLocalMax u p) :
    u =ᶠ[𝓝 p] (fun _ => u p) := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hu.eventually
  obtain ⟨f, hf, he⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (show HarmonicOnNhd u (ball p r) from hsub)
  have hp : p ∈ ball p r := mem_ball_self hr
  have hfd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (fun w => Complex.exp (f w)) z := by
    filter_upwards [ball_mem_nhds p hr] with z hz
    exact (Complex.differentiable_exp.differentiableAt.comp z (hf z hz).differentiableAt)
  have hfm : IsLocalMax (norm ∘ (fun w => Complex.exp (f w))) p := by
    filter_upwards [hm, ball_mem_nhds p hr] with z hz hzB
    simp only [Function.comp_apply, Complex.norm_exp, he hzB, he hp]
    exact Real.exp_le_exp.mpr hz
  have hc := Complex.norm_eventually_eq_of_isLocalMax hfd hfm
  filter_upwards [hc, ball_mem_nhds p hr] with z hz hzB
  have := hz
  simp only [Complex.norm_exp, he hzB, he hp, Real.exp_eq_exp] at this
  exact this

theorem harmonic_eqOn_of_isLocalMax {U : Set ℂ} (hU : IsPreconnected U)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u U) {p : ℂ} (hp : p ∈ U)
    (hm : IsLocalMax u p) : EqOn u (fun _ => u p) U :=
  (show AnalyticOnNhd ℝ u U from fun z hz => _root_.HarmonicAt.analyticAt (hu z hz))
    |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hp
      (harmonic_eventually_eq_of_isLocalMax (hu p hp) hm)

theorem harmonic_le_of_boundary_le {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (hb : Bornology.IsBounded U) {u : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) {C : ℝ} (hbd : ∀ z ∈ frontier U, u z ≤ C) :
    ∀ z ∈ closure U, u z ≤ C := by
  intro z hz
  obtain ⟨p, hp, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨z, hz⟩ hu.continuousOn
  suffices u p ≤ C from (hmax hz).trans this
  by_cases hpi : p ∈ U
  · have he := (harmonic_eqOn_of_isLocalMax hc hu.harmonicOnNhd hpi
      (hmax.isLocalMax (mem_of_superset (hU.mem_nhds hpi) subset_closure))).of_subset_closure
        hu.continuousOn continuousOn_const subset_closure Subset.rfl
    obtain ⟨q, hq⟩ := nonempty_frontier_iff.mpr ⟨⟨p, hpi⟩, (fun he => NormedSpace.unbounded_univ ℂ ℂ (he ▸ hb))⟩
    simpa only [he (frontier_subset_closure hq)] using hbd q hq
  · exact hbd p ⟨hp, by simpa only [hU.interior_eq] using hpi⟩

theorem harmonic_eqOn_of_boundary_eq {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (hb : Bornology.IsBounded U) {u v : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) (hv : HarmonicContOnCl v U)
    (he : EqOn u v (frontier U)) : EqOn u v (closure U) := by
  have hle := harmonic_le_of_boundary_le hU hc hb (hu.sub hv)
    (C := 0) (fun z hz => by change u z - v z ≤ 0; rw [he hz, sub_self])
  have hge := harmonic_le_of_boundary_le hU hc hb (hv.sub hu)
    (C := 0) (fun z hz => by change v z - u z ≤ 0; rw [he hz, sub_self])
  intro z hz
  exact le_antisymm (sub_nonpos.mp (hle z hz)) (sub_nonpos.mp (hge z hz))

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HarmonicReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harmonic Reflection. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem isOpen_upperHalfBall (R : ℝ) : IsOpen (upperHalfBall R) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

theorem convex_upperHalfBall (R : ℝ) : Convex ℝ (upperHalfBall R) :=
  (convex_ball _ _).inter ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)

theorem closure_upperHalfBall_subset (R : ℝ) :
    closure (upperHalfBall R) ⊆ closedUpperHalfBall R := by
  apply closure_minimal
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, show 0 ≤ z.im from le_of_lt (show 0 < z.im from hz.2)⟩
  · exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

theorem oddReflection_conj {R : ℝ} {u : ℂ → ℝ}
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : oddReflection u (conj z) = -oddReflection u z := by
  by_cases hi : z.im = 0
  · have hz' : conj z = z := Complex.ext (by simp) (by simp [hi])
    simp [oddReflection, hi, hz', hzero z hz hi]
  · rcases lt_or_gt_of_ne hi with hneg | hpos
    · simp [oddReflection, not_le.mpr hneg, (neg_pos.mpr hneg).le]
    · simp [oddReflection, hpos.le, not_le.mpr (neg_neg_of_pos hpos)]

theorem continuousOn_oddReflection {R : ℝ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedUpperHalfBall R))
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0) :
    ContinuousOn (oddReflection u) (sphere 0 R) := by
  let S : Set ℂ := {z | 0 ≤ z.im}
  have hS : IsClosed S := isClosed_le continuous_const Complex.continuous_im
  have hfront : ∀ z ∈ frontier S, z.im = 0 := by
    intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ici (0 : ℝ)) hz
    simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using hf
  have hlow : closure Sᶜ ⊆ {z : ℂ | z.im ≤ 0} := by
    apply closure_minimal
    · intro z hz
      exact (not_le.mp (show ¬ 0 ≤ z.im from hz)).le
    · exact isClosed_le Complex.continuous_im continuous_const
  change ContinuousOn (S.piecewise u (fun z => -u (conj z))) (sphere 0 R)
  apply ContinuousOn.piecewise
  · intro z hz
    have hi := hfront z hz.2
    have he : conj z = z := Complex.ext (by simp) (by simp [hi])
    rw [he, hzero z (sphere_subset_closedBall hz.1) hi, neg_zero]
  · rw [hS.closure_eq]
    exact hu.mono (fun z hz => ⟨sphere_subset_closedBall hz.1, hz.2⟩)
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa only [mem_closedBall_zero_iff, Complex.norm_conj] using
        (sphere_subset_closedBall hz.1)
    · change 0 ≤ -z.im
      exact neg_nonneg.mpr (show z.im ≤ 0 from hlow hz.2)

theorem harmonic_reflection {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (upperHalfBall R))
    (huc : ContinuousOn u (closedUpperHalfBall R))
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0) :
    HarmonicOnNhd (poissonExtension R (oddReflection u)) (ball 0 R) ∧
    EqOn (poissonExtension R (oddReflection u)) u (upperHalfBall R) ∧
    (∀ z ∈ ball (0 : ℂ) R, z.im = 0 → poissonExtension R (oddReflection u) z = 0) := by
  have hboundary := continuousOn_oddReflection huc hzero
  have hodd : ∀ z ∈ sphere (0 : ℂ) R,
      oddReflection u (conj z) = -oddReflection u z :=
    fun z hz => oddReflection_conj hzero (sphere_subset_closedBall hz)
  have hreal : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 →
      dirichletExtension R (oddReflection u) z = 0 := by
    intro z hz hi
    by_cases hb : z ∈ ball (0 : ℂ) R
    · rw [(dirichletExtension_eventuallyEq hb).eq_of_nhds]
      have he : conj z = z := Complex.ext (by simp) (by simp [hi])
      have ho := poissonExtension_conj hR.le hodd z
      rw [he] at ho
      linarith
    · have he : conj z = z := Complex.ext (by simp) (by simp [hi])
      simp only [dirichletExtension, piecewise_eq_of_notMem _ _ _ hb,
        oddReflection, hi, le_refl, ite_true, hzero z hz hi]
  have hd := harmonicContOnCl_dirichletExtension hR hboundary
  have heq := harmonic_eqOn_of_boundary_eq (isOpen_upperHalfBall R)
    (convex_upperHalfBall R).isPreconnected
    (isBounded_ball.subset inter_subset_left)
    (show HarmonicContOnCl (dirichletExtension R (oddReflection u)) (upperHalfBall R)
      from hd.mono inter_subset_left)
    (show HarmonicContOnCl u (upperHalfBall R) from
      ⟨hu, huc.mono (closure_upperHalfBall_subset R)⟩) (by
        intro z hz
        have hzc := closure_upperHalfBall_subset R (frontier_subset_closure hz)
        have hzn : z ∉ upperHalfBall R := by
          have hn := hz.2
          simpa only [(isOpen_upperHalfBall R).interior_eq] using hn
        by_cases hi : z.im = 0
        · rw [hreal z hzc.1 hi, hzero z hzc.1 hi]
        · have hpos : 0 < z.im := lt_of_le_of_ne hzc.2 (Ne.symm hi)
          have hs : z ∈ sphere (0 : ℂ) R := mem_sphere.mpr
            (le_antisymm (mem_closedBall.mp hzc.1)
              (le_of_not_gt (fun he => hzn ⟨he, hpos⟩)))
          rw [dirichletExtension_eq_on_sphere hs, oddReflection, ite_eq_left hpos.le])
  refine ⟨harmonicOnNhd_poissonExtension hR.le hboundary, ?_, ?_⟩
  · intro z hz
    rw [← (dirichletExtension_eventuallyEq hz.1).eq_of_nhds]
    exact heq (subset_closure hz)
  · intro z hz hi
    rw [← (dirichletExtension_eventuallyEq hz).eq_of_nhds]
    exact hreal z (ball_subset_closedBall hz) hi

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ReflectionDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflection Derivative. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem circleAverage_neg {R : ℝ} (hR : 0 < R) {v : ℂ → ℝ}
    (hv : ContinuousOn v (sphere 0 R)) (hle : ∀ z ∈ sphere 0 R, v z ≤ 0)
    (hlt : v ((R : ℂ) * I) < 0) : circleAverage v 0 R < 0 := by
  have hmap : MapsTo (circleMap 0 R) (Icc 0 (2 * π)) (sphere 0 R) :=
    fun t _ => by simpa only [abs_of_pos hR] using circleMap_mem_sphere' 0 R t
  have hc : ContinuousOn (fun t => v (circleMap 0 R t)) (Icc 0 (2 * π)) :=
    hv.comp (continuous_circleMap 0 R).continuousOn hmap
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0 : ℝ) < 2 * π by positivity) hc continuousOn_const
    (fun t ht => hle _ (hmap (Ioc_subset_Icc_self ht))) (show ∃ t ∈ Icc 0 (2 * π), v (circleMap 0 R t) < 0 from
      ⟨π / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, by
        simpa only [circleMap, zero_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
          Real.sin_pi_div_two, Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_add]
          using hlt⟩)
  simp only [intervalIntegral.integral_zero] at hi
  simpa only [circleAverage, smul_eq_mul] using
    mul_neg_of_pos_of_neg (inv_pos.mpr (by positivity : 0 < 2 * π)) hi

theorem im_deriv_schwarzExtension_zero {R : ℝ} (hR : 0 < R) {v : ℂ → ℝ}
    (hv : ContinuousOn v (sphere 0 R)) :
    (deriv (schwarzExtension R v) 0).im =
      -2 / R ^ 2 * circleAverage (fun z => z.im * v z) 0 R := by
  have hvi : CircleIntegrable (fun z => (v z : ℂ)) 0 R :=
    ContinuousOn.circleIntegrable hR.le (continuous_ofReal.comp_continuousOn hv)
  have hd := hasDerivAt_circleAverage_herglotzRieszKernel_smul hvi
    (Metric.mem_ball_self hR : (0 : ℂ) ∈ ball 0 R)
  have he : deriv (schwarzExtension R v) 0 =
      circleAverage (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ)) 0 R := by
    rw [show schwarzExtension R v =
      (fun w => circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (v ζ : ℂ)) 0 R) by rfl,
      hd.deriv]
    apply circleAverage_congr_sphere
    intro ζ hζ
    have hz : ζ ≠ 0 := by
      intro he
      have hn : ‖ζ‖ = R := by simpa only [abs_of_pos hR] using mem_sphere_zero_iff_norm.mp hζ
      exact hR.ne' (by simpa only [he, norm_zero] using hn.symm)
    simp only [sub_zero, smul_eq_mul]
    congr 1
    field_simp
  have hgi : CircleIntegrable (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ)) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    refine (continuousOn_const.div continuousOn_id (fun ζ hζ => ?_)).mul
      (continuous_ofReal.comp_continuousOn hv)
    intro he
    change ζ = 0 at he
    have hn := mem_sphere_zero_iff_norm.mp hζ
    exact hR.ne' (by simpa only [he, norm_zero] using hn.symm)
  rw [he]
  change Complex.imCLM (circleAverage (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ)) 0 R) = _
  rw [← Complex.imCLM.circleAverage_comp_comm hgi]
  have heq : circleAverage (Complex.imCLM ∘ (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ))) 0 R =
      circleAverage (fun z => (-2 / R ^ 2) • (z.im * v z)) 0 R := by
    apply circleAverage_congr_sphere
    intro z hz
    have hn : ‖z‖ = R := by simpa only [abs_of_pos hR] using mem_sphere_zero_iff_norm.mp hz
    simp only [Function.comp_apply, Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, Complex.div_im, Complex.im_ofNat,
      Complex.re_ofNat, zero_mul, Complex.normSq_eq_norm_sq, hn, smul_eq_mul]
    ring
  rw [heq, circleAverage_fun_smul, smul_eq_mul]

theorem deriv_schwarzExtension_odd_ne_zero {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn (oddReflection u) (sphere 0 R))
    (hneg : ∀ z ∈ sphere (0 : ℂ) R, 0 < z.im → u z < 0) :
    deriv (schwarzExtension R (oddReflection u)) 0 ≠ 0 := by
  have hp : (R : ℂ) * I ∈ sphere (0 : ℂ) R := by
    simp only [mem_sphere_zero_iff_norm, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
  have him : ((R : ℂ) * I).im = R := by simp
  have hle : ∀ z ∈ sphere (0 : ℂ) R, z.im * oddReflection u z ≤ 0 := by
    intro z hz
    rcases lt_trichotomy z.im 0 with hn | he | hp
    · rw [oddReflection, ite_eq_right (not_le.mpr hn)]
      have hconj : conj z ∈ sphere (0 : ℂ) R := by
        simpa only [mem_sphere_zero_iff_norm, Complex.norm_conj] using hz
      have hn' := hneg (conj z) hconj (by simpa only [conj_im] using neg_pos.mpr hn)
      exact mul_nonpos_of_nonpos_of_nonneg hn.le (neg_nonneg.mpr hn'.le)
    · rw [he, zero_mul]
    · rw [oddReflection, ite_eq_left hp.le]
      exact mul_nonpos_of_nonneg_of_nonpos hp.le (hneg z hz hp).le
  have hav := circleAverage_neg hR (Complex.continuous_im.continuousOn.mul hu) hle
    (show ((R : ℂ) * I).im * oddReflection u ((R : ℂ) * I) < 0 by
      rw [him, oddReflection, him, ite_eq_left hR.le]
      exact mul_neg_of_pos_of_neg hR (hneg _ hp (by simpa only [him] using hR)))
  have hpim : 0 < (deriv (schwarzExtension R (oddReflection u)) 0).im := by
    rw [im_deriv_schwarzExtension_zero hR hu]
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hR)) hav
  intro he
  simp only [he, zero_im, lt_irrefl] at hpim

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HolomorphicReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic Reflection. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem holomorphic_reflection {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ} {f : ℂ → ℂ}
    (hu : HarmonicOnNhd u (upperHalfBall R))
    (huc : ContinuousOn u (closedUpperHalfBall R))
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) R, 0 < z.im → u z < 0)
    (hf : DifferentiableOn ℂ f (upperHalfBall R))
    (hfn : ∀ z ∈ upperHalfBall R, f z ≠ 0)
    (hlog : EqOn (fun z => Real.log ‖f z‖) u (upperHalfBall R)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧
      EqOn g f (upperHalfBall R) ∧ deriv g 0 ≠ 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, z.im = 0 → ‖g z‖ = 1) := by
  let H := schwarzExtension R (oddReflection u)
  have hbound := continuousOn_oddReflection huc hzero
  have hHa : AnalyticOnNhd ℂ H (ball 0 R) := analyticOnNhd_schwarzExtension hR.le hbound
  have hHe : EqOn (fun z => (H z).re) u (upperHalfBall R) := by
    intro z hz
    exact (schwarzExtension_re (ContinuousOn.circleIntegrable hR.le hbound) hz.1).trans
      ((harmonic_reflection hR hu huc hzero).2.1 hz)
  let q : ℂ → ℂ := fun z => f z / Complex.exp (H z)
  have hqd : DifferentiableOn ℂ q (upperHalfBall R) := by
    apply hf.div
    · intro z hz
      exact ((hHa z hz.1).cexp.differentiableAt).differentiableWithinAt
    · exact fun z _ => Complex.exp_ne_zero (H z)
  have hqn : ∀ z ∈ upperHalfBall R, ‖q z‖ = 1 := by
    intro z hz
    dsimp [q]
    rw [norm_div, Complex.norm_exp, show (H z).re = u z from hHe hz, ← (show Real.log ‖f z‖ = u z from hlog hz),
      Real.exp_log (norm_pos_iff.mpr (hfn z hz)), div_self (norm_ne_zero_iff.mpr (hfn z hz))]
  let p : ℂ := (R / 2 : ℝ) * I
  have hp : p ∈ upperHalfBall R := by
    constructor
    · simp only [p, mem_ball_zero_iff, norm_mul, norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (half_pos hR).le]
      linarith
    · change 0 < p.im
      simpa [p] using half_pos hR
  have hqc : EqOn q (fun _ => q p) (upperHalfBall R) :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_upperHalfBall R).isPreconnected
      (isOpen_upperHalfBall R) hqd hp (fun z hz => by
        change ‖q z‖ ≤ ‖q p‖
        rw [hqn z hz, hqn p hp])
  have hqpn : q p ≠ 0 := by
    intro he
    simpa only [he, norm_zero, zero_ne_one] using hqn p hp
  refine ⟨fun z => q p * Complex.exp (H z), ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul (hHa z hz).cexp
  · intro z hz
    have he := (div_eq_iff (Complex.exp_ne_zero (H z))).mp (hqc hz)
    exact he.symm
  · have hd := ((hHa 0 (mem_ball_self hR)).differentiableAt.hasDerivAt.cexp).const_mul (q p)
    rw [hd.deriv]
    exact mul_ne_zero hqpn (mul_ne_zero (Complex.exp_ne_zero _) (deriv_schwarzExtension_odd_ne_zero hR hbound hneg))
  · intro z hz hi
    have hr : (H z).re = 0 :=
      (schwarzExtension_re (ContinuousOn.circleIntegrable hR.le hbound) hz).trans
        ((harmonic_reflection hR hu huc hzero).2.2 z hz hi)
    rw [norm_mul, hqn p hp, Complex.norm_exp, hr, Real.exp_zero, mul_one]

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem exists_extension_at_boundary {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    {p : ℂ} (hp : p ∈ frontier U) (c : BoundaryChart U p) :
    ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ AnalyticOnNhd ℂ g (ball p r) ∧
      EqOn g f (U ∩ ball p r) ∧ deriv g p ≠ 0 := by
  obtain ⟨a, ha, hfa⟩ := hbij.surjOn (mem_ball_self (by norm_num) : (0 : ℂ) ∈ ball 0 1)
  have hpa : p ≠ a := by
    rintro rfl
    exact hp.2 (hU.interior_eq.symm ▸ ha)
  have hχa : ∀ᶠ z in 𝓝 (0 : ℂ), c.e z ≠ a :=
    (c.analytic 0 c.zero_mem).continuousAt.preimage_mem_nhds
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa only [mem_compl_iff, mem_singleton_iff, c.at_zero] using hpa))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (c.e.open_source.mem_nhds c.zero_mem) hχa)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hsub : closedBall (0 : ℂ) r ⊆ c.e.source := fun z hz =>
    (hball ((closedBall_subset_ball (by dsimp [r]; linarith)) hz)).1
  have hne : ∀ z ∈ closedBall (0 : ℂ) r, c.e z ≠ a := fun z hz =>
    (hball ((closedBall_subset_ball (by dsimp [r]; linarith)) hz)).2
  have hfu : ∀ z ∈ closedBall (0 : ℂ) r, 0 < z.im → f (c.e z) ≠ 0 := by
    intro z hz hi he
    exact hne z hz (hbij.injOn ((c.side z (hsub hz)).mpr hi) ha (he.trans hfa.symm))
  let M : ℂ → ℝ := fun z => if z ∈ U then ‖f z‖ else 1
  let u : ℂ → ℝ := fun z => Real.log (M (c.e z))
  have huEq : EqOn u (fun z => Real.log ‖f (c.e z)‖) (upperHalfBall r) := by
    intro z hz
    simp only [u, M, ite_eq_left ((c.side z (hsub (ball_subset_closedBall hz.1))).mpr hz.2)]
  have hχU : MapsTo c.e (upperHalfBall r) U := fun z hz =>
    (c.side z (hsub (ball_subset_closedBall hz.1))).mpr hz.2
  have hfχ : DifferentiableOn ℂ (f ∘ c.e) (upperHalfBall r) :=
    hf.comp (c.analytic.differentiableOn.mono (inter_subset_left.trans (ball_subset_closedBall.trans hsub))) hχU
  have hu : HarmonicOnNhd u (upperHalfBall r) := by
    intro z hz
    have hg := (hfχ.analyticOnNhd (isOpen_upperHalfBall r) z hz).harmonicAt_log_norm
      (hfu z (ball_subset_closedBall hz.1) hz.2)
    exact (harmonicAt_congr_nhds (huEq.eventuallyEq_of_mem ((isOpen_upperHalfBall r).mem_nhds hz))).mpr hg
  have hχclosed : MapsTo c.e (closedUpperHalfBall r) (closure U) := fun z hz =>
    (c.closed_side z (hsub hz.1)).mpr hz.2
  have hMn : ∀ z ∈ closedUpperHalfBall r, M (c.e z) ≠ 0 := by
    intro z hz
    by_cases hi : c.e z ∈ U
    · simp only [M, ite_eq_left hi]
      exact norm_ne_zero_iff.mpr (hfu z hz.1 ((c.side z (hsub hz.1)).mp hi))
    · simp only [M, ite_eq_right hi, ne_eq, one_ne_zero, not_false_eq_true]
  have huc : ContinuousOn u (closedUpperHalfBall r) :=
    ((continuousOn_closed_modulus hU hf hbij).comp
      (c.analytic.continuousOn.mono (inter_subset_left.trans hsub)) hχclosed).log hMn
  have hu0 : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 → u z = 0 := by
    intro z hz hi
    have hn : c.e z ∉ U := fun he => (lt_irrefl (0 : ℝ)) (hi ▸ (c.side z (hsub hz)).mp he)
    simp only [u, M, ite_eq_right hn, Real.log_one]
  have hneg : ∀ z ∈ sphere (0 : ℂ) r, 0 < z.im → u z < 0 := by
    intro z hz hi
    have hzU := (c.side z (hsub (sphere_subset_closedBall hz))).mpr hi
    simp only [u, M, ite_eq_left hzU]
    exact Real.log_neg (norm_pos_iff.mpr (hfu z (sphere_subset_closedBall hz) hi))
      (mem_ball_zero_iff.mp (hbij.mapsTo hzU))
  obtain ⟨g, hga, hge, hgd, _⟩ := holomorphic_reflection hr hu huc hu0 hneg hfχ
    (fun z hz => hfu z (ball_subset_closedBall hz.1) hz.2) huEq.symm
  have hpT : p ∈ c.e.target := by simpa only [c.at_zero] using c.e.map_source c.zero_mem
  have hpInv : c.e.symm p = 0 := by simpa only [c.at_zero] using c.e.left_inv c.zero_mem
  have hcont := (c.inverse_analytic p hpT).continuousAt
  have hnb : ∀ᶠ z in 𝓝 p, c.e.symm z ∈ ball 0 r :=
    hcont.preimage_mem_nhds (hpInv.symm ▸ ball_mem_nhds (0 : ℂ) hr)
  obtain ⟨s, hs, hsSub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (c.e.open_target.mem_nhds hpT) hnb)
  refine ⟨s, g ∘ c.e.symm, hs, ?_, ?_, ?_⟩
  · intro z hz
    exact (hga _ (hsSub hz).2).comp (c.inverse_analytic z (hsSub hz).1)
  · intro z hz
    have hzt := (hsSub hz.2).1
    have hzs := c.e.map_target hzt
    have hi : 0 < (c.e.symm z).im := (c.side _ hzs).mp (by simpa only [c.e.right_inv hzt] using hz.1)
    simpa only [Function.comp_apply, c.e.right_inv hzt] using hge ⟨(hsSub hz.2).2, hi⟩
  · rw [deriv_comp p (hga _ (hpInv.symm ▸ mem_ball_self hr)).differentiableAt
      (c.inverse_analytic p hpT).differentiableAt, hpInv]
    exact mul_ne_zero hgd (deriv_ne_zero_of_injOn c.e.open_target
      c.inverse_analytic.differentiableOn c.e.symm.injOn hpT)

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Patching. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem extension_eqOn_lens {U : Set ℂ} (hU : IsOpen U) {f g₁ g₂ : ℂ → ℂ}
    {p q : ℂ} (hp : p ∈ closure U) (hq : q ∈ closure U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hg₁ : AnalyticOnNhd ℂ g₁ (ball p r)) (hg₂ : AnalyticOnNhd ℂ g₂ (ball q s))
    (he₁ : EqOn g₁ f (U ∩ ball p r)) (he₂ : EqOn g₂ f (U ∩ ball q s))
    (hover : (ball p (r / 3) ∩ ball q (s / 3)).Nonempty) :
    EqOn g₁ g₂ (ball p r ∩ ball q s) := by
  let L := ball p r ∩ ball q s
  have hL : IsOpen L := isOpen_ball.inter isOpen_ball
  have hLU : (L ∩ U).Nonempty := by
    obtain ⟨z, hzp, hzq⟩ := hover
    have hpq : dist p q < (r + s) / 3 := by
      have h := dist_triangle p z q
      rw [dist_comm p z] at h
      have := mem_ball.mp hzp
      have := mem_ball.mp hzq
      linarith
    rcases le_total s r with hsr | hrs
    · have hqL : q ∈ L := ⟨by rw [mem_ball, dist_comm]; linarith, mem_ball_self hs⟩
      exact (mem_closure_iff_nhds.mp hq) L (hL.mem_nhds hqL)
    · have hpL : p ∈ L := ⟨mem_ball_self hr, by rw [mem_ball]; linarith⟩
      exact (mem_closure_iff_nhds.mp hp) L (hL.mem_nhds hpL)
  obtain ⟨z, hzL, hzU⟩ := hLU
  apply (hg₁.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hg₂.mono inter_subset_right) ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected hzL
  filter_upwards [(hL.inter hU).mem_nhds ⟨hzL, hzU⟩] with w hw
  exact (he₁ ⟨hw.2, hw.1.1⟩).trans (he₂ ⟨hw.2, hw.1.2⟩).symm

theorem exists_extension_to_closure {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ g V ∧ EqOn g f U ∧
      (∀ p ∈ closure U, deriv g p ≠ 0) ∧ (∀ p ∈ frontier U, ‖g p‖ = 1) := by
  have hl : ∀ p : frontier U, ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      AnalyticOnNhd ℂ g (ball (p : ℂ) r) ∧ EqOn g f (U ∩ ball (p : ℂ) r) ∧ deriv g p ≠ 0 :=
    fun p => exists_extension_at_boundary hU hf hbij p.property (hchart p p.property).some
  choose r G hr hGa hGe hGd using hl
  let B : frontier U → Set ℂ := fun p => ball (p : ℂ) (r p / 3)
  have hBsub : ∀ p, B p ⊆ ball (p : ℂ) (r p) := fun p =>
    ball_subset_ball (by have := hr p; linarith)
  let V := U ∪ ⋃ p, B p
  let g : ℂ → ℂ := fun z => if z ∈ U then f z else
    if h : ∃ p : frontier U, z ∈ B p then G h.choose z else 0
  have hgu : EqOn g f U := by intro z hz; simp only [g, ite_eq_left hz]
  have hgb : ∀ p, EqOn g (G p) (B p) := by
    intro p z hz
    by_cases hzu : z ∈ U
    · exact (hgu hzu).trans (hGe p ⟨hzu, hBsub p hz⟩).symm
    · have h : ∃ q : frontier U, z ∈ B q := ⟨p, hz⟩
      simp only [g, ite_eq_right hzu, dite_eq_left h]
      exact extension_eqOn_lens hU h.choose.property.1 p.property.1
        (hr h.choose) (hr p) (hGa h.choose) (hGa p) (hGe h.choose) (hGe p)
        ⟨z, h.choose_spec, hz⟩ ⟨hBsub h.choose h.choose_spec, hBsub p hz⟩
  have hVo : IsOpen V := hU.union (isOpen_iUnion (fun _ => isOpen_ball))
  have hUV : closure U ⊆ V := by
    intro z hz
    by_cases hzu : z ∈ U
    · exact Or.inl hzu
    · let p : frontier U := ⟨z, hz, by simpa only [hU.interior_eq] using hzu⟩
      exact Or.inr (mem_iUnion.mpr ⟨p, mem_ball_self (by have := hr p; positivity)⟩)
  have hga : AnalyticOnNhd ℂ g V := by
    intro z hz
    rcases hz with hzU | hzB
    · exact ((hf.analyticOnNhd hU) z hzU).congr
        (hgu.eventuallyEq_of_mem (hU.mem_nhds hzU)).symm
    · obtain ⟨p, hp⟩ := mem_iUnion.mp hzB
      exact (hGa p z (hBsub p hp)).congr
        ((hgb p).eventuallyEq_of_mem (isOpen_ball.mem_nhds hp)).symm
  refine ⟨V, g, hVo, hUV, hga, hgu, ?_, ?_⟩
  · intro z hz
    by_cases hzU : z ∈ U
    · rw [(hgu.eventuallyEq_of_mem (hU.mem_nhds hzU)).deriv_eq]
      exact deriv_ne_zero_of_injOn hU hf hbij.injOn hzU
    · let p : frontier U := ⟨z, hz, by simpa only [hU.interior_eq] using hzU⟩
      have hn : B p ∈ 𝓝 z := ball_mem_nhds z (by have := hr p; positivity)
      rw [((hgb p).eventuallyEq_of_mem hn).deriv_eq]
      exact hGd p
  · intro p hp
    have : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp.1
    apply tendsto_nhds_unique ((hga p (hUV hp.1)).continuousAt.norm.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[U] p ≤ 𝓝 p))
    apply (tendsto_norm_one_at_frontier hU hf hbij hp).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact congrArg norm (hgu hz).symm

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CollarUnivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collar Univalence. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem inverseBranch_into_domain {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : MapsTo g U (ball 0 1)) (hfront : ∀ p ∈ frontier U, ‖g p‖ = 1)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = g)
    {p : ℂ} (hp : p ∈ closure U) (hpe : p ∈ e.source)
    {δ : ℝ} (hδ : 0 < δ) (hδe : ball (g p) δ ⊆ e.target) :
    MapsTo e.symm (ball (g p) δ ∩ ball 0 1) U := by
  let L := ball (g p) δ ∩ ball 0 1
  have hLt : L ⊆ e.target := inter_subset_left.trans hδe
  have hconn : IsPreconnected (e.symm '' L) :=
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected.image _
      (e.continuousOn_symm.mono hLt)
  have hn : e.source ∩ g ⁻¹' ball (g p) δ ∈ 𝓝 p :=
    inter_mem (e.open_source.mem_nhds hpe)
      ((he ▸ e.continuousAt hpe).preimage_mem_nhds (ball_mem_nhds _ hδ))
  obtain ⟨x, hxN, hxU⟩ := (mem_closure_iff_nhds.mp hp) _ hn
  have hnon : (e.symm '' L ∩ U).Nonempty := by
    refine ⟨x, ⟨g x, ⟨hxN.2, hg hxU⟩, ?_⟩, hxU⟩
    simpa only [he] using e.left_inv hxN.1
  have hcl : closure U ∩ e.symm '' L ⊆ U := by
    rintro x ⟨hx, z, hz, rfl⟩
    by_contra hnU
    have hpF : e.symm z ∈ frontier U := ⟨hx, by simpa only [hU.interior_eq] using hnU⟩
    have hmod := hfront _ hpF
    have heq : g (e.symm z) = z := by simpa only [he] using e.right_inv (hLt hz)
    rw [heq] at hmod
    exact (ne_of_lt (mem_ball_zero_iff.mp hz.2)) hmod
  exact fun z hz => (hconn.subset_of_closure_inter_subset hU hnon hcl) ⟨z, hz, rfl⟩

theorem injOn_closure_of_boundary_modulus {U V : Set ℂ} (hU : IsOpen U)
    (hUV : closure U ⊆ V) {g : ℂ → ℂ} (hga : AnalyticOnNhd ℂ g V)
    (hbij : BijOn g U (ball 0 1))
    (hgd : ∀ p ∈ closure U, deriv g p ≠ 0)
    (hfront : ∀ p ∈ frontier U, ‖g p‖ = 1) : InjOn g (closure U) := by
  intro p hp q hq hpq
  let dp := ((hga p (hUV hp)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hgd p hp))
  let dq := ((hga q (hUV hq)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hgd q hq))
  let ep := dp.toOpenPartialHomeomorph g
  let eq := dq.toOpenPartialHomeomorph g
  have hps : p ∈ ep.source := dp.mem_toOpenPartialHomeomorph_source
  have hqs : q ∈ eq.source := dq.mem_toOpenPartialHomeomorph_source
  have hη : g p ∈ ep.target ∩ eq.target :=
    ⟨ep.map_source hps, hpq.symm ▸ eq.map_source hqs⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (ep.open_target.inter eq.open_target) (g p) hη
  let L := ball (g p) δ ∩ ball 0 1
  have hpU := inverseBranch_into_domain hU hbij.mapsTo hfront ep rfl hp hps hδ
    (hδsub.trans inter_subset_left)
  have hqU := inverseBranch_into_domain hU hbij.mapsTo hfront eq rfl hq hqs hδ
    (hpq ▸ hδsub.trans inter_subset_right)
  have heqL : EqOn ep.symm eq.symm L := by
    intro z hz
    have hzq : z ∈ ball (g q) δ ∩ ball 0 1 := hpq ▸ hz
    apply hbij.injOn (hpU hz) (hqU hzq)
    exact (ep.right_inv (hδsub hz.1).1).trans (eq.right_inv (hδsub hz.1).2).symm
  have hle : ‖g p‖ ≤ 1 := by
    by_cases hpU : p ∈ U
    · exact (mem_ball_zero_iff.mp (hbij.mapsTo hpU)).le
    · exact (hfront p ⟨hp, by simpa only [hU.interior_eq] using hpU⟩).le
  have hcl : g p ∈ closure L := by
    have hn : ball (g p) δ ∈ 𝓝 (g p) := ball_mem_nhds _ hδ
    have hc : g p ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0), mem_closedBall_zero_iff]
      exact hle
    exact mem_closure_iff_nhds.mpr fun N hN => by
      obtain ⟨z, hzN, hzD⟩ := mem_closure_iff_nhds.mp hc _ (inter_mem hN hn)
      exact ⟨z, hzN.1, hzN.2, hzD⟩
  have : NeBot (𝓝[L] (g p)) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have heq : ep.symm (g p) = eq.symm (g p) :=
    tendsto_nhds_unique ((ep.continuousAt_symm hη.1).continuousWithinAt.tendsto)
      (((eq.continuousAt_symm hη.2).continuousWithinAt.tendsto).congr'
        (heqL.eventuallyEq_of_mem self_mem_nhdsWithin).symm)
  have hlp : ep.symm (g p) = p := ep.left_inv hps
  have hlq : eq.symm (g q) = q := eq.left_inv hqs
  rw [hlp] at heq
  rw [hpq, hlq] at heq
  exact heq

theorem exists_univalent_extension {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ g V ∧ EqOn g f U ∧ InjOn g V ∧
      (∀ p ∈ frontier U, ‖g p‖ = 1) := by
  obtain ⟨V, g, hV, hUV, hga, hgf, hgd, hfront⟩ :=
    exists_extension_to_closure hU hf hbij hchart
  have hbijg : BijOn g U (ball 0 1) := hbij.congr hgf.symm
  have hgi := injOn_closure_of_boundary_modulus hU hUV hga hbijg hgd hfront
  have hloc : ∀ x ∈ closure U, ∃ s ∈ 𝓝 x, InjOn g s := by
    intro x hx
    let d := (hga x (hUV hx)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hgd x hx)
    let e := d.toOpenPartialHomeomorph g
    have he : x ∈ e.source := d.mem_toOpenPartialHomeomorph_source
    exact ⟨e.source, e.open_source.mem_nhds he, e.injOn⟩
  obtain ⟨W, hW, hUW, hgiW⟩ := hgi.exists_isOpen_superset hb.isCompact_closure
    (fun x hx => (hga x (hUV hx)).continuousAt) hloc
  exact ⟨V ∩ W, g, hV.inter hW, subset_inter hUV hUW,
    hga.mono inter_subset_left, hgf, hgiW.mono inter_subset_right, hfront⟩

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Convexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the numerical range and its closure. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem phase_real (u v : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (c * u + star c * v).im = 0 := by
  let d : ℂ := u - star v
  have him (c : ℂ) : (c * u + star c * v).im = (c * d).im := by
    simp only [d, mul_sub, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  by_cases hd : d = 0
  · refine ⟨1, norm_one, ?_⟩
    rw [him, hd, mul_zero, Complex.zero_im]
  · refine ⟨(‖d‖ : ℂ)⁻¹ * star d, ?_, ?_⟩
    · simp [hd]
    · rw [him, mul_assoc]
      simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_inv,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem unit_interval_of_quadratic_endpoints (B : Operator H)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hBx : ⟪x, B x⟫_ℂ = 0) (hBy : ⟪y, B y⟫_ℂ = 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ w : H, ‖w‖ = 1 ∧ ⟪w, B w⟫_ℂ = (t : ℂ) := by
  obtain ⟨c, hc, hcross⟩ := phase_real ⟪x, B y⟫_ℂ ⟪y, B x⟫_ℂ
  let y' : H := c • y
  have hy' : ‖y'‖ = 1 := by simp [y', norm_smul, hc, hy]
  have hy'B : ⟪y', B y'⟫_ℂ = 1 := by
    simp only [y', map_smul, inner_smul_left, inner_smul_right, hBy, mul_one,
      Complex.mul_conj', hc, Complex.ofReal_one, one_pow]
  have hc' : (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ).im = 0 := by
    simpa only [y', map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply] using hcross
  let q : ℝ → H := fun s => ((1 - s : ℝ) : ℂ) • x + (s : ℂ) • y'
  have hq0 (s : ℝ) : q s ≠ 0 := by
    intro hz
    have heq : (((1 - s : ℝ) : ℂ) • x) = -(s : ℂ) • y' := by
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hz
    have hq := congrArg (fun z : H => ⟪z, B z⟫_ℂ) heq
    simp only [map_smul, inner_smul_left, inner_smul_right, hBx, hy'B, mul_zero,
      mul_one, map_neg, Complex.conj_ofReal, neg_mul_neg] at hq
    have hs : s = 0 := by
      have hh := congrArg Complex.re hq
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.zero_re] at hh
      nlinarith
    simp [q, hs] at hz
    rw [hz] at hx
    norm_num at hx
  have hq : Continuous q := by
    dsimp [q]
    fun_prop
  have hqi (s : ℝ) : (⟪q s, B (q s)⟫_ℂ).im = 0 := by
    have heq : ⟪q s, B (q s)⟫_ℂ = (s : ℂ) ^ 2 +
        (s : ℂ) * (1 - (s : ℂ)) * (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ) := by
      simp only [q, map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal, hBx, hy'B, map_sub, map_one,
        mul_zero, mul_one, zero_add, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rw [heq]
    simp [Complex.add_im, Complex.mul_im, hc', pow_two]
  let g : ℝ → H := fun s => (‖q s‖ : ℂ)⁻¹ • q s
  have hg (s : ℝ) : ‖g s‖ = 1 := by
    simp [g, norm_smul, hq0 s]
  have hgc : Continuous g := by
    apply Continuous.smul _ hq
    apply Continuous.inv₀ (Complex.continuous_ofReal.comp hq.norm)
    intro s
    change (‖q s‖ : ℂ) ≠ 0
    exact_mod_cast norm_ne_zero_iff.mpr (hq0 s)
  have hgi (s : ℝ) : (⟪g s, B (g s)⟫_ℂ).im = 0 := by
    simp only [g, map_smul, inner_smul_left, inner_smul_right, ← Complex.ofReal_inv,
      Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hqi s]
    ring
  let f : ℝ → ℝ := fun s => (⟪g s, B (g s)⟫_ℂ).re
  have hfc : Continuous f := Complex.continuous_re.comp (hgc.inner (𝕜 := ℂ) (B.continuous.comp hgc))
  have hf0 : f 0 = 0 := by simp [f, g, q, hx, hBx]
  have hf1 : f 1 = 1 := by simp [f, g, q, hy', hy'B]
  have hmem : t ∈ Icc (f 0) (f 1) := by simpa only [hf0, hf1] using ht
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hfc.continuousOn hmem
  refine ⟨g s, hg s, ?_⟩
  apply Complex.ext
  · exact hs
  · exact hgi s

theorem convex_numericalRange (A : Operator H) : Convex ℝ (numericalRange A) := by
  intro a ha b hb α β hα hβ hsum
  by_cases hab : a = b
  · subst b
    rw [← add_smul, hsum, one_smul]
    exact ha
  obtain ⟨x, hx, hAx⟩ := ha
  obtain ⟨y, hy, hAy⟩ := hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let B : Operator H := (b - a)⁻¹ • (A - a • 1)
  have hform (v : H) (hv : ‖v‖ = 1) :
      ⟪v, B v⟫_ℂ = (b - a)⁻¹ * (⟪v, A v⟫_ℂ - a) := by
    simp [B, inner_self_eq_norm_sq_to_K, hv]
  have hBx : ⟪x, B x⟫_ℂ = 0 := by rw [hform x hx, hAx, sub_self, mul_zero]
  have hBy : ⟪y, B y⟫_ℂ = 1 := by rw [hform y hy, hAy, inv_mul_cancel₀ hba]
  obtain ⟨w, hw, hwB⟩ := unit_interval_of_quadratic_endpoints B x y hx hy hBx hBy
    β ⟨hβ, by linarith⟩
  refine ⟨w, hw, ?_⟩
  rw [hform w hw] at hwB
  have hid := congrArg (fun z : ℂ => (b - a) * z) hwB
  simp only [← mul_assoc, mul_inv_cancel₀ hba, one_mul] at hid
  have hsumC : (α : ℂ) + (β : ℂ) = 1 := by exact_mod_cast hsum
  calc
    ⟪w, A w⟫_ℂ = (⟪w, A w⟫_ℂ - a) + a := by ring
    _ = (b - a) * (β : ℂ) + a := by rw [hid]
    _ = α • a + β • b := by
      simp only [Complex.real_smul]
      linear_combination -a * hsumC

theorem convex_numericalClosure (A : Operator H) : Convex ℝ (numericalClosure A) :=
  (convex_numericalRange A).closure

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Homotopy. -/

noncomputable section

open scoped InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem numericalClosure_operatorHomotopy_subset (A : Operator H) {a : ℂ}
    (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    numericalClosure (operatorHomotopy A a s) ⊆ numericalClosure A := by
  apply closure_minimal _ isClosed_closure
  rintro z ⟨x, hx, rfl⟩
  have h := (convex_numericalClosure A).add_smul_sub_mem ha
    (subset_closure (show ⟪x, A x⟫_ℂ ∈ numericalRange A from ⟨x, hx, rfl⟩)) hs
  simpa [operatorHomotopy, ContinuousLinearMap.algebraMap_apply,
    inner_self_eq_norm_sq_to_K, hx] using! h

theorem homotopy_resolvent_isUnit [CompleteSpace H] (A : Operator H) {a z : ℂ}
    (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : z ∉ numericalClosure A) :
    IsUnit (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) := by
  change z ∈ resolventSet ℂ (operatorHomotopy A a s)
  by_contra he
  exact hz (numericalClosure_operatorHomotopy_subset A ha hs
    (spectrum_subset_numericalClosure _ he))

theorem continuousOn_homotopyResolvent [CompleteSpace H] (A : Operator H)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (fun p : ℝ × ℂ => homotopyResolvent A a p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (numericalClosure A)ᶜ) := by
  have hc : Continuous (fun p : ℝ × ℂ =>
      algebraMap ℂ (Operator H) p.2 - operatorHomotopy A a p.1) :=
    by simp only [operatorHomotopy, Algebra.algebraMap_eq_smul_one]; fun_prop
  intro p hp
  exact ((differentiableAt_inverse (𝕜 := ℝ)
    (homotopy_resolvent_isUnit A ha hp.1 hp.2)).continuousAt.comp
      (f := fun q : ℝ × ℂ => algebraMap ℂ (Operator H) q.2 - operatorHomotopy A a q.1)
      (x := p) hc.continuousAt).continuousWithinAt

theorem commute_homotopyResolvent (A : Operator H) (a : ℂ) (s : ℝ) (z : ℂ) :
    Commute (A - algebraMap ℂ (Operator H) a) (homotopyResolvent A a s z) := by
  let D := A - algebraMap ℂ (Operator H) a
  have hc : Commute D (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) := by
    apply Commute.sub_right (Algebra.commutes z D).symm
    exact (show Commute D (algebraMap ℂ (Operator H) a) from (Algebra.commutes a D).symm).add_right ((Commute.refl D).smul_right s)
  by_cases hu : IsUnit (algebraMap ℂ (Operator H) z - operatorHomotopy A a s)
  · rcases hu with ⟨v, hv⟩
    change Commute D (Ring.inverse _)
    rw [← hv, Ring.inverse_unit]
    exact (show Commute D (v : Operator H) from hv.symm ▸ hc).units_inv_right
  · simp only [homotopyResolvent, Ring.inverse_non_unit _ hu]
    exact Commute.zero_right _

theorem hasDerivAt_homotopyResolvent [CompleteSpace H] (A : Operator H)
    {a z : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : z ∉ numericalClosure A) :
    HasDerivAt (fun r : ℝ => homotopyResolvent A a r z)
      (homotopyResolvent A a s z * (A - algebraMap ℂ (Operator H) a) *
        homotopyResolvent A a s z) s := by
  have hu := homotopy_resolvent_isUnit A ha hs hz
  have h₁ : HasFDerivAt Ring.inverse _
      (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) :=
    hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have h₂ : HasDerivAt (fun r : ℝ => algebraMap ℂ (Operator H) z - operatorHomotopy A a r)
      (-(A - algebraMap ℂ (Operator H) a)) s := by
    simpa only [operatorHomotopy, one_smul, zero_add, zero_sub, id_eq] using!
      (((hasDerivAt_id s).smul_const (A - algebraMap ℂ (Operator H) a)).const_add
        (algebraMap ℂ (Operator H) a)).const_sub (algebraMap ℂ (Operator H) z)
  simpa only [homotopyResolvent, Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ← Ring.inverse_unit hu.unit, hu.unit_spec,
    mul_neg, neg_mul, neg_neg] using! h₁.comp_hasDerivAt s h₂

theorem hasDerivAt_homotopyResolvent_path [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => homotopyResolvent A a s (Γ.path r))
      (-(deriv Γ.path t) • (homotopyResolvent A a s (Γ.path t)) ^ 2) t := by
  have hu := homotopy_resolvent_isUnit A ha hs (Γ.avoids t ht).2
  have h₁ := spectrum.hasDerivAt_resolvent_const_left (𝕜 := ℂ) hu
  have h₂ : HasDerivAt Γ.path (deriv Γ.path t) t :=
    (Γ.smooth.differentiable (by norm_num) t).hasDerivAt
  have h := (h₁.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t h₂
  simpa [homotopyResolvent, resolvent, neg_smul, Function.comp_def] using! h

theorem continuousOn_homotopyResolvent_path [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (fun p : ℝ × ℝ => homotopyResolvent A a p.1 (Γ.path p.2))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
  (continuousOn_homotopyResolvent A ha).comp
    ((continuous_fst.prodMk (Γ.smooth.continuous.comp continuous_snd)).continuousOn)
    (fun p hp => ⟨hp.1, (Γ.avoids p.2 hp.2).2⟩)

theorem continuousOn_homotopyKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (Function.uncurry (homotopyKernel A a Γ.toSmoothContour))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hr := continuousOn_homotopyResolvent_path A Γ ha
  exact (Γ.smooth.continuous_deriv_one.comp continuous_snd).continuousOn.smul
    ((hr.mul continuousOn_const).mul hr)

theorem intervalIntegrable_homotopyKernel_left [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => homotopyKernel A a Γ.toSmoothContour s t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hc := (continuousOn_homotopyKernel A Γ ha).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, ht⟩)
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one, Function.comp_def, Function.uncurry_def] using! hc

theorem intervalIntegrable_homotopyKernel_right [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (homotopyKernel A a Γ.toSmoothContour s)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hc := (continuousOn_homotopyKernel A Γ ha).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one, Function.comp_def, Function.uncurry_def] using! hc

theorem integral_homotopyKernel_left [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) =
      deriv Γ.path t • homotopyResolvent A a 1 (Γ.path t) -
        deriv Γ.path t • homotopyResolvent A a 0 (Γ.path t) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => deriv Γ.path t • homotopyResolvent A a r (Γ.path t)) _
    (intervalIntegrable_homotopyKernel_left A Γ ha ht)
  intro s hs
  exact (hasDerivAt_homotopyResolvent A ha (by simpa using hs) (Γ.avoids t ht).2).const_smul
    (deriv Γ.path t)

theorem hasDerivAt_homotopyKernel_primitive [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => -((A - algebraMap ℂ (Operator H) a) *
        homotopyResolvent A a s (Γ.path r)))
      (homotopyKernel A a Γ.toSmoothContour s t) t := by
  have h := (hasDerivAt_homotopyResolvent_path A Γ ha hs ht).const_mul
    (A - algebraMap ℂ (Operator H) a) |>.neg
  have hc := (commute_homotopyResolvent A a s (Γ.path t)).eq
  simpa only [homotopyKernel, mul_smul_comm, neg_smul, mul_neg, neg_neg,
    sq, ← mul_assoc, hc] using! h

theorem integral_homotopyKernel_right [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) = 0 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_homotopyKernel_primitive A Γ ha hs (by simpa using ht))
    (intervalIntegrable_homotopyKernel_right A Γ ha hs)
  simpa only [Γ.closed, sub_self] using he

theorem integral_integral_homotopyKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) = 0 := by
  have hc := continuousOn_homotopyKernel A Γ ha
  have hi := (hc.integrableOn_compact (μ := MeasureTheory.volume) (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hFub := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := homotopyKernel A a Γ.toSmoothContour)
    (a := (0 : ℝ)) (b := 1) (c := 0) (d := 1) (by simpa using! hi)
  rw [← hFub]
  calc
    _ = ∫ _s in (0 : ℝ)..1, (0 : Operator H) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact integral_homotopyKernel_right A Γ ha (by simpa using hs)
    _ = 0 := by simp

theorem integral_resolvent_homotopy [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t • Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)) =
      ∫ t in (0 : ℝ)..1, deriv Γ.path t •
        Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - algebraMap ℂ (Operator H) a) := by
  have hint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun t => deriv Γ.path t • homotopyResolvent A a s (Γ.path t))
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hc := (continuousOn_homotopyResolvent_path A Γ ha).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using!
      Γ.smooth.continuous_deriv_one.continuousOn.smul hc
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t • homotopyResolvent A a 1 (Γ.path t)) =
      ∫ t in (0 : ℝ)..1, deriv Γ.path t • homotopyResolvent A a 0 (Γ.path t) := by
    apply sub_eq_zero.mp
    rw [← intervalIntegral.integral_sub (hint 1 ⟨zero_le_one, le_rfl⟩) (hint 0 ⟨le_rfl, zero_le_one⟩)]
    convert integral_integral_homotopyKernel A Γ ha using 1
    apply intervalIntegral.integral_congr
    intro t ht
    exact (integral_homotopyKernel_left A Γ ha (by simpa using ht)).symm
  simpa only [homotopyResolvent, operatorHomotopy_one, operatorHomotopy_zero] using he

theorem ring_inverse_algebraMap (z : ℂ) :
    Ring.inverse (algebraMap ℂ (Operator H) z) = z⁻¹ • (1 : Operator H) := by
  by_cases hz : z = 0
  · simp [hz]
  have hu : IsUnit (algebraMap ℂ (Operator H) z) :=
    (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ (Operator H))
  have he := (Ring.inverse_mul_eq_iff_eq_mul (algebraMap ℂ (Operator H) z)
    1 (z⁻¹ • (1 : Operator H)) hu).mpr (by
      rw [← Algebra.algebraMap_eq_smul_one, ← map_mul, mul_inv_cancel₀ hz, map_one])
  simpa only [mul_one] using he

theorem contourEval_one [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    contourEval A Γ.toSmoothContour (fun _ => 1) = 1 := by
  nontriviality H
  obtain ⟨a, ha⟩ := numericalClosure_nonempty A
  unfold contourEval
  simp only [mul_one]
  rw [integral_resolvent_homotopy A Γ ha]
  simp only [← map_sub, ring_inverse_algebraMap, smul_smul,
    intervalIntegral.integral_smul_const, smul_smul]
  change Γ.toSmoothContour.index a • (1 : Operator H) = 1
  rw [Γ.index_inside a ha, one_smul]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.MatrixContours
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix Contours. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance matrixContourOperatorRealNormedSpace_r19fca1_1 (m : ℕ) :
    NormedSpace ℝ (Operator (Amplification H m)) :=
  NormedSpace.restrictScalars ℝ ℂ _
theorem sum_tensorOperator_entries (A : Operator H) {m : ℕ} (B : Coeff m) :
    (∑ i, ∑ j, tensorOperator (B i j • A) (Matrix.single i j 1)) = tensorOperator A B := by
  have hsum : (∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ)) = B := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using (Matrix.matrix_eq_sum_single B).symm
  calc
    _ = ∑ i, ∑ j, B i j • tensorCoefficientCLM A m (Matrix.single i j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact map_smul (tensorOperatorCLM (Matrix.single i j 1)) (B i j) A
    _ = tensorCoefficientCLM A m (∑ i, ∑ j, B i j • Matrix.single i j 1) := by
      simp only [map_sum, map_smul]
    _ = tensorOperator A B := by rw [hsum]; rfl

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Polynomials. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SmoothContour.integral_deriv_mul_pow (Γ : SmoothContour) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * (Γ.path t) ^ n) = 0 := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hder (t : ℝ) : HasDerivAt (fun r : ℝ => (n + 1 : ℂ)⁻¹ * Γ.path r ^ (n + 1))
      (deriv Γ.path t * Γ.path t ^ n) t := by
    have h := ((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.pow (n + 1)).const_mul
      (n + 1 : ℂ)⁻¹
    convert! h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_comm]
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * Γ.path t ^ n)
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Γ.smooth.continuous_deriv_one.mul (Γ.smooth.continuous.pow n)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hi
  simpa only [Γ.closed, sub_self] using he

theorem smul_resolvent_eq [CompleteSpace H] (A : Operator H) {z : ℂ}
    (hz : z ∉ numericalClosure A) :
    z • Ring.inverse (algebraMap ℂ (Operator H) z - A) =
      1 + A * Ring.inverse (algebraMap ℂ (Operator H) z - A) := by
  have hu : IsUnit (algebraMap ℂ (Operator H) z - A) := by
    change z ∈ resolventSet ℂ A
    by_contra he
    exact hz (spectrum_subset_numericalClosure A he)
  have he := Ring.mul_inverse_cancel _ hu
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at he
  exact sub_eq_iff_eq_add.mp he

theorem contourEval_mul_id_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0) :
    contourEval A Γ.toSmoothContour (fun z => z * f z) =
      A * contourEval A Γ.toSmoothContour f := by
  let p := fun t : ℝ => f (Γ.path t) • contourKernel A Γ.toSmoothContour t
  let q := fun t : ℝ => deriv Γ.path t * f (Γ.path t)
  let L := ContinuousLinearMap.mul ℂ (Operator H) A
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hp : ContinuousOn p (Icc (0 : ℝ) 1) := hfc.smul (continuousOn_contourKernel A Γ)
  have hq : ContinuousOn q (Icc (0 : ℝ) 1) := Γ.smooth.continuous_deriv_one.continuousOn.mul hfc
  have hip : IntervalIntegrable p MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_contourIntegrand A Γ hf
  have hiL : IntervalIntegrable (fun t => L (p t)) MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one, Function.comp_def] using!
      L.continuous.comp_continuousOn hp
  have hiq : IntervalIntegrable (fun t => q t • (1 : Operator H))
      MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using! hq.smul continuousOn_const
  have halg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t =
        q t • (1 : Operator H) + L (p t) := by
    have he := smul_resolvent_eq A (Γ.avoids t ht).2
    have hscalar : Γ.path t * f (Γ.path t) * deriv Γ.path t =
        (deriv Γ.path t * f (Γ.path t)) * Γ.path t := by ring
    dsimp only [contourKernel, p, q, L]
    rw [smul_smul, hscalar, ← smul_smul, he, smul_add]
    congr 1
    simp only [ContinuousLinearMap.mul_apply', mul_smul_comm, smul_smul]
    rw [mul_comm (f (Γ.path t))]
  rw [contourEval_eq_kernel, contourEval_eq_kernel]
  have hi : (∫ t in (0 : ℝ)..1, (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t) =
      L (∫ t in (0 : ℝ)..1, p t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, q t • (1 : Operator H) + L (p t) :=
        intervalIntegral.integral_congr (fun t ht => halg t (by simpa using ht))
      _ = (∫ t in (0 : ℝ)..1, q t) • (1 : Operator H) + L (∫ t in (0 : ℝ)..1, p t) := by
        rw [intervalIntegral.integral_add hiq hiL, intervalIntegral.integral_smul_const,
          L.intervalIntegral_comp_comm hip]
      _ = _ := by rw [show (∫ t in (0 : ℝ)..1, q t) = 0 from hzero, zero_smul, zero_add]
  rw [hi]
  exact (map_smul L _ _).symm

theorem contourEval_pow [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (n : ℕ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n) = A ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using contourEval_one A Γ
  | succ n ih =>
    have he := contourEval_mul_id_of_integral_eq_zero A Γ
      (continuous_pow n).continuousOn (Γ.toSmoothContour.integral_deriv_mul_pow n)
    simpa only [pow_succ', ih] using he

theorem contourEval_const_mul (A : Operator H) (Γ : SmoothContour) (c : ℂ) (f : ℂ → ℂ) :
    contourEval A Γ (fun z => c * f z) = c • contourEval A Γ f := by
  simp only [contourEval_eq_kernel, mul_smul, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem contourEval_sum [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) Γ.toSmoothContour.trace) :
    contourEval A Γ.toSmoothContour (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, contourEval A Γ.toSmoothContour (f i) := by
  simp only [contourEval_eq_kernel, Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum (fun i hi => intervalIntegrable_contourIntegrand A Γ (hf i hi)),
    Finset.smul_sum]

theorem contourEval_pow_mul_const [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (n : ℕ) (c : ℂ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n * c) = c • A ^ n := by
  simp_rw [mul_comm _ c]
  rw [contourEval_const_mul, contourEval_pow]

theorem contourEval_matrixPolynomial_entry [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) (i j : Fin m) :
    contourEval A Γ.toSmoothContour (fun z => matrixPolynomial B z i j) =
      ∑ k : Fin (d + 1), B k i j • A ^ (k : ℕ) := by
  have hc (k : Fin (d + 1)) : ContinuousOn (fun z : ℂ => z ^ (k : ℕ) * B k i j)
      Γ.toSmoothContour.trace := ((continuous_pow _).mul continuous_const).continuousOn
  simpa only [matrixPolynomial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    contourEval_pow_mul_const] using
    contourEval_sum A Γ Finset.univ (fun k : Fin (d + 1) => fun z => z ^ (k : ℕ) * B k i j)
      (fun k _ => hc k)

theorem matrixContourEval_matrixPolynomial [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    matrixContourEval A Γ.toSmoothContour (matrixPolynomial B) = polynomialEval A B := by
  classical
  unfold matrixContourEval polynomialEval
  simp only [contourEval_matrixPolynomial_entry, ← tensorOperatorCLM_apply, map_sum]
  calc
    _ = ∑ i, ∑ k, ∑ j, tensorOperator (B k i j • A ^ (k : ℕ)) (Matrix.single i j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, tensorOperator (B k i j • A ^ (k : ℕ)) (Matrix.single i j 1) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact sum_tensorOperator_entries (A ^ (k : ℕ)) (B k)

theorem contour_bound_of_uniform_polynomials [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ}
    (F : ℂ → Coeff m) (hF : ContinuousOn F (numericalClosure A))
    (hpoly : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B))
    (degrees : ℕ → ℕ) (B : (n : ℕ) → Fin (degrees n + 1) → Coeff m)
    (happrox : TendstoUniformlyOn (fun n => matrixPolynomial (B n)) F atTop
      (numericalClosure A ∪ Γ.toSmoothContour.trace)) :
    ‖matrixContourEval A Γ.toSmoothContour F‖ ≤ 2 * supNorm (numericalClosure A) F :=
  contour_bound_of_polynomial_approximation A Γ F hF hpoly
    (fun _ B => matrixContourEval_matrixPolynomial A Γ B) degrees B happrox

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalContours
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Contours. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rational_poleFree_neighborhood {m : ℕ} {K : Set ℂ}
    (R : RationalMatrix m) (hR : PolesOutside K R) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ PolesOutside U R ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) := by
  let U : Set ℂ := ⋂ i, ⋂ j, {z : ℂ | (R i j).denom.eval z ≠ 0}
  have hne : PolesOutside U R := by
    intro i j z hz
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hz i) j
  refine ⟨U, ?_, ?_, hne, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne.preimage (R i j).denom.continuous
  · intro z hz
    exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun j => hR i j z hz))
  · intro i j
    simp only [matrixRationalFunction, RatFunc.eval, Polynomial.eval₂_id]
    exact DifferentiableOn.div (𝕜 := ℂ) (𝕜' := ℂ)
      (R i j).num.differentiableOn (R i j).denom.differentiableOn (hne i j)

theorem rational_conclusion_of_holomorphic_bound [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {m : ℕ}
    (hhol : ∀ (U : Set ℂ) (F : ℂ → Coeff m), IsOpen U →
      numericalClosure A ⊆ U → EntrywiseHolomorphic U F →
      Nonempty (CalculusContour (numericalClosure A) U) ∧
      ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalClosure A) F)
    (R : RationalMatrix m) (hR : PolesOutside (numericalClosure A) R) :
    (∀ i j, IsUnit (Polynomial.aeval A (R i j).denom)) ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalClosure A) (matrixRationalFunction R) ∧
    (∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixRationalFunction R) =
        ‖matrixRationalFunction R z‖) ∧
    ∃ U : Set ℂ, IsOpen U ∧ numericalClosure A ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      matrixRationalEval A R = matrixHolomorphicEval A U (matrixRationalFunction R) := by
  obtain ⟨U, hU, hKU, hpoles, hF⟩ := rational_poleFree_neighborhood R hR
  obtain ⟨⟨Γ⟩, hb⟩ := hhol U (matrixRationalFunction R) hU hKU hF
  have he := matrixHolomorphicEval_matrixRationalFunction A Γ R hpoles
  refine ⟨rational_denominators_isUnit A R hR, ?_,
    rational_sup_attained A R hR, U, hU, hKU, hF, he.symm⟩
  rwa [he] at hb

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ConvexNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Neighborhood. -/

noncomputable section

open Set Metric

open scoped Convex InnerProductSpace

namespace CrouzeixHilbert

theorem convex_outward_not_mem {K : Set ℂ} (hK : Convex ℝ K)
    {a x : ℂ} (ha : a ∈ K) (hx : x ∉ K) {t : ℝ} (ht : 1 ≤ t) :
    a + t • (x - a) ∉ K := by
  intro hy
  have htp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hz := hK.add_smul_sub_mem ha hy
    (show t⁻¹ ∈ Icc (0 : ℝ) 1 from
      ⟨inv_nonneg.mpr htp.le, inv_le_one_of_one_le₀ ht⟩)
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htp.ne',
    one_smul, add_sub_cancel] at hz
  exact hx hz

theorem segment_outward_subset_compl {K : Set ℂ} (hK : Convex ℝ K)
    {a x : ℂ} (ha : a ∈ K) (hx : x ∉ K) {r : ℝ} (hr : 1 ≤ r) :
    [x -[ℝ] (a + r • (x - a))] ⊆ Kᶜ := by
  rw [segment_eq_image']
  rintro z ⟨t, ht, rfl⟩
  have he : x + t • (a + r • (x - a) - x) =
      a + (1 + t * (r - 1)) • (x - a) := by module
  dsimp only
  rw [he]
  exact convex_outward_not_mem hK ha hx (by nlinarith [ht.1])

theorem isPathConnected_compl_of_bounded_convex {K : Set ℂ}
    (hK : Bornology.IsBounded K) (hc : Convex ℝ K) : IsPathConnected Kᶜ := by
  rcases K.eq_empty_or_nonempty with h0 | ⟨a, ha⟩
  · rw [h0, compl_empty]
    exact convex_univ.isPathConnected ⟨0, mem_univ _⟩
  have hrank : 1 < Module.rank ℝ ℂ := by simp
  have hn : Kᶜ.Nonempty := by
    obtain ⟨R, hR, hb⟩ := hK.subset_ball_lt 0 a
    obtain ⟨z, hz⟩ := (isPathConnected_sphere hrank a hR.le).nonempty
    refine ⟨z, ?_⟩
    intro hzK
    have := mem_ball.mp (hb hzK)
    rw [mem_sphere.mp hz] at this
    exact lt_irrefl _ this
  apply isPathConnected_iff.mpr
  refine ⟨hn, ?_⟩
  intro x hx y hy
  obtain ⟨R, hR, hb⟩ := hK.subset_ball_lt (max (dist x a) (dist y a)) a
  have hRx : dist x a < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRy : dist y a < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRp : 0 < R := lt_of_le_of_lt dist_nonneg hRx
  have hsphere : sphere a R ⊆ Kᶜ := by
    intro z hz hzK
    have hlt := mem_ball.mp (hb hzK)
    rw [mem_sphere.mp hz] at hlt
    exact lt_irrefl _ hlt
  have hradial (v : ℂ) (hv : v ∈ Kᶜ) (hRv : dist v a < R) :
      ∃ q ∈ sphere a R, JoinedIn Kᶜ v q := by
    have hvne : v - a ≠ 0 := by
      intro he
      exact hv (sub_eq_zero.mp he ▸ ha)
    have hnv : 0 < ‖v - a‖ := norm_pos_iff.mpr hvne
    have hr : 1 ≤ R / ‖v - a‖ := by
      apply (le_div_iff₀ hnv).mpr
      simpa only [one_mul, dist_eq_norm] using hRv.le
    refine ⟨a + (R / ‖v - a‖) • (v - a), ?_, ?_⟩
    · rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hRp.le hnv.le), div_mul_cancel₀ _ hnv.ne']
    · exact JoinedIn.of_segment_subset (segment_outward_subset_compl hc ha hv hr)
  obtain ⟨qx, hqx, jx⟩ := hradial x hx hRx
  obtain ⟨qy, hqy, jy⟩ := hradial y hy hRy
  exact jx.trans (((isPathConnected_sphere hrank a hRp.le).joinedIn qx hqx qy hqy).mono
    hsphere |>.trans jy.symm)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_compact_convex_neighborhood (A : Operator H) {U : Set ℂ}
    (hU : IsOpen U) (hKU : numericalClosure A ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧
      IsCompact (cthickening ε (numericalClosure A)) ∧
      Convex ℝ (cthickening ε (numericalClosure A)) ∧
      numericalClosure A ⊆ interior (cthickening ε (numericalClosure A)) ∧
      cthickening ε (numericalClosure A) ⊆ U ∧
      IsConnected (cthickening ε (numericalClosure A))ᶜ := by
  obtain ⟨ε, hε, hεU⟩ := (isCompact_numericalClosure A).exists_cthickening_subset_open hU hKU
  have hcmp : IsCompact (cthickening ε (numericalClosure A)) :=
    (isCompact_numericalClosure A).cthickening
  have hc : Convex ℝ (cthickening ε (numericalClosure A)) :=
    (convex_numericalRange A).closure.cthickening ε
  exact ⟨ε, hε, hcmp, hc,
    (self_subset_thickening hε _).trans (thickening_subset_interior_cthickening _ _), hεU,
    (isPathConnected_compl_of_bounded_convex hcmp.isBounded hc).isConnected⟩

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PolynomialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Approximation. -/

noncomputable section

open scoped Topology

open Set Filter Metric MeasureTheory

namespace CrouzeixHilbert

open scoped Matrix.Norms.L2Operator

theorem matrix_norm_le_entry_bound {m : ℕ} (B : Coeff m) {δ : ℝ}
    (hB : ∀ i j, ‖B i j‖ ≤ δ) :
    ‖B‖ ≤ δ * (∑ i : Fin m, ∑ j : Fin m, ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖) := by
  have he : B = ∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single B
  calc
    ‖B‖ = ‖∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ)‖ := congrArg norm he
    _ ≤ ∑ i, ∑ j, ‖B i j • (Matrix.single i j (1 : ℂ) : Coeff m)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, δ * ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg _)
    _ = δ * (∑ i, ∑ j, ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖) := by
      simp only [Finset.mul_sum]

theorem exists_matrixPolynomial_entries {m : ℕ}
    (p : Fin m → Fin m → Polynomial ℂ) :
    ∃ d : ℕ, ∃ B : Fin (d + 1) → Coeff m,
      ∀ z i j, matrixPolynomial B z i j = (p i j).eval z := by
  classical
  let d := Finset.univ.sup (fun i : Fin m => Finset.univ.sup (fun j : Fin m => (p i j).natDegree))
  refine ⟨d, fun k i j => (p i j).coeff k, ?_⟩
  intro z i j
  have hd : (p i j).natDegree < d + 1 := Nat.lt_succ_of_le (le_trans
    (Finset.le_sup (f := fun j : Fin m => (p i j).natDegree) (Finset.mem_univ j))
    (Finset.le_sup (f := fun i : Fin m => Finset.univ.sup (fun j : Fin m => (p i j).natDegree))
      (Finset.mem_univ i)))
  rw [Polynomial.eval_eq_sum_range' hd]
  simp only [matrixPolynomial, Matrix.sum_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem exists_matrixPolynomial_uniform_approx {m : ℕ} {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic U F) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, ∃ B : Fin (d + 1) → Coeff m, ∀ z ∈ K, ‖matrixPolynomial B z - F z‖ < ε := by
  classical
  let C : ℝ := ∑ i : Fin m, ∑ j : Fin m, ‖(Matrix.single i j (1 : ℂ) : Coeff m)‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have he : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hp := fun i j => exists_polynomial_uniform_approx hK hc hU hKU (hF i j) he
  choose p hp using hp
  obtain ⟨d, B, hB⟩ := exists_matrixPolynomial_entries p
  refine ⟨d, B, fun z hz => ?_⟩
  calc
    ‖matrixPolynomial B z - F z‖ ≤ (ε / (C + 1)) * C :=
      matrix_norm_le_entry_bound _ (fun i j => by
        simpa only [Matrix.sub_apply, hB] using (hp i j z hz).le)
    _ < (ε / (C + 1)) * (C + 1) := mul_lt_mul_of_pos_left (by linarith) he
    _ = ε := div_mul_cancel₀ _ (by linarith)

theorem exists_matrixPolynomial_tendstoUniformlyOn {m : ℕ} {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic U F) :
    ∃ degrees : ℕ → ℕ, ∃ B : (n : ℕ) → Fin (degrees n + 1) → Coeff m,
      TendstoUniformlyOn (fun n => matrixPolynomial (B n)) F atTop K := by
  have he (n : ℕ) : (0 : ℝ) < 1 / (n + 1) := by positivity
  choose degrees B hB using fun n => exists_matrixPolynomial_uniform_approx hK hc hU hKU hF (he n)
  refine ⟨degrees, B, Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)⟩
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_comm, dist_eq_norm]
  exact (hB n z hz).trans hn

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_contour_bound_of_polynomial_bound [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {m : ℕ} {U : Set ℂ} (F : ℂ → Coeff m)
    (hU : IsOpen U) (hKU : numericalClosure A ⊆ U) (hF : EntrywiseHolomorphic U F)
    (hpoly : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B)) :
    ∃ Γ : CalculusContour (numericalClosure A) U,
      ‖matrixContourEval A Γ.toSmoothContour F‖ ≤ 2 * supNorm (numericalClosure A) F := by
  obtain ⟨ε, _hε, hL, hLc, hKL, hLU, _hcomp⟩ := exists_compact_convex_neighborhood A hU hKU
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) isOpen_interior hKL
  let Δ : CalculusContour (numericalClosure A) U :=
    { toSmoothContour := Γ.toSmoothContour
      avoids := fun t ht => ⟨hLU (interior_subset (Γ.avoids t ht).1), (Γ.avoids t ht).2⟩
      index_inside := Γ.index_inside
      index_outside := fun z hz => Γ.index_outside z (fun he => hz (hLU (interior_subset he))) }
  obtain ⟨degrees, B, happ⟩ := exists_matrixPolynomial_tendstoUniformlyOn hL hLc hU hLU hF
  refine ⟨Δ, contour_bound_of_uniform_polynomials A Δ F (hF.continuousOn.mono hKU)
    hpoly degrees B (happ.mono ?_)⟩
  rintro z (hz | ⟨t, ht, rfl⟩)
  · exact interior_subset (hKL hz)
  · exact interior_subset (Γ.avoids t ht).1

theorem holomorphicEval_eq_contourEval_of_independent (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (f : ℂ → ℂ)
    (hind : ∀ Δ : CalculusContour (numericalClosure A) U,
      contourEval A Δ.toSmoothContour f = contourEval A Γ.toSmoothContour f) :
    holomorphicEval A U f = contourEval A Γ.toSmoothContour f := by
  classical
  rw [holomorphicEval, dite_eq_left (show Nonempty (CalculusContour (numericalClosure A) U) from ⟨Γ⟩)]
  exact hind _

theorem nonzeroConclusion_of_finite_bound_and_contour_independence
    [CompleteSpace H] [Nontrivial H] (A : Operator H)
    (hfin : FiniteMatrixPolynomialBound)
    (hind : ∀ (U : Set ℂ), IsOpen U → numericalClosure A ⊆ U →
      ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f U →
      ∀ Γ Δ : CalculusContour (numericalClosure A) U,
        contourEval A Γ.toSmoothContour f = contourEval A Δ.toSmoothContour f) :
    NonzeroConclusion A := by
  have hhol (m : ℕ) (hm : 0 < m) (U : Set ℂ) (F : ℂ → Coeff m)
      (hU : IsOpen U) (hKU : numericalClosure A ⊆ U) (hF : EntrywiseHolomorphic U F) :
      Nonempty (CalculusContour (numericalClosure A) U) ∧
      (∀ Γ : CalculusContour (numericalClosure A) U, ∀ i j,
        holomorphicEval A U (fun z => F z i j) =
          contourEval A Γ.toSmoothContour (fun z => F z i j)) ∧
      ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalClosure A) F ∧
      ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) F = ‖F z‖ := by
    obtain ⟨Γ, hb⟩ := exists_contour_bound_of_polynomial_bound A F hU hKU hF
      (fun _ B => polynomial_bound_of_finite_matrix_bound hfin A hm B)
    have hsame (Δ : CalculusContour (numericalClosure A) U) (i j : Fin m) :
        holomorphicEval A U (fun z => F z i j) =
          contourEval A Δ.toSmoothContour (fun z => F z i j) :=
      holomorphicEval_eq_contourEval_of_independent A Δ _
        (fun Γ => hind U hU hKU _ (hF i j) Γ Δ)
    refine ⟨⟨Γ⟩, hsame, ?_, holomorphic_sup_attained A hKU hF⟩
    have he : matrixHolomorphicEval A U F = matrixContourEval A Γ.toSmoothContour F := by
      simp only [matrixHolomorphicEval, matrixContourEval, hsame Γ]
    rwa [he]
  refine ⟨isCompact_numericalClosure A, convex_numericalClosure A,
    spectrum_subset_numericalClosure A, ?_, hhol, ?_⟩
  · intro m hm d B
    exact ⟨polynomial_bound_of_finite_matrix_bound hfin A hm B, polynomial_sup_eq_max A B⟩
  · intro m hm R hR
    exact rational_conclusion_of_holomorphic_bound A
      (fun U F hU hKU hF => ⟨(hhol m hm U F hU hKU hF).1, (hhol m hm U F hU hKU hF).2.2.1⟩)
      R hR

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A two-dimensional operator with sharp constant two. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_sharpOperator : ‖sharpOperator‖ = 2 := by
  norm_num [sharpOperator, norm_smul, InnerProductSpace.norm_rankOne,
    PiLp.norm_single]

theorem sharpOperator_apply (x : EuclideanSpace ℂ (Fin 2)) :
    sharpOperator x = (2 * x 1) • EuclideanSpace.single 0 1 := by
  simp [sharpOperator, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left,
    smul_smul]

theorem sharpOperator_inner_norm (x : EuclideanSpace ℂ (Fin 2)) :
    ‖⟪x, sharpOperator x⟫_ℂ‖ = 2 * ‖x 0‖ * ‖x 1‖ := by
  rw [sharpOperator_apply, inner_smul_right, EuclideanSpace.inner_single_right]
  simp only [one_mul, norm_mul, Complex.norm_conj]
  norm_num
  ring

theorem sharpOperator_numerical_le {z : ℂ} (hz : z ∈ numericalRange sharpOperator) :
    ‖z‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  have hs := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_two, hx, one_pow] at hs
  rw [sharpOperator_inner_norm]
  nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖)]

theorem sharpOperator_numerical_attains :
    ∃ z ∈ numericalRange sharpOperator, ‖z‖ = 1 := by
  let v : EuclideanSpace ℂ (Fin 2) :=
    EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
  have hv0 : v 0 = 1 := by simp [v]
  have hv1 : v 1 = 1 := by simp [v]
  have hv : ‖v‖ ≠ 0 := by
    intro h
    have hh := congrArg (fun w : EuclideanSpace ℂ (Fin 2) => w 0) (norm_eq_zero.mp h)
    simp [hv0] at hh
  let x : EuclideanSpace ℂ (Fin 2) := (‖v‖ : ℂ)⁻¹ • v
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, hv]
  have heq : x 0 = x 1 := by simp [x, hv0, hv1]
  refine ⟨⟪x, sharpOperator x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
  rw [sharpOperator_inner_norm, heq]
  have hs := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_two, hx, one_pow, heq] at hs
  nlinarith

theorem sharpConstant : SharpConstant := by
  refine ⟨sharpOperator, sharpCoefficients, ?_, ?_⟩
  · apply le_antisymm
    · apply supNorm_le (by norm_num)
      intro z hz
      simpa [norm_smul] using sharpOperator_numerical_le hz
    · obtain ⟨z, hz, hzn⟩ := sharpOperator_numerical_attains
      have hbK := supNorm_bddAbove (isCompact_numericalClosure sharpOperator)
        (continuous_matrixPolynomial (d := 1) sharpCoefficients).continuousOn
      have hbW : BddAbove (insert 0 ((fun z => ‖matrixPolynomial (d := 1) sharpCoefficients z‖) ''
          numericalRange sharpOperator)) :=
        hbK.mono (Set.insert_subset_insert (Set.image_mono subset_closure))
      simpa [norm_smul, hzn] using norm_le_supNorm hbW hz
  · rw [sharp_polynomialEval]
    apply le_antisymm
    · simpa [norm_sharpOperator] using norm_tensorOperator_le sharpOperator (1 : Coeff 1)
    · let e : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1
      let f : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1
      let w : Amplification (EuclideanSpace ℂ (Fin 2)) 1 := ↑(e ⊗ₜ[ℂ] f)
      have hw : ‖w‖ ≤ 1 := by simp [w, e, f]
      have hl := (tensorOperator sharpOperator (1 : Coeff 1)).unit_le_opNorm w hw
      have he : ‖sharpOperator e‖ = 2 := by
        simp [sharpOperator_apply, e, norm_smul]
      simpa [w, f, tensorOperator, ContinuousLinearMap.completion_apply_coe, he] using hl

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HilbertExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert Extension. -/

noncomputable section

open Set Filter Metric

open scoped Topology

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem differentiableOn_resolvent [CompleteSpace H] (A : Operator H) :
    DifferentiableOn ℂ (fun z : ℂ => Ring.inverse (algebraMap ℂ (Operator H) z - A))
      (numericalClosure A)ᶜ := by
  intro z hz
  have hr : z ∈ resolventSet ℂ A := by
    by_contra h
    exact hz (spectrum_subset_numericalClosure A h)
  exact (spectrum.hasDerivAt_resolvent_const_left hr).differentiableAt.differentiableWithinAt

theorem contourEval_eq_integral (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) :
    contourEval A Γ f =
      Γ.integral (fun z => f z • Ring.inverse (algebraMap ℂ (Operator H) z - A)) := by
  simp only [contourEval, SmoothContour.integral, smul_smul]

theorem contourEval_independent [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ Δ : CalculusContour (numericalClosure A) U) :
    contourEval A Γ.toSmoothContour f = contourEval A Δ.toSmoothContour f := by
  let V := U \ numericalClosure A
  have hV : IsOpen V := hU.sdiff isClosed_closure
  let paths : Bool → SmoothContour := fun b => if b then Γ.toSmoothContour else Δ.toSmoothContour
  let c : Bool → ℂ := fun b => if b then 1 else -1
  have hp : ∀ b, (paths b).trace ⊆ V := by
    intro b z hz
    cases b <;> rcases hz with ⟨t, ht, rfl⟩
    · exact Δ.avoids t ht
    · exact Γ.avoids t ht
  have hi : ∀ z ∉ V, ∑ b, c b * (paths b).index z = 0 := by
    intro z hz
    simp only [Fintype.sum_bool, paths, c, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, ← sub_eq_add_neg]
    by_cases hK : z ∈ numericalClosure A
    · rw [Γ.index_inside z hK, Δ.index_inside z hK, sub_self]
    · have hzU : z ∉ U := fun hzU => hz ⟨hzU, hK⟩
      rw [Γ.index_outside z hzU, Δ.index_outside z hzU, sub_self]
  have hd : DifferentiableOn ℂ (fun z => f z •
      Ring.inverse (algebraMap ℂ (Operator H) z - A)) V :=
    (hf.mono (fun _ hz => hz.1)).fun_smul
      ((differentiableOn_resolvent A).mono (fun _ hz => hz.2))
  have h := null_homology_integral paths c hV hp hi hd
  simp only [Fintype.sum_bool, paths, c, Bool.false_eq_true, ite_false, ite_true,
    one_smul, neg_smul, ← sub_eq_add_neg] at h
  rw [contourEval_eq_integral, contourEval_eq_integral]
  exact sub_eq_zero.mp h

theorem holomorphicEval_eq_contourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ : CalculusContour (numericalClosure A) U) :
    holomorphicEval A U f = contourEval A Γ.toSmoothContour f :=
  holomorphicEval_eq_contourEval_of_independent A Γ f (fun Δ => contourEval_independent A hU hf Δ Γ)

theorem nonzeroConclusion_of_finite_matrix_bound [CompleteSpace H] [Nontrivial H]
    (hfin : FiniteMatrixPolynomialBound) (A : Operator H) : NonzeroConclusion A :=
  nonzeroConclusion_of_finite_bound_and_contour_independence A hfin
    (fun _U hU _hK _f hf Γ Δ => contourEval_independent A hU hf Γ Δ)

theorem hilbert_of_finite_matrix_bound (hfin : FiniteMatrixPolynomialBound)
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator H) :
    (Nontrivial H → NonzeroConclusion A) ∧
    (Subsingleton H → ZeroConclusion A) ∧ SharpConstant := by
  refine ⟨fun h => ?_, fun h => ?_, sharpConstant⟩
  · have := h
    exact nonzeroConclusion_of_finite_matrix_bound hfin A
  · have := h
    exact zeroConclusion A

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ConformalCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conformal Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem isOpen_image_of_univalent {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℂ}
    (hga : AnalyticOnNhd ℂ g V) (hgi : InjOn g V) : IsOpen (g '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, rfl⟩
  rw [← (hga z hz).hasStrictDerivAt.map_nhds_eq
    (deriv_ne_zero_of_injOn hV hga.differentiableOn hgi hz)]
  exact image_mem_map (hV.mem_nhds hz)

theorem image_closure_eq_closedDisk {U V : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hUV : closure U ⊆ V) {g : ℂ → ℂ}
    (hga : AnalyticOnNhd ℂ g V) (hbij : BijOn g U (ball 0 1))
    (hfront : ∀ p ∈ frontier U, ‖g p‖ = 1) : g '' closure U = closedBall 0 1 := by
  apply Subset.antisymm
  · rintro w ⟨z, hz, rfl⟩
    rw [mem_closedBall_zero_iff]
    by_cases hzu : z ∈ U
    · exact (mem_ball_zero_iff.mp (hbij.mapsTo hzu)).le
    · exact (hfront z ⟨hz, by simpa only [hU.interior_eq] using hzu⟩).le
  · rw [← closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    apply closure_minimal _ ((hb.isCompact_closure.image_of_continuousOn
      (hga.continuousOn.mono hUV)).isClosed)
    exact hbij.surjOn.trans (image_mono subset_closure)

theorem exists_conformal_collar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (ρ : ℝ) (f h : ℂ → ℂ),
      IsOpen V ∧ closure U ⊆ V ∧ 1 < ρ ∧
      AnalyticOnNhd ℂ f V ∧ AnalyticOnNhd ℂ h (ball 0 ρ) ∧
      InjOn f V ∧ InjOn h (ball 0 ρ) ∧
      BijOn f U (ball 0 1) ∧ BijOn h (ball 0 1) U ∧
      BijOn f (closure U) (closedBall 0 1) ∧
      BijOn h (closedBall 0 1) (closure U) ∧
      InvOn h f U (ball 0 1) ∧ f a = 0 ∧ h 0 = a ∧
      (∀ z ∈ frontier U, ‖f z‖ = 1) ∧
      InvOn h f V (f '' V) ∧ ball 0 ρ ⊆ f '' V := by
  obtain ⟨f₀, hf₀, _, hfb₀⟩ := riemann_mapping_bounded hU hb hc ha
  obtain ⟨V, f, hV, hUV, hfa, hfe, hfi, hfront⟩ :=
    exists_univalent_extension hU hb hf₀.holomorphic hfb₀ hchart
  have hfb : BijOn f U (ball 0 1) := hfb₀.congr hfe.symm
  have hBij : BijOn f V (f '' V) := ⟨mapsTo_image _ _, hfi, surjOn_image _ _⟩
  let h := invFunOn f V
  have hinv : InvOn h f V (f '' V) := hBij.invOn_invFunOn
  have hWi := isOpen_image_of_univalent hV hfa hfi
  have hha : AnalyticOnNhd ℂ h (f '' V) := by
    apply DifferentiableOn.analyticOnNhd _ hWi
    intro w hw
    exact (hasStrictDerivAt_invFunOn hV hfa.differentiableOn hBij hw).hasDerivAt.differentiableAt.differentiableWithinAt
  have hfc : BijOn f (closure U) (closedBall 0 1) :=
    ⟨by rw [← image_closure_eq_closedDisk hU hb hUV hfa hfb hfront]; exact mapsTo_image _ _,
      hfi.mono hUV,
      by rw [← image_closure_eq_closedDisk hU hb hUV hfa hfb hfront]; exact surjOn_image _ _⟩
  have hclosed : closedBall 0 1 ⊆ f '' V :=
    hfc.surjOn.trans (image_mono hUV)
  have hUsub : U ⊆ V := subset_closure.trans hUV
  have hdisk : ball 0 1 ⊆ f '' V := ball_subset_closedBall.trans hclosed
  have hiU : InvOn h f U (ball 0 1) := ⟨hinv.1.mono hUsub, hinv.2.mono hdisk⟩
  have hiC : InvOn h f (closure U) (closedBall 0 1) := ⟨hinv.1.mono hUV, hinv.2.mono hclosed⟩
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hWi hclosed
  rw [thickening_closedBall hδ zero_le_one] at hδsub
  have hfa0 : f a = 0 := (hfe ha).trans hf₀.normalized
  have h0 : h 0 = a := hfa0 ▸ hinv.1 (hUsub ha)
  exact ⟨V, δ + 1, f, h, hV, hUV, by linarith,
    hfa, hha.mono hδsub, hfi, (hBij.symm hinv.symm).injOn.mono hδsub,
    hfb, hfb.symm hiU.symm, hfc, hfc.symm hiC.symm, hiU, hfa0, h0,
    hfront, hinv, hδsub⟩

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.InteriorCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

namespace CrouzeixHilbert.Conformal

theorem exists_interiorCollar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) (hne : U.Nonempty)
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) : Nonempty (InteriorCollar U) := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨V,ρ,f,h,hV,hUV,hρ,hfa,hha,hfi,hhi,hfb,hhb,hfc,hhc,_,_,_,hfn,hinv,hd⟩ :=
    exists_conformal_collar hU hb hc ha hchart
  exact ⟨⟨V,hV,hUV,ρ,hρ,f,h,hfa,hha,hfi,hhi,hfb,hhb,hfc,hhc,hinv,hd,hfn⟩⟩

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ConvexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Coordinates. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem convex_image_subdisk {U : Set ℂ} (hconv : Convex ℝ U)
    {f h : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hbij : BijOn h (ball 0 1) U)
    (hinv : InvOn h f U (ball 0 1)) {r : ℝ} (hr1 : r ≤ 1) :
    Convex ℝ (h '' ball 0 r) := by
  rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩ a b ha hb hab
  have hvn : ‖v‖ < r := mem_ball_zero_iff.mp hv
  have hwn : ‖w‖ < r := mem_ball_zero_iff.mp hw
  obtain ⟨s, hslow, hsr⟩ := exists_between (max_lt hvn hwn)
  have hs : 0 < s := (norm_nonneg v).trans_lt (lt_of_le_of_lt (le_max_left _ _) hslow)
  have hvs : ‖v‖ < s := (le_max_left _ _).trans_lt hslow
  have hws : ‖w‖ < s := (le_max_right _ _).trans_lt hslow
  have hscale : ∀ z t : ℂ, ‖t‖ < s → z ∈ ball 0 1 → z * (t / (s : ℂ)) ∈ ball 0 1 := by
    intro z t ht hz
    rw [mem_ball_zero_iff, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have hc : ‖t‖ / s < 1 := (div_lt_one hs).mpr ht
    calc
      ‖z‖ * (‖t‖ / s) ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hc.le (norm_nonneg _)
      _ < 1 := by simpa only [mul_one] using mem_ball_zero_iff.mp hz
  let p : ℂ → ℂ := fun z => a • h (z * (v / (s : ℂ))) + b • h (z * (w / (s : ℂ)))
  have hpU : MapsTo p (ball 0 1) U := fun z hz =>
    hconv (hbij.mapsTo (hscale z v hvs hz)) (hbij.mapsTo (hscale z w hws hz)) ha hb hab
  have hpD : DifferentiableOn ℂ p (ball 0 1) := by
    intro z hz
    have h₁ : DifferentiableAt ℂ (fun z => h (z * (v / (s : ℂ)))) z := ((hh _ (hscale z v hvs hz)).differentiableAt
      (isOpen_ball.mem_nhds (hscale z v hvs hz))).comp z (differentiableAt_id.mul_const _)
    have h₂ : DifferentiableAt ℂ (fun z => h (z * (w / (s : ℂ)))) z := ((hh _ (hscale z w hws hz)).differentiableAt
      (isOpen_ball.mem_nhds (hscale z w hws hz))).comp z (differentiableAt_id.mul_const _)
    exact ((h₁.const_smul a).add (h₂.const_smul b)).differentiableWithinAt
  have hfmap : MapsTo f U (ball 0 1) := (hbij.symm hinv).mapsTo
  have hφD : DifferentiableOn ℂ (f ∘ p) (ball 0 1) := hf.comp hpD hpU
  have hφmap : MapsTo (f ∘ p) (ball 0 1) (closedBall 0 1) :=
    fun z hz => ball_subset_closedBall (hfmap (hpU hz))
  have hp0 : p 0 = h 0 := by simp only [p, zero_mul, ← add_smul, hab, one_smul]
  have hφ0 : (f ∘ p) 0 = 0 := by
    rw [comp_apply, hp0]
    exact hinv.2 (mem_ball_self zero_lt_one)
  have hs1 : ‖(s : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact hsr.trans_le hr1
  have hn := Complex.norm_le_norm_of_mapsTo_ball hφD hφmap hφ0 hs1
  have hps : p (s : ℂ) = a • h v + b • h w := by
    have hn : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [p, mul_div_cancel₀ _ hn]
  have hpUs : a • h v + b • h w ∈ U := hps ▸ hpU (mem_ball_zero_iff.mpr hs1)
  refine ⟨f (a • h v + b • h w), ?_, hinv.1 hpUs⟩
  apply mem_ball_zero_iff.mpr
  have he : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
  rw [comp_apply, hps, he] at hn
  exact hn.trans_lt hsr

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskBoundaryChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem localCayley_injOn : InjOn localCayley {z | I + z ≠ 0} := by
  intro z hz w hw he
  have hm := (div_eq_div_iff hz hw).mp he
  have he' : (z - w) * (2 * I) = 0 := by linear_combination -hm
  exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right (mul_ne_zero (by norm_num) I_ne_zero))

theorem localCayley_norm_lt_one {z : ℂ} (hz : I + z ≠ 0) :
    ‖localCayley z‖ < 1 ↔ 0 < z.im := by
  rw [localCayley, norm_div, div_lt_one (norm_pos_iff.mpr hz)]
  have he : ‖I + z‖ ^ 2 - ‖I - z‖ ^ 2 = 4 * z.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
    ring
  constructor <;> intro h <;> nlinarith [norm_nonneg (I + z), norm_nonneg (I - z)]

theorem localCayley_norm_le_one {z : ℂ} (hz : I + z ≠ 0) :
    ‖localCayley z‖ ≤ 1 ↔ 0 ≤ z.im := by
  rw [localCayley, norm_div, div_le_one (norm_pos_iff.mpr hz)]
  have he : ‖I + z‖ ^ 2 - ‖I - z‖ ^ 2 = 4 * z.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
    ring
  constructor <;> intro h <;> nlinarith [norm_nonneg (I + z), norm_nonneg (I - z)]

theorem analyticAt_localCayley {z : ℂ} (hz : I + z ≠ 0) :
    AnalyticAt ℂ localCayley z :=
  (analyticAt_const.sub analyticAt_id).div (analyticAt_const.add analyticAt_id) hz

theorem analyticOnNhd_symm (e : OpenPartialHomeomorph ℂ ℂ)
    (he : AnalyticOnNhd ℂ e e.source) : AnalyticOnNhd ℂ e.symm e.target := by
  apply DifferentiableOn.analyticOnNhd _ e.open_target
  intro z hz
  exact (e.hasStrictDerivAt_symm hz
    (deriv_ne_zero_of_injOn e.open_source he.differentiableOn e.injOn (e.map_target hz))
    (he _ (e.map_target hz)).hasStrictDerivAt).hasDerivAt.differentiableAt.differentiableWithinAt

theorem closure_image_subdisk {h : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hh : ContinuousOn h (ball 0 R)) :
    closure (h '' ball 0 r) = h '' closedBall 0 r := by
  have hc : ContinuousOn h (closedBall 0 r) := hh.mono (closedBall_subset_ball hrR)
  apply Subset.antisymm
  · apply closure_minimal (image_mono ball_subset_closedBall)
    exact ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn hc).isClosed
  · have hcl : closure (ball (0 : ℂ) r) = closedBall 0 r := closure_ball _ hr.ne'
    rw [← hcl] at hc ⊢
    exact hc.image_closure

theorem boundaryChart_image_subdisk {h : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn h (ball 0 R)) {p : ℂ} (hp : p ∈ frontier (h '' ball 0 r)) :
    Nonempty (BoundaryChart (h '' ball 0 r) p) := by
  have hclosed := closure_image_subdisk hr hrR hh.continuousOn
  have hopen := isOpen_image_of_univalent isOpen_ball (hh.mono (ball_subset_ball hrR.le))
    (hi.mono (ball_subset_ball hrR.le))
  obtain ⟨v, hv, rfl⟩ := hclosed ▸ hp.1
  have hvn : ‖v‖ = r := by
    apply le_antisymm (mem_closedBall_zero_iff.mp hv)
    by_contra hn
    have hvb : v ∈ ball 0 r := mem_ball_zero_iff.mpr (lt_of_not_ge hn)
    exact hp.2 (by rw [hopen.interior_eq]; exact ⟨v, hvb, rfl⟩)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (hvn ▸ hr.ne')
  have hvR : v ∈ ball 0 R := (closedBall_subset_ball hrR) hv
  let N : Set ℂ := {z | I + z ≠ 0} ∩ {z | v * localCayley z ∈ ball 0 R}
  have hNo : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact inter_mem
      ((continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
        (isClosed_singleton.isOpen_compl.mem_nhds hz.1))
      ((continuousAt_const.mul (analyticAt_localCayley hz.1).continuousAt).preimage_mem_nhds
        (isOpen_ball.mem_nhds hz.2))
  have hN0 : (0 : ℂ) ∈ N := by
    simp only [N, mem_inter_iff, mem_ofPred_eq, add_zero, localCayley_zero, mul_one]
    exact ⟨I_ne_zero, hvR⟩
  let χ : ℂ → ℂ := fun z => h (v * localCayley z)
  have hχa : AnalyticOnNhd ℂ χ N := by
    intro z hz
    have hc : AnalyticAt ℂ (fun w => v * localCayley w) z :=
      analyticAt_const.mul (analyticAt_localCayley hz.1)
    exact (hh _ hz.2).comp (f := fun w => v * localCayley w) (x := z) hc
  have hχi : InjOn χ N := by
    intro z hz w hw he
    exact localCayley_injOn hz.1 hw.1 (mul_left_cancel₀ hv0 (hi hz.2 hw.2 he))
  let d := (hχa 0 hN0).hasStrictDerivAt.hasStrictFDerivAt_equiv
    (deriv_ne_zero_of_injOn hNo hχa.differentiableOn hχi hN0)
  let e := (d.toOpenPartialHomeomorph χ).restrOpen N hNo
  have heN : e.source ⊆ N := inter_subset_right
  have hea : AnalyticOnNhd ℂ e e.source := hχa.mono heN
  have he0 : (0 : ℂ) ∈ e.source := ⟨d.mem_toOpenPartialHomeomorph_source, hN0⟩
  refine ⟨⟨e, he0, ?_, hea, analyticOnNhd_symm e hea, ?_, ?_⟩⟩
  · change h (v * localCayley 0) = h v
    simp only [localCayley_zero, mul_one]
  · intro z hz
    have hzN := heN hz
    have hm : h (v * localCayley z) ∈ h '' ball 0 r ↔ v * localCayley z ∈ ball 0 r := by
      constructor
      · rintro ⟨w, hw, he⟩
        exact hi ((ball_subset_ball hrR.le) hw) hzN.2 he ▸ hw
      · exact fun hw => ⟨_, hw, rfl⟩
    change h (v * localCayley z) ∈ h '' ball 0 r ↔ _
    rw [hm, mem_ball_zero_iff, norm_mul, hvn, mul_lt_iff_lt_one_right hr]
    exact localCayley_norm_lt_one hzN.1
  · intro z hz
    have hzN := heN hz
    have hm : h (v * localCayley z) ∈ h '' closedBall 0 r ↔ v * localCayley z ∈ closedBall 0 r := by
      constructor
      · rintro ⟨w, hw, he⟩
        exact hi ((closedBall_subset_ball hrR) hw) hzN.2 he ▸ hw
      · exact fun hw => ⟨_, hw, rfl⟩
    change h (v * localCayley z) ∈ closure (h '' ball 0 r) ↔ _
    rw [hclosed, hm, mem_closedBall_zero_iff, norm_mul, hvn, mul_le_iff_le_one_right hr]
    exact localCayley_norm_le_one hzN.1

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ConvexApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Approximation. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem isSimplyConnected_of_convex {U : Set ℂ} (hc : Convex ℝ U) (hne : U.Nonempty) :
    IsSimplyConnected U := by
  let _ := hc.contractibleSpace hne
  change SimplyConnectedSpace U
  infer_instance

theorem exists_convex_analytic_neighborhood {K V : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ U : Set ℂ, IsOpen U ∧ Bornology.IsBounded U ∧ Convex ℝ U ∧
      K ⊆ U ∧ closure U ⊆ V ∧
      (∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) := by
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_cthickening_subset_open hV hKV
  let N := thickening δ K
  have hNo : IsOpen N := isOpen_thickening
  have hNb : Bornology.IsBounded N := hK.isBounded.thickening
  have hNc : Convex ℝ N := hconv.thickening δ
  have hKN : K ⊆ N := self_subset_thickening hδ K
  obtain ⟨a, ha⟩ := hne
  have hNa : a ∈ N := hKN ha
  obtain ⟨f, h, hf, hh, hfb, hhb, hinv, _, _, _⟩ :=
    riemann_biholomorphic_bounded hNo hNb (isSimplyConnected_of_convex hNc ⟨a, hNa⟩) hNa
  obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn ⟨a, ha⟩ ((hf.continuousOn.mono hKN).norm)
  obtain ⟨r, hbr, hr1⟩ := exists_between (mem_ball_zero_iff.mp (hfb.mapsTo (hKN hb)))
  have hr : 0 < r := (norm_nonneg _).trans_lt hbr
  have hKU : K ⊆ h '' ball 0 r := by
    intro z hz
    exact ⟨f z, mem_ball_zero_iff.mpr ((hbmax hz).trans_lt hbr), hinv.1 (hKN hz)⟩
  have hha := hh.analyticOnNhd isOpen_ball
  have hUo := isOpen_image_of_univalent isOpen_ball (hha.mono (ball_subset_ball hr1.le))
    (hhb.injOn.mono (ball_subset_ball hr1.le))
  have hUc := convex_image_subdisk hNc hf hh hhb hinv hr1.le
  have hUclosed := closure_image_subdisk hr hr1 hh.continuousOn
  have hUsubN : closure (h '' ball 0 r) ⊆ N := by
    rw [hUclosed]
    rintro z ⟨w, hw, rfl⟩
    exact hhb.mapsTo ((closedBall_subset_ball hr1) hw)
  exact ⟨h '' ball 0 r, hUo, hNb.subset (subset_closure.trans hUsubN), hUc,
    hKU, hUsubN.trans ((thickening_subset_cthickening δ K).trans hδsub),
    fun p hp => boundaryChart_image_subdisk hr hr1 hha hhb.injOn hp⟩

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorRiemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Riemann. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem invertedExterior_mem_nhds_zero {K : Set ℂ} (hb : Bornology.IsBounded K) (a : ℂ) :
    invertedExterior K a ∈ 𝓝 0 := by
  obtain ⟨R, hR, hsub⟩ := hb.subset_ball_lt 0 a
  apply Metric.mem_nhds_iff.mpr
  refine ⟨R⁻¹, inv_pos.mpr hR, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  · apply Or.inr
    intro hk
    have hn := mem_ball.mp (hsub hk)
    rw [dist_eq_norm, add_sub_cancel_left, norm_inv] at hn
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hzr : ‖z‖ < R⁻¹ := mem_ball_zero_iff.mp hz
    have hback : R < ‖z‖⁻¹ := (lt_inv_comm₀ hR hnorm).mpr hzr
    exact (hback.trans hn).false

theorem isOpen_invertedExterior {K : Set ℂ} (hK : IsCompact K) (a : ℂ) :
    IsOpen (invertedExterior K a) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    exact invertedExterior_mem_nhds_zero hK.isBounded a
  · have hzn : a + z⁻¹ ∉ K := hz.resolve_left hz0
    have hc : ContinuousAt (fun w : ℂ => a + w⁻¹) z :=
      continuousAt_const.add (continuousAt_inv₀ hz0)
    filter_upwards [hc.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hzn)] with w hw
    exact Or.inr hw

theorem isBounded_invertedExterior {K : Set ℂ} {a : ℂ} (ha : a ∈ interior K) :
    Bornology.IsBounded (invertedExterior K a) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := ε⁻¹)).subset
  intro z hz
  apply mem_closedBall_zero_iff.mpr
  rcases hz with rfl | hzn
  · simpa only [norm_zero] using (inv_nonneg.mpr hε.le)
  · by_cases hz0 : z = 0
    · simpa only [hz0, norm_zero] using (inv_nonneg.mpr hε.le)
    · by_contra h
      have hlarge : ε⁻¹ < ‖z‖ := lt_of_not_ge h
      apply hzn
      apply hsub
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv]
      exact (inv_lt_comm₀ (norm_pos_iff.mpr hz0) hε).mpr hlarge

theorem starConvex_invertedExterior {K : Set ℂ} (hK : Convex ℝ K) {a : ℂ}
    (ha : a ∈ K) : StarConvex ℝ 0 (invertedExterior K a) := by
  intro z hz s t hs ht hst
  simp only [smul_zero, zero_add]
  by_cases ht0 : t = 0
  · simp only [ht0, zero_smul, zero_mem_invertedExterior]
  by_cases hz0 : z = 0
  · simp only [hz0, smul_zero, zero_mem_invertedExterior]
  apply Or.inr
  intro hk
  have hi := hK.add_smul_sub_mem ha hk (show t ∈ Icc 0 1 by constructor <;> linarith)
  have he : a + t • (a + (t • z)⁻¹ - a) = a + z⁻¹ := by
    simp only [Complex.real_smul, add_sub_cancel_left, mul_inv_rev]
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    field_simp
  rw [he] at hi
  exact (hz.resolve_left hz0) hi

theorem isSimplyConnected_invertedExterior {K : Set ℂ} (hK : Convex ℝ K) {a : ℂ}
    (ha : a ∈ K) : IsSimplyConnected (invertedExterior K a) := by
  let _ := (starConvex_invertedExterior hK ha).contractibleSpace
    (show (invertedExterior K a).Nonempty from ⟨0, zero_mem_invertedExterior K a⟩)
  change SimplyConnectedSpace (invertedExterior K a)
  infer_instance

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorBoundaryChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem closed_side_of_side (e : OpenPartialHomeomorph ℂ ℂ) {U : Set ℂ}
    (hs : ∀ z ∈ e.source, e z ∈ U ↔ 0 < z.im) :
    ∀ z ∈ e.source, e z ∈ closure U ↔ 0 ≤ z.im := by
  have hi : e.IsImage {z : ℂ | 0 < z.im} U := fun _ hz => hs _ hz
  intro z hz
  simpa only [closure_setOfPred_lt_im, mem_ofPred_eq] using hi.closure hz

theorem frontier_invertedExterior {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (a : ℂ) {z : ℂ}
    (hz : z ∈ frontier (invertedExterior (closure U) a)) :
    z ≠ 0 ∧ a + z⁻¹ ∈ frontier U := by
  have hI := isOpen_invertedExterior hb.isCompact_closure a
  have hzn : z ∉ invertedExterior (closure U) a := by
    simpa only [hI.interior_eq] using hz.2
  have hz0 : z ≠ 0 := fun he => hzn (Or.inl he)
  have hzc : a + z⁻¹ ∈ closure U := by
    by_contra hn
    exact hzn (Or.inr hn)
  refine ⟨hz0, hzc, ?_⟩
  rw [hU.interior_eq]
  intro hzu
  have hn : {w : ℂ | w ≠ 0 ∧ a + w⁻¹ ∈ U} ∈ 𝓝 z :=
    inter_mem (isClosed_singleton.isOpen_compl.mem_nhds hz0)
      ((continuousAt_const.add (continuousAt_inv₀ hz0)).preimage_mem_nhds (hU.mem_nhds hzu))
  obtain ⟨w, hw, hwI⟩ := mem_closure_iff_nhds.mp hz.1 _ hn
  exact (hwI.resolve_left hw.1) (subset_closure hw.2)

theorem boundaryChart_invertedExterior {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {a : ℂ} (_ha : a ∈ U)
    (hc : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p))
    {p : ℂ} (hp : p ∈ frontier (invertedExterior (closure U) a)) :
    Nonempty (BoundaryChart (invertedExterior (closure U) a) p) := by
  obtain ⟨hp0, hpf⟩ := frontier_invertedExterior hU hb a hp
  obtain ⟨c⟩ := hc _ hpf
  let N : Set ℂ := {z | -z ∈ c.e.source ∧ c.e (-z) ≠ a}
  have hNo : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact inter_mem ((continuous_neg).continuousAt.preimage_mem_nhds
      (c.e.open_source.mem_nhds hz.1))
      (((c.analytic _ hz.1).continuousAt.comp continuous_neg.continuousAt).preimage_mem_nhds
        (isClosed_singleton.isOpen_compl.mem_nhds hz.2))
  have hN0 : (0 : ℂ) ∈ N := by
    refine ⟨by simpa only [neg_zero] using c.zero_mem, ?_⟩
    simp only [neg_zero, c.at_zero, ne_eq, add_eq_left, inv_eq_zero]
    exact hp0
  let χ : ℂ → ℂ := fun z => (c.e (-z) - a)⁻¹
  have hχa : AnalyticOnNhd ℂ χ N := by
    intro z hz
    exact (((c.analytic _ hz.1).comp (show AnalyticAt ℂ (fun z : ℂ => -z) z from
      analyticAt_id.neg)).sub analyticAt_const).inv (sub_ne_zero.mpr hz.2)
  have hχi : InjOn χ N := by
    intro z hz w hw he
    exact neg_injective (c.e.injOn hz.1 hw.1
      (sub_left_injective (inv_injective he)))
  let d := (hχa 0 hN0).hasStrictDerivAt.hasStrictFDerivAt_equiv
    (deriv_ne_zero_of_injOn hNo hχa.differentiableOn hχi hN0)
  let e := (d.toOpenPartialHomeomorph χ).restrOpen N hNo
  have heN : e.source ⊆ N := inter_subset_right
  have hea : AnalyticOnNhd ℂ e e.source := hχa.mono heN
  have he0 : (0 : ℂ) ∈ e.source := ⟨d.mem_toOpenPartialHomeomorph_source, hN0⟩
  have hs : ∀ z ∈ e.source,
      e z ∈ invertedExterior (closure U) a ↔ 0 < z.im := by
    intro z hz
    have hzN := heN hz
    change ((c.e (-z) - a)⁻¹ = 0 ∨ a + ((c.e (-z) - a)⁻¹)⁻¹ ∉ closure U) ↔ _
    simp only [inv_eq_zero, sub_eq_zero, hzN.2, false_or, inv_inv, add_sub_cancel,
      c.closed_side _ hzN.1, neg_im, not_le, neg_lt_zero]
  refine ⟨⟨e, he0, ?_, hea, analyticOnNhd_symm e hea, hs, closed_side_of_side e hs⟩⟩
  change (c.e (-0) - a)⁻¹ = p
  simp only [neg_zero, c.at_zero, add_sub_cancel_left, inv_inv]

theorem exists_inverted_exterior_collar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hconv : Convex ℝ U) {a : ℂ} (ha : a ∈ U)
    (hc : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (ρ : ℝ) (f h : ℂ → ℂ),
      IsOpen V ∧ closure (invertedExterior (closure U) a) ⊆ V ∧ 1 < ρ ∧
      AnalyticOnNhd ℂ f V ∧ AnalyticOnNhd ℂ h (ball 0 ρ) ∧
      InjOn f V ∧ InjOn h (ball 0 ρ) ∧
      BijOn f (invertedExterior (closure U) a) (ball 0 1) ∧
      BijOn h (ball 0 1) (invertedExterior (closure U) a) ∧
      BijOn f (closure (invertedExterior (closure U) a)) (closedBall 0 1) ∧
      BijOn h (closedBall 0 1) (closure (invertedExterior (closure U) a)) ∧
      InvOn h f (invertedExterior (closure U) a) (ball 0 1) ∧ f 0 = 0 ∧ h 0 = 0 ∧
      (∀ z ∈ frontier (invertedExterior (closure U) a), ‖f z‖ = 1) ∧
      InvOn h f V (f '' V) ∧ ball 0 ρ ⊆ f '' V := by
  apply exists_conformal_collar (isOpen_invertedExterior hb.isCompact_closure a)
    (isBounded_invertedExterior (interior_mono subset_closure (hU.interior_eq.symm ▸ ha)))
    (isSimplyConnected_invertedExterior hconv.closure (subset_closure ha))
    (zero_mem_invertedExterior _ _)
  exact fun p hp => boundaryChart_invertedExterior hU hb ha hc hp

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem mem_closure_invertedExterior {U : Set ℂ} (hU : IsOpen U)
    (hc : Convex ℝ U) (hne : U.Nonempty) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    z ∈ closure (invertedExterior (closure U) a) ↔ a + z⁻¹ ∉ U := by
  have hi : (inversionChart a).IsImage (invertedExterior (closure U) a) (closure U)ᶜ := by
    intro w hw
    change a + w⁻¹ ∉ closure U ↔ w = 0 ∨ a + w⁻¹ ∉ closure U
    simp only [show w ≠ 0 from hw, false_or]
  have hreg : interior (closure U) = U :=
    (hc.interior_closure_eq_interior_of_nonempty_interior (hU.interior_eq.symm ▸ hne)).trans hU.interior_eq
  have he := (hi.closure hz).symm
  change (z ∈ closure (invertedExterior (closure U) a) ↔ a + z⁻¹ ∈ closure (closure U)ᶜ) at he
  simpa only [closure_compl, hreg, mem_compl_iff] using he

theorem reciprocal_simple_pole {ρ : ℝ} (hρ : 0 < ρ) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (ball 0 ρ)) (hi : InjOn h (ball 0 ρ)) (h0 : h 0 = 0)
    (a : ℂ) :
    ∃ (b : ℂ) (g : ℂ → ℂ), b ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 ρ) ∧
      ∀ t : ℂ, ρ⁻¹ < ‖t‖ → a + (h t⁻¹)⁻¹ = b * t + g t⁻¹ := by
  let k := dslope h 0
  have hk : AnalyticOnNhd ℂ k (ball 0 ρ) :=
    ((differentiableOn_dslope (ball_mem_nhds 0 hρ)).mpr hh.differentiableOn).analyticOnNhd isOpen_ball
  have hkn : ∀ z ∈ ball 0 ρ, k z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      simpa only [k, dslope_same] using
        deriv_ne_zero_of_injOn isOpen_ball hh.differentiableOn hi (mem_ball_self hρ)
    · have hn : h z ≠ 0 := fun he => hz0 (hi hz (mem_ball_self hρ) (he.trans h0.symm))
      simpa only [k, dslope_of_ne h hz0, slope_def_field, sub_zero, h0] using div_ne_zero hn hz0
  let l := fun z => (k z)⁻¹
  have hl : AnalyticOnNhd ℂ l (ball 0 ρ) := fun z hz => (hk z hz).inv (hkn z hz)
  let g := fun z => a + dslope l 0 z
  have hg : AnalyticOnNhd ℂ g (ball 0 ρ) := fun z hz =>
    analyticAt_const.add (((differentiableOn_dslope (ball_mem_nhds 0 hρ)).mpr hl.differentiableOn).analyticOnNhd isOpen_ball z hz)
  refine ⟨l 0, g, inv_ne_zero (hkn 0 (mem_ball_self hρ)), hg, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := norm_pos_iff.mp ((inv_pos.mpr hρ).trans ht)
  have hu0 := inv_ne_zero ht0
  have hhu : h t⁻¹ ≠ 0 := by
    have hu : t⁻¹ ∈ ball 0 ρ := mem_ball_zero_iff.mpr (by
      rw [norm_inv]; exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hρ).mpr ht)
    exact fun he => hu0 (hi hu (mem_ball_self hρ) (he.trans h0.symm))
  simp only [g, k, l, dslope_of_ne h hu0, h0, sub_zero, slope_def_field,
    dslope_of_ne (fun z => (dslope h 0 z)⁻¹) hu0]
  field_simp
  ring

theorem exists_exteriorCollar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : Convex ℝ U) {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    Nonempty (ExteriorCollar U) := by
  obtain ⟨V, ρ, f, h, hV, hIV, hρ, hf, hh, hfi, hhi, hfb, hhb, hfc, hhc,
    hinv, hf0, hh0, hfront, hinvV, hρV⟩ := exists_inverted_exterior_collar hU hb hc ha hchart
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  let I := invertedExterior (closure U) a
  let G : ℂ → ℂ := fun t => a + (h t⁻¹)⁻¹
  have ht0 : ∀ t : ℂ, ρ⁻¹ < ‖t‖ → t ≠ 0 := fun t ht =>
    norm_pos_iff.mp ((inv_pos.mpr hρ0).trans ht)
  have hti : ∀ t : ℂ, ρ⁻¹ < ‖t‖ → t⁻¹ ∈ ball 0 ρ := by
    intro t ht
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr (ht0 t ht)) hρ0).mpr ht
  have hhn : ∀ z ∈ ball 0 ρ, z ≠ 0 → h z ≠ 0 :=
    fun z hz hz0 he => hz0 (hhi hz (mem_ball_self hρ0) (he.trans hh0.symm))
  have hhiC : InvOn h f (closure I) (closedBall 0 1) :=
    ⟨hinvV.1.mono hIV, hinvV.2.mono ((closedBall_subset_ball hρ).trans hρV)⟩
  have hr1 : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).mpr hρ
  have hGinj : InjOn G {t | ρ⁻¹ < ‖t‖} := by
    intro t ht s hs he
    exact inv_injective (hhi (hti t ht) (hti s hs) (inv_injective (add_left_cancel he)))
  have hGe : ∀ t : ℂ, 1 ≤ ‖t‖ → t⁻¹ ∈ closedBall 0 1 := by
    intro t ht
    rw [mem_closedBall_zero_iff, norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le ht)).mpr ht
  have hGo : ∀ t : ℂ, 1 < ‖t‖ → t⁻¹ ∈ ball 0 1 := by
    intro t ht
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_one₀ (zero_lt_one.trans ht)).mpr ht
  have hGb : BijOn G {t | 1 < ‖t‖} (closure U)ᶜ := by
    refine ⟨?_, hGinj.mono (fun t ht => hr1.trans ht), ?_⟩
    · intro t ht
      exact (hhb.mapsTo (hGo t ht)).resolve_left (hhn _ (hti t (hr1.trans ht)) (inv_ne_zero (ht0 t (hr1.trans ht))))
    · intro z hz
      have hza : z - a ≠ 0 := fun he => hz (sub_eq_zero.mp he ▸ subset_closure ha)
      have hzi : (z - a)⁻¹ ∈ I := Or.inr (by simpa only [inv_inv, add_sub_cancel, mem_compl_iff] using hz)
      let v := f (z - a)⁻¹
      have hv : v ∈ ball 0 1 := hfb.mapsTo hzi
      have hv0 : v ≠ 0 := fun he => inv_ne_zero hza
        (hfb.injOn hzi (zero_mem_invertedExterior _ _) (he.trans hf0.symm))
      refine ⟨v⁻¹, ?_, ?_⟩
      · change 1 < ‖v⁻¹‖
        rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hv0)]
        exact mem_ball_zero_iff.mp hv
      · simp only [G, inv_inv, v, hinv.1 hzi, add_sub_cancel]
  have hGf : BijOn G (sphere 0 1) (frontier U) := by
    refine ⟨?_, hGinj.mono (fun t ht => by change ρ⁻¹ < ‖t‖; rwa [mem_sphere_zero_iff_norm.mp ht]), ?_⟩
    · intro t ht
      have htn : ‖t‖ = 1 := mem_sphere_zero_iff_norm.mp ht
      have htS : ρ⁻¹ < ‖t‖ := htn ▸ hr1
      have htvn : ‖t⁻¹‖ = 1 := by rw [norm_inv, htn, inv_one]
      have hin : h t⁻¹ ∈ frontier I := by
        refine ⟨hhc.mapsTo (hGe t htn.ge), ?_⟩
        rw [(isOpen_invertedExterior hb.isCompact_closure a).interior_eq]
        intro he
        have heq := hhiC.2 (hGe t htn.ge)
        have hsmall := mem_ball_zero_iff.mp (hfb.mapsTo he)
        rw [heq, htvn] at hsmall
        exact (lt_irrefl 1 hsmall)
      exact (frontier_invertedExterior hU hb a hin).2
    · intro z hz
      have hza : z - a ≠ 0 := fun he => hz.2 (by rw [hU.interior_eq]; exact sub_eq_zero.mp he ▸ ha)
      let v := (z - a)⁻¹
      have hv0 : v ≠ 0 := inv_ne_zero hza
      have hvC : v ∈ closure I := (mem_closure_invertedExterior hU hc ⟨a, ha⟩ a hv0).mpr (by
        simpa only [v, inv_inv, add_sub_cancel, hU.interior_eq] using hz.2)
      have hvn : v ∉ I := by
        intro he
        have := he.resolve_left hv0
        exact this (by simpa only [v, inv_inv, add_sub_cancel] using hz.1)
      have hvF : v ∈ frontier I := ⟨hvC, fun he => hvn (interior_subset he)⟩
      have hfv : ‖f v‖ = 1 := hfront _ hvF
      refine ⟨(f v)⁻¹, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_inv, hfv, inv_one]
      · change a + (h ((f v)⁻¹)⁻¹)⁻¹ = z
        rw [inv_inv, hhiC.1 hvC]
        simp only [v, inv_inv, add_sub_cancel]
  have hGin : MapsTo G {t | ρ⁻¹ < ‖t‖ ∧ ‖t‖ < 1} U := by
    intro t ht
    by_contra hn
    have hvC : h t⁻¹ ∈ closure I :=
      (mem_closure_invertedExterior hU hc ⟨a, ha⟩ a
        (hhn _ (hti t ht.1) (inv_ne_zero (ht0 t ht.1)))).mpr hn
    obtain ⟨v, hv, he⟩ := hhc.surjOn hvC
    have hvt : v = t⁻¹ := hhi ((closedBall_subset_ball hρ) hv) (hti t ht.1) he
    have hle : ‖t‖⁻¹ ≤ 1 := by simpa only [hvt, norm_inv, mem_closedBall_zero_iff] using hv
    exact (not_le_of_gt ht.2) ((inv_le_one₀ (norm_pos_iff.mpr (ht0 t ht.1))).mp hle)
  have hGa : AnalyticOnNhd ℂ G {t | ρ⁻¹ < ‖t‖} := by
    intro t ht
    exact analyticAt_const.add (((hh _ (hti t ht)).comp
      (analyticAt_id.inv (ht0 t ht))).inv (hhn _ (hti t ht) (inv_ne_zero (ht0 t ht))))
  obtain ⟨b, g, hbn, hga, hLaur⟩ := reciprocal_simple_pole hρ0 hh hhi hh0 a
  exact ⟨⟨ρ⁻¹, inv_pos.mpr hρ0, hr1, G, hGa, hGinj, hGb, hGf, hGin,
    b, hbn, g, by simpa only [inv_inv] using hga, hLaur⟩⟩

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CompleteFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete Finite. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

lemma entrywiseHolomorphic_matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (V : Set ℂ) : EntrywiseHolomorphic V (matrixPolynomial B) := by
  intro i j
  simp only [matrixPolynomial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply DifferentiableOn.fun_sum
  intro k _
  exact (differentiableOn_id.pow (k : ℕ)).mul_const _

lemma matrixHolomorphicEval_matrixPolynomial
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {V : Set ℂ} (hV : IsOpen V) (hKV : numericalClosure A ⊆ V)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    matrixHolomorphicEval A V (matrixPolynomial B) = polynomialEval A B := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hV hKV
  have he : matrixHolomorphicEval A V (matrixPolynomial B) =
      matrixContourEval A Γ.toSmoothContour (matrixPolynomial B) := by
    simp only [matrixHolomorphicEval, matrixContourEval,
      holomorphicEval_eq_contourEval A hV (entrywiseHolomorphic_matrixPolynomial B V _ _) Γ]
  rw [he, matrixContourEval_matrixPolynomial A Γ B]

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {n : ℕ} (hn : 0 < n) (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U)

include C R hn hKU hU hc hb

lemma polynomial_bound {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (closure U) (matrixPolynomial B) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  rw [← matrixHolomorphicEval_matrixPolynomial A isOpen_univ (subset_univ _) B]
  exact C.holomorphic_bound R hn A hKU hU hc hb isOpen_univ (subset_univ _)
    (entrywiseHolomorphic_matrixPolynomial B univ)

end Conformal.ExteriorCollar

theorem finite_matrix_polynomial_bound : FiniteMatrixPolynomialBound := by
  intro n hn M m _ d B
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let A := Matrix.toEuclideanCLM (𝕜 := ℂ) M
  change ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B)
  rw [(polynomial_sup_eq_max A B).1]
  let K := numericalClosure A
  let P := matrixPolynomial B
  have hK := isCompact_numericalClosure A
  have hc := convex_numericalClosure A
  have hne : K.Nonempty := numericalClosure_nonempty A
  have hsup := supNorm_bddAbove hK (continuous_matrixPolynomial B).continuousOn
  have hs0 := supNorm_nonneg hsup
  apply le_of_forall_pos_le_add
  intro ε hε
  let V := {z : ℂ | ‖P z‖ < supNorm K P + ε / 2}
  have hV : IsOpen V := isOpen_lt (continuous_matrixPolynomial B).norm continuous_const
  have hKV : K ⊆ V := fun z hz => (norm_le_supNorm hsup hz).trans_lt (by dsimp only [K,P]; linarith)
  obtain ⟨U,hU,hb,hcU,hKU,hUV,hchart⟩ := Conformal.exists_convex_analytic_neighborhood
    hK hc hne hV hKV
  obtain ⟨a,ha⟩ := hne
  obtain ⟨R⟩ := Conformal.exists_interiorCollar hU hb
    (Conformal.isSimplyConnected_of_convex hcU ⟨a,hKU ha⟩) ⟨a,hKU ha⟩ hchart
  obtain ⟨C⟩ := Conformal.exists_exteriorCollar hU hb hcU (hKU ha) hchart
  have hg := C.polynomial_bound R hn A hKU hU hcU hb B
  have hs : supNorm (closure U) P ≤ supNorm K P + ε / 2 :=
    supNorm_le (by dsimp only [K,P]; linarith) (fun z hz => (hUV hz).le)
  calc
    ‖polynomialEval A B‖ ≤ 2 * supNorm (closure U) P := hg
    _ ≤ 2 * (supNorm K P + ε / 2) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = 2 * supNorm (numericalClosure A) (matrixPolynomial B) + ε := by dsimp only [K,P]; ring

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HilbertInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert Inequality. -/

namespace CrouzeixHilbert

universe u

theorem hilbert_oai (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Operator H) :
    (Nontrivial H → NonzeroConclusion A) ∧
    (Subsingleton H → ZeroConclusion A) ∧ SharpConstant := by
  exact hilbert_of_finite_matrix_bound finite_matrix_polynomial_bound H A

end CrouzeixHilbert


end OAI
end

theorem solution.{u} : type_of% @OAI.CrouzeixHilbert.hilbert_oai.{u} := @OAI.CrouzeixHilbert.hilbert_oai.{u}
