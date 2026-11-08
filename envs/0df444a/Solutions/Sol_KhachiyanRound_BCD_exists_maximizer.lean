-- Prove2me | solution 1 for KhachiyanRound.BCD.exists_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:44:39.262775+00:00
-- url     : https://prove2.me/submissions/2405e559-123f-401e-9111-973a12b68170

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise
open Matrix

open KhachiyanRound.BCD in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (hfull : affineSpan ℝ (Set.range a) = ⊤) :
    ∃ pstar ∈ SF a, (∀ q ∈ SF a, F a q ≤ F a pstar) ∧ F a pstar = Fstar a := by
  classical
  -- the index set is nonempty
  have hne : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    rw [Set.range_eq_empty a, AffineSubspace.span_empty] at hfull
    exact absurd hfull (AffineSubspace.bot_ne_top _ _ _)
  -- the points are not contained in a hyperplane through the origin
  have hsep : ∀ x : Fin n → ℝ, x ≠ 0 → ∃ i, a i ⬝ᵥ x ≠ 0 := by
    intro x hx
    by_contra h
    push_neg at h
    let K : Submodule ℝ (Fin n → ℝ) :=
      { carrier := {y | y ⬝ᵥ x = 0}
        add_mem' := by
          intro u v hu hv
          simp only [Set.mem_setOf_eq] at *
          rw [add_dotProduct, hu, hv, add_zero]
        zero_mem' := by simp
        smul_mem' := by
          intro c u hu
          simp only [Set.mem_setOf_eq] at *
          rw [smul_dotProduct, hu, smul_zero] }
    have hle : affineSpan ℝ (Set.range a) ≤ K.toAffineSubspace := by
      apply affineSpan_le_of_subset_coe
      rintro _ ⟨i, rfl⟩
      exact Submodule.mem_toAffineSubspace.mpr (h i)
    rw [hfull] at hle
    have hx' : x ∈ K.toAffineSubspace := hle (AffineSubspace.mem_top ℝ _ x)
    rw [Submodule.mem_toAffineSubspace] at hx'
    have hxx : x ⬝ᵥ x = 0 := hx'
    exact hx (dotProduct_self_eq_zero.mp hxx)
  -- quadratic form of the moment matrix
  have hquad : ∀ (p : ι → ℝ) (x : Fin n → ℝ),
      x ⬝ᵥ (momentMatrix a p *ᵥ x) = ∑ i, p i * (a i ⬝ᵥ x) ^ 2 := by
    intro p x
    rw [momentMatrix, Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.smul_mulVec, vecMulVec_mulVec, dotProduct_smul]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_smul,
      dotProduct_comm x (a i)]
    ring
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set p0 : ι → ℝ := fun _ => 1 / (Fintype.card ι : ℝ) with hp0
  have hp0S : p0 ∈ stdSimplex ℝ ι := by
    refine ⟨fun _ => by positivity, ?_⟩
    rw [hp0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hp0pos : 0 < (momentMatrix a p0).det := by
    apply Matrix.PosDef.det_pos
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simp only [conjTranspose_apply, star_trivial, momentMatrix, Matrix.sum_apply,
        Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · intro x hx
      rw [star_trivial, hquad]
      obtain ⟨i, hi⟩ := hsep x hx
      apply Finset.sum_pos'
      · intro j _
        exact mul_nonneg (by positivity) (sq_nonneg _)
      · exact ⟨i, Finset.mem_univ _, mul_pos (by positivity) (by positivity)⟩
  have hcont : Continuous fun p : ι → ℝ => (momentMatrix a p).det := by
    apply Continuous.matrix_det
    unfold momentMatrix
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).smul continuous_const
  obtain ⟨ps, hps, hmax⟩ := (isCompact_stdSimplex ℝ ι).exists_isMaxOn ⟨p0, hp0S⟩
    hcont.continuousOn
  have hmax' := isMaxOn_iff.mp hmax
  have hpsdet : 0 < (momentMatrix a ps).det := lt_of_lt_of_le hp0pos (hmax' p0 hp0S)
  have hpsSF : ps ∈ SF a := ⟨hps, hpsdet⟩
  have hle : ∀ q ∈ SF a, F a q ≤ F a ps := by
    intro q hq
    unfold F
    exact Real.log_le_log hq.2 (hmax' q hq.1)
  refine ⟨ps, hpsSF, hle, ?_⟩
  unfold Fstar
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨ps, hpsSF, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact hle q hq
