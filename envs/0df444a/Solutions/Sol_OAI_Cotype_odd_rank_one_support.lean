-- Prove2me | solution 1 for OAI.Cotype.odd_rank_one_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:16:09.445492+00:00
-- url     : https://prove2.me/submissions/9a0a57bd-f55b-4554-85c4-a582775a9787

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank

open OAI OAI.Cotype
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
theorem h50d_neg_char {α : Type*} [Fintype α] (p ε : α → Bool) :
    character p (negateCube ε) = paritySign p * character p ε := by
  unfold character paritySign negateCube
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases p i <;> cases ε i <;> simp

theorem h50d_odd {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → ℝ) (p : α → Bool) :
    fourier (oddPart f) p = (1 - paritySign p) / 2 * fourier f p := by
  have hsub : ∑ ε, f (negateCube ε) * character p ε = paritySign p * ∑ ε, f ε * character p ε := by
    rw [← Equiv.sum_comp negateEquiv]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    show f (negateCube (negateCube ε)) * character p (negateCube ε) = _
    rw [negateCube_negateCube, h50d_neg_char]; ring
  simp only [Cotype.fourier, average, smul_eq_mul, oddPart]
  have : ∑ ε, (f ε - f (negateCube ε)) / 2 * character p ε =
      (∑ ε, f ε * character p ε - ∑ ε, f (negateCube ε) * character p ε) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun ε _ => ?_; ring
  rw [this, hsub]; ring

theorem h50d_col_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ (ZMod 2)) (hM : M.rank ≤ 1) (j j' : κ)
    (hj : M.col j ≠ 0) (hj' : M.col j' ≠ 0) : M.col j = M.col j' := by
  rw [Matrix.rank_eq_finrank_span_cols] at hM
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hM
  have key : ∀ w : Submodule.span (ZMod 2) (Set.range M.col), w ≠ 0 → w = v := by
    intro w hw
    obtain ⟨c, hc⟩ := hv w
    rcases (show c = 0 ∨ c = 1 by fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl) with rfl | rfl
    · rw [zero_smul] at hc; exact absurd hc.symm hw
    · rw [one_smul] at hc; exact hc.symm
  have m1 : M.col j ∈ Submodule.span (ZMod 2) (Set.range M.col) :=
    Submodule.subset_span ⟨j, rfl⟩
  have m2 : M.col j' ∈ Submodule.span (ZMod 2) (Set.range M.col) :=
    Submodule.subset_span ⟨j', rfl⟩
  have e1 := key ⟨_, m1⟩ (by intro h; apply hj; simpa using congrArg Subtype.val h)
  have e2 := key ⟨_, m2⟩ (by intro h; apply hj'; simpa using congrArg Subtype.val h)
  have := e1.trans e2.symm
  simpa using congrArg Subtype.val this

theorem h50d_paritySign {α : Type*} [Fintype α] (p : α → Bool) :
    paritySign p = (-1 : ℝ) ^ (Finset.univ.filter (fun a => p a = true)).card := by
  unfold paritySign
  rw [Finset.prod_ite]
  simp

theorem solution {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f)
    {P : (ι × κ) → Bool} (hcoef : fourier f P ≠ 0)
    (hP : (binaryMatrix P).rank ≤ 1) :
    ∃ (s : Finset ι) (t : Finset κ),
      Odd s.card ∧ Odd t.card ∧ rectangle s t = P := by
  classical
  have hP_rank := hP
  -- parity of the support
  have hodd : paritySign P = -1 := by
    have h := h50d_odd f P
    have hof : oddPart f = f := by
      funext ε; simp only [oddPart, hf ε]; ring
    rw [hof] at h
    have : (1 - paritySign P) / 2 = 1 := by
      have := mul_right_cancel₀ hcoef (h.symm.trans (one_mul _).symm)
      exact this
    linarith
  set s : Finset ι := Finset.univ.filter (fun i => ∃ j, P (i, j) = true) with hs
  set t : Finset κ := Finset.univ.filter (fun j => ∃ i, P (i, j) = true) with ht
  have hentry : ∀ i j, binaryMatrix P i j = 1 ↔ P (i, j) = true := by
    intro i j; unfold binaryMatrix; cases P (i, j) <;> simp
  have hrect : rectangle s t = P := by
    funext ⟨i, j⟩
    simp only [rectangle, hs, ht, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hP : P (i, j) = true
    · rw [hP]; simp only [decide_eq_true_eq]; exact ⟨⟨j, hP⟩, ⟨i, hP⟩⟩
    · rw [Bool.not_eq_true] at hP
      rw [hP]
      simp only [decide_eq_false_iff_not, not_and]
      rintro ⟨j', hj'⟩ ⟨i', hi'⟩
      have c1 : (binaryMatrix P).col j ≠ 0 := by
        intro h0; have := congrFun h0 i'
        simp only [Matrix.col_apply, Pi.zero_apply] at this
        rw [(hentry i' j).mpr hi'] at this; exact one_ne_zero this
      have c2 : (binaryMatrix P).col j' ≠ 0 := by
        intro h0; have := congrFun h0 i
        simp only [Matrix.col_apply, Pi.zero_apply] at this
        rw [(hentry i j').mpr hj'] at this; exact one_ne_zero this
      have := congrFun (h50d_col_eq _ hP_rank j j' c1 c2) i
      simp only [Matrix.col_apply] at this
      rw [(hentry i j').mpr hj'] at this
      have := (hentry i j).mp this
      rw [hP] at this; exact absurd this (by simp)
  have hcard : (Finset.univ.filter (fun a : ι × κ => P a = true)).card = s.card * t.card := by
    rw [← Finset.card_product]
    congr 1
    ext ⟨i, j⟩
    have := congrFun hrect (i, j)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [← this]; simp [rectangle]
  rw [h50d_paritySign, hcard] at hodd
  have hodd' : Odd (s.card * t.card) := by
    rcases Nat.even_or_odd (s.card * t.card) with he | ho
    · rw [he.neg_one_pow] at hodd; norm_num at hodd
    · exact ho
  rw [Nat.odd_mul] at hodd'
  exact ⟨s, t, hodd'.1, hodd'.2, hrect⟩

