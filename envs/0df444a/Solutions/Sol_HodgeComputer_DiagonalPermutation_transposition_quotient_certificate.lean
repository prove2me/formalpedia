-- Prove2me | solution 1 for HodgeComputer.DiagonalPermutation.transposition_quotient_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T05:01:48.902475+00:00
-- url     : https://prove2.me/submissions/e92ae65a-f85e-4609-9084-f05fc6e0e766
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_ReflectionChart_certificate_of_relative_primitive
import Theorems.Thm_HodgeComputer_DiagonalPermutation_chart_and_target_irreducible
import Theorems.Thm_HodgeComputer_DiagonalPermutation_relative_primitive_exists
import Definitions.Def_HodgeComputerDiagonalPermutationQuotient
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace DiagQuotientSketch
open MvPolynomial HodgeComputer HodgeComputer.DiagonalPermutation HodgeComputer.ReflectionChart

private lemma F_hom : F.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 6) ℂ
  have hC := isHomogeneous_C (Fin 6) (R := ℂ)
  have h5 : (5 : AmbientPoly 5).IsHomogeneous 0 := by rw [← map_ofNat C 5]; exact hC _
  have hm1 (i : Fin 6) : ((X i : AmbientPoly 5) ^ 6).IsHomogeneous 6 := (hX i).pow 6
  have hm4 (a : ℂ) (i j k l : Fin 6) :
      ((((((5 : AmbientPoly 5) * X i ^ 3) * X j) * X k) * X l) * C a).IsHomogeneous 6 := by
    simpa using ((((h5.mul ((hX i).pow 3)).mul (hX j)).mul (hX k)).mul (hX l)).mul (hC a)
  have hm3a (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i ^ 3) * X j) * X k ^ 2) * C a).IsHomogeneous 6 := by
    simpa using (((h5.mul ((hX i).pow 3)).mul (hX j)).mul ((hX k).pow 2)).mul (hC a)
  have hm3b (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i ^ 2) * X j ^ 3) * X k) * C a).IsHomogeneous 6 := by
    simpa using (((h5.mul ((hX i).pow 2)).mul ((hX j).pow 3)).mul (hX k)).mul (hC a)
  have hm3c (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i ^ 2) * X j) * X k ^ 3) * C a).IsHomogeneous 6 := by
    simpa using (((h5.mul ((hX i).pow 2)).mul (hX j)).mul ((hX k).pow 3)).mul (hC a)
  have hm13 (a : ℂ) (i j k l : Fin 6) :
      ((((((5 : AmbientPoly 5) * X i) * X j ^ 3) * X k) * X l) * C a).IsHomogeneous 6 := by
    simpa using ((((h5.mul (hX i)).mul ((hX j).pow 3)).mul (hX k)).mul (hX l)).mul (hC a)
  have hm132 (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i) * X j ^ 3) * X k ^ 2) * C a).IsHomogeneous 6 := by
    simpa using (((h5.mul (hX i)).mul ((hX j).pow 3)).mul ((hX k).pow 2)).mul (hC a)
  unfold F
  exact (((((((((((((((((((((((hm1 0
    |>.add (hm4 _ 0 1 3 4))
    |>.add (hm3a _ 0 1 5))
    |>.add (hm4 _ 0 2 3 5))
    |>.add (hm3a _ 0 2 4))
    |>.add (hm3b _ 0 4 5))
    |>.add (hm3c _ 0 4 5))
    |>.add (hm13 _ 0 1 3 4))
    |>.add (hm132 _ 0 1 5))
    |>.add (hm13 _ 0 2 3 5))
    |>.add (hm132 _ 0 2 4))
    |>.add (hm1 1))
    |>.add (hm3a _ 1 2 3))
    |>.add (hm4 _ 1 2 4 5))
    |>.add (hm3b _ 1 3 5))
    |>.add (hm3c _ 1 3 5))
    |>.add (hm132 _ 1 2 3))
    |>.add (hm13 _ 1 2 4 5))
    |>.add (hm1 2))
    |>.add (hm3b _ 2 3 4))
    |>.add (hm3c _ 2 3 4))
    |>.add (hm1 3))
    |>.add (hm1 4))
    |>.add (hm1 5))

private lemma transpositionSource_hom : transpositionSource.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 6) ℂ
  have hC := isHomogeneous_C (Fin 6) (R := ℂ)
  unfold transpositionSource
  have t1 : (X 0 ^ 3 * X 3 ^ 3 : AmbientPoly 5).IsHomogeneous 6 := ((hX 0).pow 3).mul ((hX 3).pow 3)
  have t2 : (X 1 ^ 3 * X 4 ^ 3 : AmbientPoly 5).IsHomogeneous 6 := ((hX 1).pow 3).mul ((hX 4).pow 3)
  have t3 : (C 2 * X 2 ^ 3 * X 5 ^ 3 : AmbientPoly 5).IsHomogeneous 6 :=
    (((hC 2).mul ((hX 2).pow 3)).mul ((hX 5).pow 3))
  exact (t1.add t2).sub t3

private lemma pullback_F : affinePullback F = squareLift diagWeighted := by
  apply MvPolynomial.funext
  intro x
  simp [affinePullback, squareLift, F, diagWeighted, diagEll, diagB, diagC, diagD, eval_X, eval_C]
  ring

private lemma pullback_transpositionSource :
    affinePullback transpositionSource = squareLift diagSource := by
  apply MvPolynomial.funext
  intro x
  simp [affinePullback, squareLift, transpositionSource, diagSource, eval_X, eval_C]
  ring

private lemma normalPoint_zero : eval normalPoint (squareLift diagWeighted) = 0 := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  have hi4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  simp [diagWeighted, diagEll, diagB, diagC, diagD, squareLift, normalPoint, eval_X, eval_C]
  norm_num [hi2, hi4, hi6]

private lemma normalPoint_fu_ne_zero :
    eval normalPoint (squareLift (pderiv 4 diagWeighted)) ≠ 0 := by
  have hi4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hel4 : pderiv 4 diagEll = 0 := by simp [diagEll, Derivation.leibniz, Derivation.leibniz_pow]
  have hb4 : pderiv 4 diagB = 0 := by simp [diagB, Derivation.leibniz, Derivation.leibniz_pow]
  have hc4 : pderiv 4 diagC = 0 := by simp [diagC, Derivation.leibniz, Derivation.leibniz_pow]
  have hd4 : pderiv 4 diagD = 0 := by simp [diagD, Derivation.leibniz, Derivation.leibniz_pow]
  have hfu : pderiv 4 diagWeighted = 3 * diagEll * X 4 ^ 2 + 2 * diagB * X 4 + diagC := by
    unfold diagWeighted
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self,
      hel4, hb4, hc4, hd4, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      zero_mul, zero_add, add_zero, mul_one]
    ring
  rw [hfu]
  simp [diagEll, diagB, diagC, squareLift, normalPoint, eval_X, eval_C]
  norm_num [hi2, hi4]

end DiagQuotientSketch

theorem solution :
    HodgeComputer.HasCertificate
      HodgeComputer.DiagonalPermutation.F
      HodgeComputer.DiagonalPermutation.transpositionSource 6 1 :=
  HodgeComputer.ReflectionChart.certificate_of_relative_primitive _ _ _ _
    DiagQuotientSketch.F_hom DiagQuotientSketch.transpositionSource_hom
    HodgeComputer.DiagonalPermutation.chart_and_target_irreducible.1
    HodgeComputer.DiagonalPermutation.chart_and_target_irreducible.2
    DiagQuotientSketch.pullback_F DiagQuotientSketch.pullback_transpositionSource
    DiagQuotientSketch.normalPoint_zero DiagQuotientSketch.normalPoint_fu_ne_zero
    HodgeComputer.DiagonalPermutation.relative_primitive_exists
