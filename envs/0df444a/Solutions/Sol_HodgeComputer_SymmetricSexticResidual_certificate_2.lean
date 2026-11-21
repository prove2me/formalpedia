-- Prove2me | solution 2 for HodgeComputer.SymmetricSexticResidual.certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T05:01:46.954579+00:00
-- url     : https://prove2.me/submissions/c763cf9d-67b7-4e66-bfdb-87d7c4012036
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_ReflectionChart_certificate_of_relative_primitive
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_chart_and_target_irreducible
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_relative_primitive_exists
import Definitions.Def_HodgeComputerSymmetricChart
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace SymRootSketch
open MvPolynomial HodgeComputer HodgeComputer.SymmetricSexticResidual HodgeComputer.ReflectionChart

private def QX : AmbientPoly 5 := X 0 * X 1 + X 0 * X 2 + X 1 * X 2
private def QY : AmbientPoly 5 := X 3 * X 4 + X 3 * X 5 + X 4 * X 5
private def compactF : AmbientPoly 5 :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 +
    C (1 / 7 : ℂ) * (C 5 * QX ^ 2 * QY + C 10 * QX * QY ^ 2)

private lemma exactF_compact : F = compactF := by
  apply MvPolynomial.funext (σ := Fin 6)
  intro x
  simp [F, compactF, QX, QY]
  ring

private lemma F_hom : F.IsHomogeneous 6 := by
  rw [exactF_compact]
  have hX := isHomogeneous_X (σ := Fin 6) ℂ
  have hC := isHomogeneous_C (Fin 6) (R := ℂ)
  have hQX : QX.IsHomogeneous 2 :=
    (((hX 0).mul (hX 1)).add ((hX 0).mul (hX 2))).add ((hX 1).mul (hX 2))
  have hQY : QY.IsHomogeneous 2 :=
    (((hX 3).mul (hX 4)).add ((hX 3).mul (hX 5))).add ((hX 4).mul (hX 5))
  have hsum6 : (X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 : AmbientPoly 5).IsHomogeneous 6 :=
    ((((((hX 0).pow 6).add ((hX 1).pow 6)).add ((hX 2).pow 6)).add
      ((hX 3).pow 6)).add ((hX 4).pow 6)).add ((hX 5).pow 6)
  have hcross1 : (C 5 * QX ^ 2 * QY).IsHomogeneous 6 := by
    simpa using (((hC 5).mul (hQX.pow 2)).mul hQY)
  have hcross2 : (C 10 * QX * QY ^ 2).IsHomogeneous 6 := by
    simpa using (((hC 10).mul hQX).mul (hQY.pow 2))
  exact hsum6.add ((hC (1 / 7 : ℂ)).mul (hcross1.add hcross2))

private lemma A_hom : A.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 6) ℂ
  unfold A
  exact ((((((hX 0).mul (hX 1)).mul (hX 2)).mul (hX 3)).mul (hX 4)).mul (hX 5))

private lemma pullback_F : affinePullback F = squareLift symWeighted := by
  rw [exactF_compact]
  apply MvPolynomial.funext
  intro x
  simp [affinePullback, squareLift, compactF, QX, QY, symWeighted, leftQuadric, rightQuadric, eval_X, eval_C]
  ring

private lemma pullback_A : affinePullback A = squareLift symSource := by
  apply MvPolynomial.funext
  intro x
  simp [affinePullback, squareLift, A, symSource, eval_X, eval_C]
  ring

private lemma normalPoint_zero : eval normalPoint (squareLift symWeighted) = 0 := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  have hi4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  simp [symWeighted, leftQuadric, rightQuadric, squareLift, normalPoint, eval_X, eval_C]
  norm_num [hi2, hi4, hi6]

private lemma normalPoint_fu_ne_zero :
    eval normalPoint (squareLift (pderiv 4 symWeighted)) ≠ 0 := by
  have hi4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hcubic : symWeighted = symEll * X 4 ^ 3 + symB * X 4 ^ 2 + symC * X 4 + symD := by
    apply MvPolynomial.funext; intro x
    simp [symWeighted, leftQuadric, rightQuadric, symEll, symB, symC, symD, eval_X, eval_C]; ring
  have hel4 : pderiv 4 symEll = 0 := by simp [symEll, Derivation.leibniz, Derivation.leibniz_pow]
  have hb4 : pderiv 4 symB = 0 := by simp [symB, Derivation.leibniz, Derivation.leibniz_pow]
  have hc4 : pderiv 4 symC = 0 := by simp [symC, Derivation.leibniz, Derivation.leibniz_pow]
  have hd4 : pderiv 4 symD = 0 := by simp [symD, Derivation.leibniz, Derivation.leibniz_pow]
  have hfu : pderiv 4 symWeighted = 3 * symEll * X 4 ^ 2 + 2 * symB * X 4 + symC := by
    rw [hcubic]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self,
      hel4, hb4, hc4, hd4, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      zero_mul, zero_add, add_zero, mul_one]
    ring
  rw [hfu]
  simp [symEll, symB, symC, squareLift, normalPoint, eval_X, eval_C]
  norm_num [hi2, hi4]

end SymRootSketch

theorem solution :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.SymmetricSexticResidual.n)
      HodgeComputer.SymmetricSexticResidual.F
      HodgeComputer.SymmetricSexticResidual.A
      HodgeComputer.SymmetricSexticResidual.d
      HodgeComputer.SymmetricSexticResidual.q :=
  HodgeComputer.ReflectionChart.certificate_of_relative_primitive _ _ _ _
    SymRootSketch.F_hom SymRootSketch.A_hom
    HodgeComputer.SymmetricSexticResidual.chart_and_target_irreducible.1
    HodgeComputer.SymmetricSexticResidual.chart_and_target_irreducible.2
    SymRootSketch.pullback_F SymRootSketch.pullback_A
    SymRootSketch.normalPoint_zero SymRootSketch.normalPoint_fu_ne_zero
    HodgeComputer.SymmetricSexticResidual.relative_primitive_exists
