-- Prove2me | solution 2 for HodgeComputer.DiagonalPermutation.certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T05:01:48.209907+00:00
-- url     : https://prove2.me/submissions/52ac1c5a-5379-413b-8040-844d5f17d21b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_DiagonalPermutation_transposition_quotient_certificate
import Definitions.Def_HodgeComputerDiagonalPermutationQuotient
import Theorems.Thm_HodgeComputer_Verify_signed_coordinate_transport
import Theorems.Thm_HodgeComputer_HasCertificate_finite_linear_combination
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace DiagRootSketch
open MvPolynomial HodgeComputer HodgeComputer.DiagonalPermutation

private lemma F_hom : F.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 6) ℂ
  have hC := isHomogeneous_C (Fin 6) (R := ℂ)
  unfold F
  -- Every summand has total degree 6: check directly on monomial support!
  intro m hm
  revert m
  -- Even faster: prove by `IsHomogeneous` combinators or `eval`? Wait: `F` has 24 terms.
  -- Let's use a 4-line helper for monomial products!
  have hm1 (i : Fin 6) : ((X i : AmbientPoly 5) ^ 6).IsHomogeneous 6 := (hX i).pow 6
  have hm4 (a : ℂ) (i j k l : Fin 6) :
      ((((((5 : AmbientPoly 5) * X i ^ 3) * X j) * X k) * X l) * C a).IsHomogeneous 6 := by
    have h5 : (5 : AmbientPoly 5).IsHomogeneous 0 := by rw [← map_ofNat C 5]; exact hC _
    simpa using ((((h5.mul ((hX i).pow 3)).mul (hX j)).mul (hX k)).mul (hX l)).mul (hC a)
  have hm3a (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i ^ 3) * X j) * X k ^ 2) * C a).IsHomogeneous 6 := by
    have h5 : (5 : AmbientPoly 5).IsHomogeneous 0 := by rw [← map_ofNat C 5]; exact hC _
    simpa using (((h5.mul ((hX i).pow 3)).mul (hX j)).mul ((hX k).pow 2)).mul (hC a)
  have hm3b (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i ^ 2) * X j ^ 3) * X k) * C a).IsHomogeneous 6 := by
    have h5 : (5 : AmbientPoly 5).IsHomogeneous 0 := by rw [← map_ofNat C 5]; exact hC _
    simpa using (((h5.mul ((hX i).pow 2)).mul ((hX j).pow 3)).mul (hX k)).mul (hC a)
  have hm3c (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i ^ 2) * X j) * X k ^ 3) * C a).IsHomogeneous 6 := by
    have h5 : (5 : AmbientPoly 5).IsHomogeneous 0 := by rw [← map_ofNat C 5]; exact hC _
    simpa using (((h5.mul ((hX i).pow 2)).mul (hX j)).mul ((hX k).pow 3)).mul (hC a)
  have hm13 (a : ℂ) (i j k l : Fin 6) :
      ((((((5 : AmbientPoly 5) * X i) * X j ^ 3) * X k) * X l) * C a).IsHomogeneous 6 := by
    have h5 : (5 : AmbientPoly 5).IsHomogeneous 0 := by rw [← map_ofNat C 5]; exact hC _
    simpa using ((((h5.mul (hX i)).mul ((hX j).pow 3)).mul (hX k)).mul (hX l)).mul (hC a)
  have hm132 (a : ℂ) (i j k : Fin 6) :
      (((((5 : AmbientPoly 5) * X i) * X j ^ 3) * X k ^ 2) * C a).IsHomogeneous 6 := by
    have h5 : (5 : AmbientPoly 5).IsHomogeneous 0 := by rw [← map_ofNat C 5]; exact hC _
    simpa using (((h5.mul (hX i)).mul ((hX j).pow 3)).mul ((hX k).pow 2)).mul (hC a)
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

private lemma F_ne_zero : F ≠ 0 := by
  intro h
  have h' : (F : AmbientPoly 5) = (0 : AmbientPoly 5) := h
  have hev := congrArg (eval (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ)) h'
  simp [F] at hev

private def perm02 : Fin 6 ≃ Fin 6 where
  toFun := ![2, 1, 0, 5, 4, 3]
  invFun := ![2, 1, 0, 5, 4, 3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def perm12 : Fin 6 ≃ Fin 6 where
  toFun := ![0, 2, 1, 3, 5, 4]
  invFun := ![0, 2, 1, 3, 5, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private lemma id_eval₂ :
    eval₂Hom C (fun i : Fin 6 => C (1 : ℂ) * X i) = RingHom.id (AmbientPoly 5) := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro i; simp

private lemma cert_rename (e : Fin 6 ≃ Fin 6) (heF : rename e F = F) {Src : AmbientPoly 5}
    (h : HasCertificate F Src 6 1) : HasCertificate F (rename e Src) 6 1 := by
  obtain ⟨D, N, Q, hv⟩ := h
  have htr := HodgeComputer.Verify.signed_coordinate_transport e (fun _ => (1 : ℂ))
    (fun _ => by ring) hv
  dsimp only at htr
  rw [id_eval₂] at htr
  simp only [RingHom.id_apply, map_one, one_mul] at htr
  rw [heF] at htr
  exact ⟨rename e D, fun i => rename e (N (e.symm i)), rename e Q, htr⟩

private lemma rename_perm02_F : rename perm02 F = F := by
  apply MvPolynomial.funext (σ := Fin 6)
  intro x
  simp [F, perm02, eval_rename]
  ring

private lemma rename_perm12_F : rename perm12 F = F := by
  apply MvPolynomial.funext (σ := Fin 6)
  intro x
  simp [F, perm12, eval_rename]
  ring

private lemma linear_comb_sources :
    (C (1 / 3 : ℂ) * rename perm12 transpositionSource +
      C (-1 / 3 : ℂ) * rename perm02 transpositionSource : AmbientPoly 5) = A := by
  apply MvPolynomial.funext
  intro x
  simp [transpositionSource, A, perm12, perm02, eval_rename]
  ring

end DiagRootSketch

theorem solution :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.DiagonalPermutation.n)
      HodgeComputer.DiagonalPermutation.F
      HodgeComputer.DiagonalPermutation.A
      HodgeComputer.DiagonalPermutation.d
      HodgeComputer.DiagonalPermutation.q := by
  open DiagRootSketch MvPolynomial HodgeComputer HodgeComputer.DiagonalPermutation in
  have hB0 : HasCertificate F (rename perm02 transpositionSource) 6 1 :=
    cert_rename perm02 rename_perm02_F transposition_quotient_certificate
  have hB1 : HasCertificate F (rename perm12 transpositionSource) 6 1 :=
    cert_rename perm12 rename_perm12_F transposition_quotient_certificate
  let As : Fin 2 → AmbientPoly 5 := ![rename perm12 transpositionSource, rename perm02 transpositionSource]
  let cs : Fin 2 → ℂ := ![1 / 3, -1 / 3]
  have hcomb : HasCertificate F (∑ i : Fin 2, C (cs i) * As i) 6 1 :=
    HodgeComputer.HasCertificate.finite_linear_combination F F_ne_zero F_hom As cs
      (fun i => by fin_cases i; exact hB1; exact hB0)
  have hsum : (∑ i : Fin 2, C (cs i) * As i) = A := by
    simp only [Fin.sum_univ_two, As, cs, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact linear_comb_sources
  rw [hsum] at hcomb
  exact hcomb
