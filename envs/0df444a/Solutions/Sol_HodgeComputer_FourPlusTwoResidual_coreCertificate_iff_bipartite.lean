-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coreCertificate_iff_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:45.393166+00:00
-- url     : https://prove2.me/submissions/fd809a5d-2b1c-48ec-95e6-627acc29acf3

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open MvPolynomial
open scoped BigOperators
open HodgeComputer.FourPlusTwoResidual

namespace FP2Bipartite

private abbrev R4 := MvPolynomial (Fin 4) ℂ

private def sgnAB : Fin 4 → R4 := ![-1, -1, 1, 1]
private def eps : Fin 4 → R4 := ![1, 1, -1, -1]

private def coreDef (D : R4) (N : Fin 4 → R4) : R4 :=
  2 * coreSource * D ^ 2 - 2 * D * (∑ i, pderiv i core * N i) +
    3 * core * (D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i)

private lemma flipAB_C (c : ℂ) : flipAB (C c) = C c := by simp [flipAB]
private lemma flipAB_X0 : flipAB (X 0) = -X 0 := by simp [flipAB]
private lemma flipAB_X1 : flipAB (X 1) = -X 1 := by simp [flipAB]
private lemma flipAB_X2 : flipAB (X 2) = X 2 := by simp [flipAB]
private lemma flipAB_X3 : flipAB (X 3) = X 3 := by simp [flipAB]

private lemma flipCD_C (c : ℂ) : flipCD (C c) = C c := by simp [flipCD]
private lemma flipCD_X0 : flipCD (X 0) = X 0 := by simp [flipCD]
private lemma flipCD_X1 : flipCD (X 1) = X 1 := by simp [flipCD]
private lemma flipCD_X2 : flipCD (X 2) = -X 2 := by simp [flipCD]
private lemma flipCD_X3 : flipCD (X 3) = -X 3 := by simp [flipCD]

private lemma flipAB_involutive (p : R4) : flipAB (flipAB p) = p := by
  have hcomp : flipAB.comp flipAB = AlgHom.id ℂ R4 := by
    apply MvPolynomial.algHom_ext
    intro i; fin_cases i <;> simp [flipAB]
  exact AlgHom.congr_fun hcomp p

private lemma flipAB_core : flipAB core = core := by
  simp only [core, map_add, map_mul, map_pow, flipAB_C,
    flipAB_X0, flipAB_X1, flipAB_X2, flipAB_X3]
  ring

private lemma flipAB_coreSource : flipAB coreSource = -coreSource := by
  simp only [coreSource, map_mul, map_pow, flipAB_X0, flipAB_X2]
  ring

private lemma pderiv_flipAB (i : Fin 4) (p : R4) :
    pderiv i (flipAB p) = sgnAB i * flipAB (pderiv i p) := by
  induction p using MvPolynomial.induction_on generalizing i with
  | C c =>
    rw [flipAB_C, pderiv_C, map_zero, mul_zero]
  | add f g hf hg =>
    simp only [map_add, hf, hg]
    ring
  | mul_X f j hf =>
    rw [map_mul, pderiv_mul, pderiv_mul, map_add, map_mul, map_mul, hf]
    fin_cases i <;> fin_cases j <;>
      simp [sgnAB, flipAB_X0, flipAB_X1, flipAB_X2, flipAB_X3, pderiv_X] <;> ring

private lemma flipAB_pderiv_core0 : flipAB (pderiv 0 core) = -pderiv 0 core := by
  have h := congrArg (pderiv 0) flipAB_core
  rw [pderiv_flipAB] at h
  have hs0 : sgnAB 0 = -1 := rfl
  rw [hs0] at h
  linear_combination -h

private lemma flipAB_pderiv_core1 : flipAB (pderiv 1 core) = -pderiv 1 core := by
  have h := congrArg (pderiv 1) flipAB_core
  rw [pderiv_flipAB] at h
  have hs1 : sgnAB 1 = -1 := rfl
  rw [hs1] at h
  linear_combination -h

private lemma flipAB_pderiv_core2 : flipAB (pderiv 2 core) = pderiv 2 core := by
  have h := congrArg (pderiv 2) flipAB_core
  rw [pderiv_flipAB] at h
  have hs2 : sgnAB 2 = 1 := rfl
  rw [hs2, one_mul] at h
  exact h

private lemma flipAB_pderiv_core3 : flipAB (pderiv 3 core) = pderiv 3 core := by
  have h := congrArg (pderiv 3) flipAB_core
  rw [pderiv_flipAB] at h
  have hs3 : sgnAB 3 = 1 := rfl
  rw [hs3, one_mul] at h
  exact h

private lemma flipAB_isHomogeneous {p : R4} {n : ℕ} (hp : p.IsHomogeneous n) :
    (flipAB p).IsHomogeneous n := by
  rw [p.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro d hd
  have hdeg : d 0 + d 1 + d 2 + d 3 = n := by
    have h := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
  rw [monomial_eq, map_mul, flipAB_C]
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four,
    map_mul, map_pow, flipAB_X0, flipAB_X1, flipAB_X2, flipAB_X3]
  have h0 : ((-X (0 : Fin 4) : R4) ^ d 0).IsHomogeneous (1 * d 0) :=
    ((isHomogeneous_X ℂ (0 : Fin 4)).neg).pow (d 0)
  have h1 : ((-X (1 : Fin 4) : R4) ^ d 1).IsHomogeneous (1 * d 1) :=
    ((isHomogeneous_X ℂ (1 : Fin 4)).neg).pow (d 1)
  have h2 : ((X (2 : Fin 4) : R4) ^ d 2).IsHomogeneous (1 * d 2) :=
    (isHomogeneous_X ℂ (2 : Fin 4)).pow (d 2)
  have h3 : ((X (3 : Fin 4) : R4) ^ d 3).IsHomogeneous (1 * d 3) :=
    (isHomogeneous_X ℂ (3 : Fin 4)).pow (d 3)
  have hprod := (isHomogeneous_C (Fin 4) (coeff d p)).mul (((h0.mul h1).mul h2).mul h3)
  exact (show 0 + (1 * d 0 + 1 * d 1 + 1 * d 2 + 1 * d 3) = n by omega) ▸ hprod

private lemma flipAB_flipCD_even {p : R4} {m : ℕ} (hp : p.IsHomogeneous (2 * m)) :
    flipAB (flipCD p) = p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 + d 2 + d 3 = 2 * m := by
    have h := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
  rw [monomial_eq, map_mul, map_mul, flipCD_C, flipAB_C]
  congr 1
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four,
    map_mul, map_pow, map_neg, flipCD_X0, flipCD_X1, flipCD_X2, flipCD_X3,
    flipAB_X0, flipAB_X1, flipAB_X2, flipAB_X3]
  have hsign : (-1 : R4) ^ d 0 * (-1 : R4) ^ d 1 * (-1 : R4) ^ d 2 * (-1 : R4) ^ d 3 = 1 := by
    calc
      (-1 : R4) ^ d 0 * (-1 : R4) ^ d 1 * (-1 : R4) ^ d 2 * (-1 : R4) ^ d 3
          = (-1 : R4) ^ (d 0 + d 1 + d 2 + d 3) := by
            simp only [pow_add, mul_assoc]
      _ = ((-1 : R4) ^ 2) ^ m := by rw [hdeg, pow_mul]
      _ = 1 := by norm_num
  calc
    (-X 0) ^ d 0 * (-X 1) ^ d 1 * (-X 2) ^ d 2 * (-X 3) ^ d 3
        = ((-1 : R4) ^ d 0 * (-1 : R4) ^ d 1 * (-1 : R4) ^ d 2 * (-1 : R4) ^ d 3) *
            (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2 * X 3 ^ d 3) := by
          have neg_pow : ∀ (z : R4) (k : ℕ), (-z) ^ k = (-1 : R4) ^ k * z ^ k :=
            fun z k => neg_eq_neg_one_mul z ▸ mul_pow (-1) z k
          rw [neg_pow (X 0), neg_pow (X 1), neg_pow (X 2), neg_pow (X 3)]
          ring
    _ = X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2 * X 3 ^ d 3 := by rw [hsign, one_mul]

private lemma coreDef_flipAB (D : R4) (N : Fin 4 → R4) :
    coreDef (flipAB D) (fun i => eps i * flipAB (N i)) = -flipAB (coreDef D N) := by
  have hp0 : pderiv 0 (eps 0 * flipAB (N 0)) = -flipAB (pderiv 0 (N 0)) := by
    simpa [eps, sgnAB] using pderiv_flipAB 0 (N 0)
  have hp1 : pderiv 1 (eps 1 * flipAB (N 1)) = -flipAB (pderiv 1 (N 1)) := by
    simpa [eps, sgnAB] using pderiv_flipAB 1 (N 1)
  have hp2 : pderiv 2 (eps 2 * flipAB (N 2)) = -flipAB (pderiv 2 (N 2)) := by
    have h := pderiv_flipAB 2 (N 2)
    have he : eps 2 = -1 := rfl
    have hs : sgnAB 2 = 1 := rfl
    rw [he, neg_one_mul, map_neg, h, hs, one_mul]
  have hp3 : pderiv 3 (eps 3 * flipAB (N 3)) = -flipAB (pderiv 3 (N 3)) := by
    have h := pderiv_flipAB 3 (N 3)
    have he : eps 3 = -1 := rfl
    have hs : sgnAB 3 = 1 := rfl
    rw [he, neg_one_mul, map_neg, h, hs, one_mul]
  have hd0 : pderiv 0 (flipAB D) = -flipAB (pderiv 0 D) := by
    simpa [sgnAB] using pderiv_flipAB 0 D
  have hd1 : pderiv 1 (flipAB D) = -flipAB (pderiv 1 D) := by
    simpa [sgnAB] using pderiv_flipAB 1 D
  have hd2 : pderiv 2 (flipAB D) = flipAB (pderiv 2 D) := by
    simpa [sgnAB] using pderiv_flipAB 2 D
  have hd3 : pderiv 3 (flipAB D) = flipAB (pderiv 3 D) := by
    simpa [sgnAB] using pderiv_flipAB 3 D
  have he0 : eps 0 = 1 := rfl
  have he1 : eps 1 = 1 := rfl
  have he2 : eps 2 = -1 := rfl
  have he3 : eps 3 = -1 := rfl
  unfold coreDef
  simp only [Fin.sum_univ_four]
  rw [hp0, hp1, hp2, hp3, hd0, hd1, hd2, hd3]
  simp only [he0, he1, he2, he3, map_add, map_sub, map_mul, map_pow, map_ofNat,
    flipAB_core, flipAB_coreSource,
    flipAB_pderiv_core0, flipAB_pderiv_core1, flipAB_pderiv_core2, flipAB_pderiv_core3]
  ring

private lemma coreDef_combine (D1 D2 : R4) (N1 N2 : Fin 4 → R4) :
    coreDef (2 * D1 * D2) (fun i => D2 * N1 i + D1 * N2 i) =
      2 * D2 ^ 2 * coreDef D1 N1 + 2 * D1 ^ 2 * coreDef D2 N2 := by
  have hp2 : ∀ i : Fin 4, pderiv i (2 : R4) = 0 := fun i => by
    rw [← map_ofNat C 2, pderiv_C]
  unfold coreDef
  simp only [Fin.sum_univ_four, map_add, pderiv_mul, hp2]
  ring

end FP2Bipartite

theorem solution :
    (∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) ↔
    (∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.BipartiteCoreCertificate D N) := by
  constructor
  · rintro ⟨D, N, hD_ne, ⟨k, hD_hom, hN_hom⟩, hdef⟩
    let D' : MvPolynomial (Fin 4) ℂ := flipAB D
    let N' : Fin 4 → MvPolynomial (Fin 4) ℂ := fun i => FP2Bipartite.eps i * flipAB (N i)
    let Dhat : MvPolynomial (Fin 4) ℂ := 2 * D * D'
    let Nhat : Fin 4 → MvPolynomial (Fin 4) ℂ := fun i => D' * N i + D * N' i
    have hD'_ne : D' ≠ 0 := by
      intro h0
      have h0' : flipAB D = 0 := h0
      apply hD_ne
      rw [← FP2Bipartite.flipAB_involutive D, h0', map_zero]
    have h2_ne : (2 : MvPolynomial (Fin 4) ℂ) ≠ 0 := by
      rw [← map_ofNat C 2, Ne, C_eq_zero]; norm_num
    have hDhat_ne : Dhat ≠ 0 := mul_ne_zero (mul_ne_zero h2_ne hD_ne) hD'_ne
    have hD'_hom : D'.IsHomogeneous (k + 1) := FP2Bipartite.flipAB_isHomogeneous hD_hom
    have hDhat_hom : Dhat.IsHomogeneous (2 * k + 2) := by
      have h2 : (2 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 0 := by
        rw [← map_ofNat C 2]; exact isHomogeneous_C _ _
      have hmul := (h2.mul hD_hom).mul hD'_hom
      convert hmul using 1
      omega
    have hNhat_hom : ∀ i : Fin 4, (Nhat i).IsHomogeneous (2 * k + 3) := by
      intro i
      have hNi' : (flipAB (N i)).IsHomogeneous (k + 2) :=
        FP2Bipartite.flipAB_isHomogeneous (hN_hom i)
      have hN'i : (N' i).IsHomogeneous (k + 2) := by
        fin_cases i
        · change (1 * flipAB (N 0)).IsHomogeneous (k + 2); simpa using hNi'
        · change (1 * flipAB (N 1)).IsHomogeneous (k + 2); simpa using hNi'
        · change (-1 * flipAB (N 2)).IsHomogeneous (k + 2); simpa using hNi'.neg
        · change (-1 * flipAB (N 3)).IsHomogeneous (k + 2); simpa using hNi'.neg
      have h1 : (D' * N i).IsHomogeneous (2 * k + 3) := by
        convert hD'_hom.mul (hN_hom i) using 1; omega
      have h2 : (D * N' i).IsHomogeneous (2 * k + 3) := by
        convert hD_hom.mul hN'i using 1; omega
      exact h1.add h2
    have hflipAB_Dhat : flipAB Dhat = Dhat := by
      simp only [Dhat, D', map_mul, map_ofNat, FP2Bipartite.flipAB_involutive]
      ring
    have hflipCD_Dhat : flipCD Dhat = Dhat := by
      have heven : flipAB (flipCD Dhat) = Dhat :=
        FP2Bipartite.flipAB_flipCD_even (m := k + 1) (by convert hDhat_hom using 1; omega)
      calc
        flipCD Dhat = flipAB (flipAB (flipCD Dhat)) := (FP2Bipartite.flipAB_involutive _).symm
        _ = flipAB Dhat := by rw [heven]
        _ = Dhat := hflipAB_Dhat
    have he0 : FP2Bipartite.eps 0 = 1 := rfl
    have he1 : FP2Bipartite.eps 1 = 1 := rfl
    have he2 : FP2Bipartite.eps 2 = -1 := rfl
    have he3 : FP2Bipartite.eps 3 = -1 := rfl
    refine ⟨Dhat, Nhat, hDhat_ne, ⟨k, hDhat_hom, hNhat_hom⟩, hflipAB_Dhat, hflipCD_Dhat,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Nhat, D', N', he0, map_add, map_mul, map_one, FP2Bipartite.flipAB_involutive]; ring
    · simp only [Nhat, D', N', he1, map_add, map_mul, map_one, FP2Bipartite.flipAB_involutive]; ring
    · simp only [Nhat, D', N', he2, map_add, map_mul, map_neg, map_one,
        FP2Bipartite.flipAB_involutive]; ring
    · simp only [Nhat, D', N', he3, map_add, map_mul, map_neg, map_one,
        FP2Bipartite.flipAB_involutive]; ring
    · have hc1 : FP2Bipartite.coreDef D N = 0 := hdef
      have hc2 : FP2Bipartite.coreDef D' N' = 0 := by
        dsimp [D', N']
        rw [FP2Bipartite.coreDef_flipAB, hc1, map_zero, neg_zero]
      change FP2Bipartite.coreDef Dhat Nhat = 0
      dsimp [Dhat, Nhat]
      rw [FP2Bipartite.coreDef_combine, hc1, hc2]
      ring
  · rintro ⟨D, N, hD_ne, ⟨m, hD_hom, hN_hom⟩, -, -, -, -, -, -, hdef⟩
    refine ⟨D, N, hD_ne, ⟨2 * m + 1, ?_, ?_⟩, hdef⟩
    · convert hD_hom using 1
    · intro i; convert hN_hom i using 1
