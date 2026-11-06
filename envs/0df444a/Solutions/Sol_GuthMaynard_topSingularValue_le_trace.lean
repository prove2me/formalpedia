-- Prove2me | solution 1 for GuthMaynard.topSingularValue_le_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T19:45:12.803963+00:00
-- url     : https://prove2.me/submissions/53bcc1fa-0ea2-4fc5-b591-b1daa23079ae

import Definitions.Def_GuthMaynard
import Mathlib

section
section
namespace GuthMaynardS4

theorem real42 (a S P m : ℝ) (hm : 1 ≤ m) (ha : 0 ≤ a) (haS : a ≤ S)
    (h1 : a ^ 3 + (S - a) ^ 3 / m ^ 2 ≤ P) (h2 : S ^ 3 / m ^ 2 ≤ P) :
    √a ≤ 2 * (P - S ^ 3 / m ^ 2) ^ (1 / 6 : ℝ) + 2 * (S / m) ^ (1 / 2 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hQ : 0 ≤ P - S ^ 3 / m ^ 2 := by linarith
  have hS : 0 ≤ S := le_trans ha haS
  have hu : 0 ≤ S / m := by positivity
  have hQp : 0 ≤ (P - S ^ 3 / m ^ 2) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hQ _
  have hup : 0 ≤ (S / m) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu _
  rw [← Real.sqrt_eq_rpow] at hup ⊢
  by_cases hc : a ≤ 4 * (S / m)
  · have : √a ≤ √(4 * (S / m)) := Real.sqrt_le_sqrt hc
    have h4 : √(4 * (S / m)) = 2 * √(S / m) := by
      rw [Real.sqrt_mul (by norm_num)]
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_eq_rpow] at hup
    nlinarith [Real.sqrt_eq_rpow (S / m)]
  · push_neg at hc
    set u := S / m with hudef
    have hSu : S = m * u := by rw [hudef]; field_simp
    -- (S - a)^3 ≥ S^3 - 3 a S^2
    have h3 : S ^ 3 - 3 * a * S ^ 2 ≤ (S - a) ^ 3 := by nlinarith [sq_nonneg a, mul_nonneg hS (sq_nonneg a), mul_nonneg ha (sq_nonneg a)]
    have h4 : a ^ 3 ≤ (P - S ^ 3 / m ^ 2) + 3 * a * u ^ 2 := by
      have : (S ^ 3 - 3 * a * S ^ 2) / m ^ 2 ≤ (S - a) ^ 3 / m ^ 2 :=
        div_le_div_of_nonneg_right h3 (by positivity)
      have e : (S ^ 3 - 3 * a * S ^ 2) / m ^ 2 = S ^ 3 / m ^ 2 - 3 * a * u ^ 2 := by
        rw [hSu]; field_simp
      linarith
    have hapos : 0 < a := by nlinarith
    have h5 : 3 * a * u ^ 2 ≤ a ^ 3 / 2 := by
      have : u ^ 2 ≤ a ^ 2 / 16 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this ha]
    have h6 : a ^ 3 ≤ 2 * (P - S ^ 3 / m ^ 2) := by linarith
    -- √a = (a^3)^(1/6)
    set Q := P - S ^ 3 / m ^ 2 with hQdef
    have h7 : √a ≤ (2 * Q) ^ (1 / 6 : ℝ) := by
      have : √a = (a ^ 3) ^ (1 / 6 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
      rw [this]
      exact Real.rpow_le_rpow (by positivity) h6 (by norm_num)
    have h8 : (2 * Q) ^ (1 / 6 : ℝ) ≤ 2 * Q ^ (1 / 6 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hQ]
      have : (2:ℝ) ^ (1 / 6 : ℝ) ≤ 2 := by
        calc (2:ℝ) ^ (1 / 6 : ℝ) ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := by norm_num
      exact mul_le_mul_of_nonneg_right this hQp
    linarith

end GuthMaynardS4

end
end

section
section
namespace GuthMaynardS4

open Module

theorem trace_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    B.trace.re = ∑ i, hB.eigenvalues i := by
  rw [hB.trace_eq_sum_eigenvalues]; simp [Complex.re_sum]

theorem trace_cube_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    (B ^ 3).trace.re = ∑ i, hB.eigenvalues i ^ 3 := by
  have h := hB.spectral_theorem
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have e : B ^ 3 = (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hB.eigenvectorUnitary) (D ^ 3) := by
    rw [map_pow, ← h]
  rw [e, Unitary.conjStarAlgAut_apply]
  have hu : star (hB.eigenvectorUnitary : Matrix ι ι ℂ) * (hB.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simp
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  have : D ^ 3 = Matrix.diagonal (fun i => ((hB.eigenvalues i ^ 3 : ℝ) : ℂ)) := by
    simp only [D, Matrix.diagonal_pow]
    congr 1; ext i; simp
  rw [this, Matrix.trace_diagonal]
  simp [Complex.re_sum, ← Complex.ofReal_pow]

end GuthMaynardS4

namespace GuthMaynardS4

open Module

theorem exists_eig {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (hB : (A * A.conjTranspose).IsHermitian)
    (hpos : 0 < GuthMaynard.topSingularValue A) :
    ∃ j, hB.eigenvalues j = GuthMaynard.topSingularValue A ^ 2 := by
  set T := Matrix.toEuclideanLin A with hT
  set a := GuthMaynard.topSingularValue A ^ 2 with ha
  have hapos : 0 < a := by positivity
  have hk : 0 < finrank ℂ (EuclideanSpace ℂ κ) := by
    by_contra h
    have h0 : finrank ℂ (EuclideanSpace ℂ κ) = 0 := by omega
    have := LinearMap.singularValues_of_finrank_le T (i := 0) (by omega)
    have h2 : GuthMaynard.topSingularValue A = 0 := this
    linarith
  have hev := LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues T (n := 0) hk
  have hev' : Module.End.HasEigenvalue (LinearMap.adjoint T ∘ₗ T) (a : ℂ) := by
    simpa [ha, GuthMaynard.topSingularValue, hT] using hev
  obtain ⟨v, hv⟩ := hev'.exists_hasEigenvector
  have hv1 : (LinearMap.adjoint T) (T v) = (a : ℂ) • v := by
    have := hv.apply_eq_smul
    simpa using this
  have hv0 : v ≠ 0 := hv.2
  have hw0 : T v ≠ 0 := by
    intro h
    rw [h, map_zero] at hv1
    have : (a : ℂ) • v = 0 := hv1.symm
    rcases smul_eq_zero.mp this with h' | h'
    · exact hapos.ne' (by exact_mod_cast h')
    · exact hv0 h'
  have hBT : Matrix.toEuclideanLin (A * A.conjTranspose) = T ∘ₗ LinearMap.adjoint T := by
    have h1 : Matrix.toEuclideanLin (A * A.conjTranspose) =
        Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin A.conjTranspose :=
      Matrix.toLpLin_mul_same 2 A A.conjTranspose
    rw [h1, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hev2 : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A * A.conjTranspose)) (a : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := T v) ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff, hBT]
    simp only [LinearMap.comp_apply]
    rw [hv1, map_smul]
  have hmem : (a : ℂ) ∈ spectrum ℂ (A * A.conjTranspose) := by
    rw [← Matrix.spectrum_toEuclideanLin]
    exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev2
  rw [hB.spectrum_eq_image_range] at hmem
  obtain ⟨x, ⟨j, rfl⟩, hx⟩ := hmem
  exact ⟨j, by simpa using hx⟩

end GuthMaynardS4

end
end

section
section
namespace GuthMaynardS4

open scoped ComplexOrder

theorem main42 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) :
    GuthMaynard.topSingularValue A ≤
      2 * (((A * A.conjTranspose) ^ 3).trace.re -
          (A * A.conjTranspose).trace.re ^ 3 / (Fintype.card ι : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
        2 * ((A * A.conjTranspose).trace.re / Fintype.card ι) ^ (1 / 2 : ℝ) := by
  have hB : (A * A.conjTranspose).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self A
  rw [trace_cube_sum _ hB, trace_sum _ hB]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hT : Matrix.toEuclideanLin A = 0 := by
      ext x i; exact (IsEmpty.false i).elim
    have : GuthMaynard.topSingularValue A = 0 := by
      unfold GuthMaynard.topSingularValue
      rw [hT]; simp
    simp [this]
  have hm : (1:ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr hι
  set lam := hB.eigenvalues with hlam
  have hnn : ∀ i, 0 ≤ lam i := fun i =>
    (Matrix.posSemidef_self_mul_conjTranspose A).eigenvalues_nonneg i
  have h2 : (∑ i, lam i) ^ 3 / (Fintype.card ι : ℝ) ^ 2 ≤ ∑ i, lam i ^ 3 := by
    have := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := lam) (fun i _ => hnn i) 2
    simpa using this
  have hs0 := GuthMaynard.topSingularValue A
  have hsnn : 0 ≤ GuthMaynard.topSingularValue A := by
    unfold GuthMaynard.topSingularValue; exact LinearMap.singularValues_nonneg _ _
  rcases hsnn.eq_or_lt with h0 | hpos
  · rw [← h0]
    have := real42 0 (∑ i, lam i) (∑ i, lam i ^ 3) (Fintype.card ι) hm le_rfl
      (Finset.sum_nonneg fun i _ => hnn i) (by simpa using h2) h2
    simpa using this
  · obtain ⟨j, hj⟩ := exists_eig A hB hpos
    have hsq : √(GuthMaynard.topSingularValue A ^ 2) = GuthMaynard.topSingularValue A :=
      Real.sqrt_sq hsnn
    rw [← hj] at hsq
    rw [← hsq]
    have hsplit : ∑ i, lam i = lam j + ∑ i ∈ Finset.univ.erase j, lam i := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hsplit3 : ∑ i, lam i ^ 3 = lam j ^ 3 + ∑ i ∈ Finset.univ.erase j, lam i ^ 3 := by
      exact (Finset.add_sum_erase _ (fun i => lam i ^ 3) (Finset.mem_univ j)).symm
    have hc : 0 ≤ ∑ i ∈ Finset.univ.erase j, lam i := Finset.sum_nonneg fun i _ => hnn i
    have hS : ∑ i, lam i - lam j = ∑ i ∈ Finset.univ.erase j, lam i := by linarith
    apply real42 (lam j) (∑ i, lam i) (∑ i, lam i ^ 3) (Fintype.card ι) hm (hnn j)
      (by linarith) _ h2
    rw [hS, hsplit3]
    have key : (∑ i ∈ Finset.univ.erase j, lam i) ^ 3 / (Fintype.card ι : ℝ) ^ 2 ≤
        ∑ i ∈ Finset.univ.erase j, lam i ^ 3 := by
      have hJ := pow_sum_div_card_le_sum_pow (s := Finset.univ.erase j) (f := lam)
        (fun i _ => hnn i) 2
      rcases (Finset.univ.erase j).eq_empty_or_nonempty with he | hne
      · rw [he]; simp
      · refine le_trans ?_ hJ
        have hcard : (1:ℝ) ≤ ((Finset.univ.erase j).card : ℝ) := by
          exact_mod_cast hne.card_pos
        have hle : ((Finset.univ.erase j).card : ℝ) ≤ Fintype.card ι := by
          have := Finset.card_erase_le (s := (Finset.univ : Finset ι)) (a := j)
          rw [Finset.card_univ] at this; exact_mod_cast this
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by linarith) hle 2
    linarith

end GuthMaynardS4

alias GuthMaynard.topSingularValue_le_trace_dev := GuthMaynardS4.main42

end
end

section
open GuthMaynard

theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) :
    topSingularValue A ≤
      2 * (((A * A.conjTranspose) ^ 3).trace.re -
          (A * A.conjTranspose).trace.re ^ 3 / (Fintype.card ι : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
        2 * ((A * A.conjTranspose).trace.re / Fintype.card ι) ^ (1 / 2 : ℝ) := by
  apply GuthMaynard.topSingularValue_le_trace_dev <;> assumption

end
