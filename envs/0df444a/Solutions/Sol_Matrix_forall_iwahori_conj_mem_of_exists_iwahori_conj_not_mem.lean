-- Prove2me | solution 1 for Matrix.forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/069c4308-1e4b-55e5-a2d9-bbd1cfba7229

import Mathlib
import Theorems.Thm_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem

set_option autoImplicit false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField

namespace IwFlip

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "K" => v.adicCompletion ℚ
local notation "O" => v.adicCompletionIntegers ℚ

theorem intg_mul {M N : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) : ∀ i j, (M * N) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem intg_one : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) K) i j ∈ O := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem inv_unique {Y Yi R : Matrix (Fin 2) (Fin 2) K} (h2 : Yi * Y = 1) (hR : Y * R = 1) : Yi = R := by
  calc Yi = Yi * (Y * R) := by rw [hR, mul_one]
    _ = R := by rw [← mul_assoc, h2, one_mul]

theorem mul_fin_two (M N : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (M * N) i j = M i 0 * N 0 j + M i 1 * N 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

noncomputable abbrev ℓ (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)

theorem ℓ_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (ℓ w).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).2

theorem intCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) : (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (ℓ w : ℤ) ∣ z := by
  rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_intCast,
    ← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, Int.cast_id]
  rfl

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ w.asIdeal ↔ ℓ w ∣ n := by
  rw [show (n : 𝓞 ℚ) = ((n : ℤ) : 𝓞 ℚ) from (Int.cast_natCast n).symm, intCast_mem_asIdeal_iff, Int.natCast_dvd_natCast]

theorem ℓ_eq_of_prime_mem (w : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) : ℓ w = p :=
  (Nat.prime_dvd_prime_iff_eq (ℓ_prime w) hp).mp ((natCast_mem_asIdeal_iff w p).mp hpw)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) q) = w.valuation ℚ q := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q

theorem valuation_natCast_lt_one_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : w.valuation ℚ (n : ℚ) < 1 ↔ ℓ w ∣ n := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_dvd,
    Ideal.dvd_span_singleton, natCast_mem_asIdeal_iff]

theorem valuation_natCast_le_one (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : w.valuation ℚ (n : ℚ) ≤ 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem v_natCast_lt_one (w : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    Valued.v ((p : ℕ) : w.adicCompletion ℚ) < 1 := by
  rw [← map_natCast (algebraMap ℚ (w.adicCompletion ℚ)), valued_algebraMap, valuation_natCast_lt_one_iff,
    ℓ_eq_of_prime_mem w hp hpw]

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← map_natCast (algebraMap ℚ (w.adicCompletion ℚ)),
    valued_algebraMap]
  exact valuation_natCast_le_one w n

section TwoByTwo
variable {v}
variable (p : ℕ)

theorem iw_mul {M N : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ i j, M i j ∈ O) (hM10 : (p : K)⁻¹ * M 1 0 ∈ O)
    (hN : ∀ i j, N i j ∈ O) (hN10 : (p : K)⁻¹ * N 1 0 ∈ O) :
    (∀ i j, (M * N) i j ∈ O) ∧ (p : K)⁻¹ * (M * N) 1 0 ∈ O := by
  refine ⟨intg_mul v hM hN, ?_⟩
  rw [mul_fin_two, show (p : K)⁻¹ * (M 1 0 * N 0 0 + M 1 1 * N 1 0) =
    ((p : K)⁻¹ * M 1 0) * N 0 0 + M 1 1 * ((p : K)⁻¹ * N 1 0) by ring]
  exact add_mem (mul_mem hM10 (hN 0 0)) (mul_mem (hM 1 1) hN10)

theorem conj_eq (a b c d : K) (M : Matrix (Fin 2) (Fin 2) K) :
    !![a, 0; 0, b] * M * !![c, 0; 0, d] =
      !![a * M 0 0 * c, a * M 0 1 * d; b * M 1 0 * c, b * M 1 1 * d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Fin.isValue, Fin.zero_eta, Fin.mk_one] <;> ring

theorem al_conj_eq (M : Matrix (Fin 2) (Fin 2) K) :
    !![(0 : K), 1; (p : K), 0] * M * !![(0 : K), (p : K)⁻¹; 1, 0] =
      !![M 1 1, M 1 0 * (p : K)⁻¹; (p : K) * M 0 1, (p : K) * M 0 0 * (p : K)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Fin.isValue, Fin.zero_eta, Fin.mk_one] <;> ring

theorem intg_of_entries {a b c d : K} (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O) (hd : d ∈ O) :
    ∀ i j, (!![a, b; c, d]) i j ∈ O := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem conj_intg (hp0 : (p : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ i j, M i j ∈ O) (hM10 : (p : K)⁻¹ * M 1 0 ∈ O) (hpO : (p : K) ∈ O) :
    ∀ i j, (!![(1 : K), 0; 0, (p : K)⁻¹] * M * !![(1 : K), 0; 0, (p : K)]) i j ∈ O := by
  rw [conj_eq]
  refine intg_of_entries ?_ ?_ ?_ ?_
  · simpa using hM 0 0
  · simpa using mul_mem (hM 0 1) hpO
  · simpa using hM10
  · rw [show (p : K)⁻¹ * M 1 1 * (p : K) = M 1 1 by field_simp]; exact hM 1 1

theorem al_conj_intg (hp0 : (p : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ i j, M i j ∈ O) (hM10 : (p : K)⁻¹ * M 1 0 ∈ O) (hpO : (p : K) ∈ O) :
    ∀ i j, (!![(0 : K), 1; (p : K), 0] * M * !![(0 : K), (p : K)⁻¹; 1, 0]) i j ∈ O := by
  rw [al_conj_eq]
  refine intg_of_entries (hM 1 1) ?_ (mul_mem hpO (hM 0 1)) ?_
  · rw [mul_comm]; exact hM10
  · rw [show (p : K) * M 0 0 * (p : K)⁻¹ = M 0 0 by field_simp]; exact hM 0 0

theorem det_intg {M : Matrix (Fin 2) (Fin 2) K} (hM : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem iw_inv {M Mi : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ i j, M i j ∈ O) (hM10 : (p : K)⁻¹ * M 1 0 ∈ O) (hMi : ∀ i j, Mi i j ∈ O)
    (h1 : M * Mi = 1) (h2 : Mi * M = 1) : (p : K)⁻¹ * Mi 1 0 ∈ O := by
  have hdet : M.det * Mi.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  have hdet0 : M.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet

  have hinv : Mi = M⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have hMi10 : Mi 1 0 = -(M.det⁻¹ * M 1 0) := by
    rw [hinv, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    simp
  have hdinv : M.det⁻¹ = Mi.det := (mul_eq_one_iff_inv_eq₀ hdet0).mp hdet
  rw [hMi10, hdinv, show (p : K)⁻¹ * -(Mi.det * M 1 0) = -(Mi.det * ((p : K)⁻¹ * M 1 0)) by ring]
  exact neg_mem (mul_mem (det_intg hMi) hM10)

end TwoByTwo

section TwoByTwo2
variable {v}

theorem diag_mul_diag (a b c d : K) : !![a, 0; 0, b] * !![c, 0; 0, d] = !![a * c, 0; 0, b * d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Fin.isValue, Fin.zero_eta, Fin.mk_one] <;> ring

theorem al_mul_al' (p : K) (hp0 : p ≠ 0) : !![(0 : K), 1; p, 0] * !![(0 : K), p⁻¹; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, Fin.reduceNe]
    <;> simp [hp0]

theorem diag_one_one : !![(1 : K), 0; 0, 1] = 1 := by
  rw [← Matrix.one_fin_two]

theorem entry10 (a b c d : K) : (!![a, b; c, d]) 1 0 = c := by simp

theorem diagonal_eq (a b : K) : Matrix.diagonal ![a, b] = !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

end TwoByTwo2

end IwFlip

open IwFlip in
theorem solution
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hZ : ∃ Z : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Z i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Z 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Y * Z * Yi) i j ∈ v.adicCompletionIntegers ℚ) :
    ∀ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) →
      (p : v.adicCompletion ℚ)⁻¹ * X 1 0 ∈ v.adicCompletionIntegers ℚ →
      ∀ i j, (Yi * X * Y) i j ∈ v.adicCompletionIntegers ℚ := by
  intro X hXint hX10
  classical
  obtain ⟨Z, hZint, hZ10, hZbad⟩ := hZ
  have hp0 : (p : v.adicCompletion ℚ) ≠ 0 := by
    have : ((p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have h := (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr this
    rwa [map_natCast] at h
  have hpO : (p : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := natCast_mem_integers v p
  have hpinv : (p : v.adicCompletion ℚ)⁻¹ ∉ v.adicCompletionIntegers ℚ := by
    intro h
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
    have hlt : Valued.v (p : v.adicCompletion ℚ) < 1 := v_natCast_lt_one v hp hpv
    have hv0 : Valued.v (p : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp0
    exact absurd (one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv0, hlt⟩) (not_lt.mpr h)
  obtain ⟨hdet, htri⟩ := Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
    p hp v hpv Y Yi h1 h2 hY hY10 hpYi hpYi10 hYi hpY
  have hZiw : (∀ i j, Z i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Z 1 0 ∈ _ := ⟨hZint, hZ10⟩
  rcases htri with hT1 | hT2 | hAL
  ·
    exfalso
    obtain ⟨ι, ιi, ι', ι'i, hι, hιi, hι', hι'i, hιιi, hιiι, hι'ι'i, hι'iι', hι10, hι'10, hY⟩ := hT1
    apply hZbad
    have hι'i10 := iw_inv p hι' hι'10 hι'i hι'ι'i hι'iι'
    have hDDi : !![(p : v.adicCompletion ℚ), 0; 0, 1] * !![(p : v.adicCompletion ℚ)⁻¹, 0; 0, 1] = 1 := by
      rw [diag_mul_diag, mul_inv_cancel₀ hp0, mul_one, diag_one_one]
    have hYi : Yi = ι'i * !![(p : v.adicCompletion ℚ)⁻¹, 0; 0, 1] * ιi := IwFlip.inv_unique v h2 (by
      rw [hY]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ι' ι'i, hι'ι'i, Matrix.one_mul, ← Matrix.mul_assoc _ _ ιi, hDDi, Matrix.one_mul, hιιi])
    have hN := iw_mul p (iw_mul p hι' hι'10 hZint hZ10).1 (iw_mul p hι' hι'10 hZint hZ10).2 hι'i hι'i10
    have hmid : ∀ i j, (!![(p : v.adicCompletion ℚ), 0; 0, 1] * (ι' * Z * ι'i) *
        !![(p : v.adicCompletion ℚ)⁻¹, 0; 0, 1]) i j ∈ v.adicCompletionIntegers ℚ := by
      rw [conj_eq]
      refine intg_of_entries ?_ ?_ ?_ ?_
      · rw [show (p : v.adicCompletion ℚ) * (ι' * Z * ι'i) 0 0 * (p : v.adicCompletion ℚ)⁻¹ = (ι' * Z * ι'i) 0 0 by
          field_simp]; exact hN.1 0 0
      · rw [mul_one]; exact mul_mem hpO (hN.1 0 1)
      · rw [one_mul, mul_comm]; exact hN.2
      · rw [one_mul, mul_one]; exact hN.1 1 1
    have heq : Y * Z * Yi = ι * (!![(p : v.adicCompletion ℚ), 0; 0, 1] * (ι' * Z * ι'i) *
        !![(p : v.adicCompletion ℚ)⁻¹, 0; 0, 1]) * ιi := by
      rw [hY, hYi]; simp only [Matrix.mul_assoc]
    rw [heq]
    exact intg_mul v (intg_mul v hι hmid) hιi
  ·
    obtain ⟨ι, ιi, ι', ι'i, hι, hιi, hι', hι'i, hιιi, hιiι, hι'ι'i, hι'iι', hι10, hι'10, hY⟩ := hT2
    have hιi10 := iw_inv p hι hι10 hιi hιιi hιiι
    have hDDi : !![(1 : v.adicCompletion ℚ), 0; 0, (p : v.adicCompletion ℚ)] *
        !![(1 : v.adicCompletion ℚ), 0; 0, (p : v.adicCompletion ℚ)⁻¹] = 1 := by
      rw [diag_mul_diag, mul_inv_cancel₀ hp0, one_mul, diag_one_one]
    have hYi : Yi = ι'i * !![(1 : v.adicCompletion ℚ), 0; 0, (p : v.adicCompletion ℚ)⁻¹] * ιi := IwFlip.inv_unique v h2 (by
      rw [hY]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ι' ι'i, hι'ι'i, Matrix.one_mul, ← Matrix.mul_assoc _ _ ιi, hDDi, Matrix.one_mul, hιιi])
    have hN := iw_mul p (iw_mul p hιi hιi10 hXint hX10).1 (iw_mul p hιi hιi10 hXint hX10).2 hι hι10
    have hmid := conj_intg p hp0 hN.1 hN.2 hpO
    have heq : Yi * X * Y = ι'i * (!![(1 : v.adicCompletion ℚ), 0; 0, (p : v.adicCompletion ℚ)⁻¹] * (ιi * X * ι) *
        !![(1 : v.adicCompletion ℚ), 0; 0, (p : v.adicCompletion ℚ)]) * ι' := by
      rw [hY, hYi]; simp only [Matrix.mul_assoc]
    rw [heq]
    exact intg_mul v (intg_mul v hι'i hmid) hι'
  ·
    exfalso
    obtain ⟨κ, κi, hκ, hκi, hκκi, hκiκ, hκ10, hY⟩ := hAL
    apply hZbad
    have hκi10 := iw_inv p hκ hκ10 hκi hκκi hκiκ
    have hYi : Yi = κi * !![(0 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹; 1, 0] := IwFlip.inv_unique v h2 (by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc κ, hκκi, Matrix.one_mul, al_mul_al' _ hp0])
    have hN := iw_mul p (iw_mul p hκ hκ10 hZint hZ10).1 (iw_mul p hκ hκ10 hZint hZ10).2 hκi hκi10
    have heq : Y * Z * Yi = !![(0 : v.adicCompletion ℚ), 1; (p : v.adicCompletion ℚ), 0] * (κ * Z * κi) *
        !![(0 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹; 1, 0] := by
      rw [hY, hYi]; simp only [Matrix.mul_assoc]
    rw [heq]
    exact al_conj_intg p hp0 hN.1 hN.2 hpO

end S_Matrix_forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem
end P2MW
export P2MW.S_Matrix_forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem (solution)
