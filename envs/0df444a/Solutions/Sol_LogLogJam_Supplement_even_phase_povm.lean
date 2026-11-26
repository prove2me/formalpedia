-- Prove2me | solution 1 for LogLogJam.Supplement.even_phase_povm
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:28:47.368821+00:00
-- url     : https://prove2.me/submissions/74fa256a-0561-413c-8ea8-1c2c9d5ea3f3

import Mathlib
import Theorems.Thm_BosonicLearn_fockPOVM_of_effect
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open MeasureTheory BosonicLearn
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Classical ComplexConjugate

private theorem orthogonal_readout {I X : Type} [DecidableEq I] [MeasurableSpace X]
    (ν : Measure X) (u : I → X → ℂ)
    (hi : ∀ i j, Integrable (fun x => conj (u i x) * u j x) ν)
    (ho : ∀ i j, ∫ x, conj (u i x) * u j x ∂ν = (1 : Matrix I I ℂ) i j) :
    ∃ M : FockPOVM I X, ∀ B : Set X, ∀ i j,
      M.effect B i j = ∫ x in B, conj (u i x) * u j x ∂ν := by
  classical
  let E := fun (B : Set X) (i j : I) => ∫ x in B, conj (u i x) * u j x ∂ν
  have hfull : E Set.univ = (1 : Matrix I I ℂ) := by
    ext i j
    simpa only [E, Measure.restrict_univ] using ho i j
  have hf (B : Set X) (s : Finset I) (z : I → ℂ) :
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j) =
        ((∫ x in B, ‖∑ i ∈ s, z i * u i x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    let F := fun (i j : I) (x : X) => conj (z i) * (conj (u i x) * u j x) * z j
    have hiF (i j : I) : Integrable (F i j) ν :=
      ((hi i j).const_mul _).mul_const _
    have hp (x : X) : (∑ i ∈ s, ∑ j ∈ s, F i j x) = ((‖∑ i ∈ s, z i * u i x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← Complex.conj_mul']
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [F]
      ring
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, ∫ x in B, F i j x ∂ν := by
        simp only [F, E, integral_mul_const, integral_const_mul, Complex.star_def]
      _ = ∫ x in B, ∑ i ∈ s, ∑ j ∈ s, F i j x ∂ν := by
        rw [integral_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => (hiF i j).integrableOn))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum s (fun j _ => (hiF i j).integrableOn)]
      _ = _ := by simp_rw [hp]; exact integral_ofReal
  obtain ⟨M, hm⟩ := fockPOVM_of_effect E (by
    intro B hB s z
    rw [hf]
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
    refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
    have hplus (i j : I) : E B i j + E Bᶜ i j = E Set.univ i j := by
      simpa only [E, Measure.restrict_univ] using integral_add_compl hB (hi i j)
    have hadd : (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j) +
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E Bᶜ i j * z j) =
        ∑ i ∈ s, ∑ j ∈ s, star (z i) * E Set.univ i j * z j := by
      simp only [← Finset.sum_add_distrib, ← add_mul, ← mul_add, hplus]
    have hone : (∑ i ∈ s, ∑ j ∈ s, star (z i) * E Set.univ i j * z j) =
        ((∑ i ∈ s, ‖z i‖^2 : ℝ) : ℂ) := by
      rw [hfull, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      rw [Finset.sum_eq_single_of_mem i hi']
      · simp [Complex.conj_mul']
      · intro j _ hji
        simp [Ne.symm hji]
    rw [hone, hf, hf] at hadd
    have hsum := congrArg Complex.re hadd
    simp only [Complex.add_re, Complex.ofReal_re] at hsum
    exact le_of_le_of_eq (le_add_of_nonneg_right (integral_nonneg (fun x => sq_nonneg ‖∑ i ∈ s, z i * u i x‖))) hsum)
    hfull (fun i j f hm hd => hasSum_integral_iUnion hm hd (hi i j).integrableOn)
  exact ⟨M, fun B i j => congrFun (congrFun (congrFun hm B) i) j⟩




/-- A full single-copy POVM on the physical one-mode space whose even-sector
compression is exactly the canonical phase readout of Definition 8.17. -/
theorem solution :
    ∃ M : FockPOVM (Occupation (Fin 1)) ℝ,
      ∀ B : Set ℝ, MeasurableSet B → ∀ k l : ℕ,
      M.effect B (fun _ => 2*k) (fun _ => 2*l) =
        (∫ α in B ∩ Set.Ico 0 (2 * Real.pi),
          Complex.exp (Complex.I * (((k : ℝ) - l) * α))) / (2 * Real.pi : ℝ) := by
  classical
  let period := 2 * Real.pi
  have hp : 0 < period := by dsimp [period]; positivity
  let arc := Set.Ico 0 period
  let ν := ENNReal.ofReal period⁻¹ • (volume.restrict arc : Measure ℝ)
  let freq (i : Occupation (Fin 1)) := Equiv.intEquivNat.symm (i 0)
  have hinj : Function.Injective freq := by
    intro i j h
    have hv := Equiv.intEquivNat.symm.injective h
    funext t
    simpa [Subsingleton.elim t 0] using hv
  have heven (k : ℕ) : freq (fun _ => 2*k) = k := by
    apply Equiv.intEquivNat.injective
    change Equiv.intEquivNat (Equiv.intEquivNat.symm (2*k)) = Equiv.intEquivNat (k : ℤ)
    simp only [Equiv.apply_symm_apply]
    rfl
  let u (i : Occupation (Fin 1)) (x : ℝ) :=
    Complex.exp (-(freq i : ℂ) * Complex.I * (x : ℂ))
  have he (i j : Occupation (Fin 1)) (x : ℝ) :
      conj (u i x) * u j x = Complex.exp (((freq i - freq j : ℤ) : ℂ) * Complex.I * (x : ℂ)) := by
    dsimp [u]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    push_cast
    simp only [map_mul, map_neg, map_intCast, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    ring
  have hΔ (n : ℤ) :
      (∫ x in arc, Complex.exp ((n : ℂ) * Complex.I * (x : ℂ))) =
        if n = 0 then (period : ℂ) else 0 := by
    dsimp [arc]
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp.le]
    by_cases hn : n = 0
    · simp [hn]
    · have hcoef : (n : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
      rw [integral_exp_mul_complex hcoef, if_neg hn]
      have hperiod : (n : ℂ) * Complex.I * (period : ℂ) = n * (2 * Real.pi * Complex.I) := by
        dsimp [period]
        push_cast
        ring
      rw [hperiod, Complex.exp_int_mul_two_pi_mul_I]
      simp
  have hi (i j : Occupation (Fin 1)) : Integrable (fun x => conj (u i x) * u j x) ν := by
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    have hc : Continuous (fun x => conj (u i x) * u j x) := by dsimp [u]; fun_prop
    exact (hc.integrableOn_Icc (μ := volume) (a := 0) (b := period)).mono_set Set.Ico_subset_Icc_self
  have ho (i j : Occupation (Fin 1)) :
      (∫ x, conj (u i x) * u j x ∂ν) = (1 : Matrix _ _ ℂ) i j := by
    simp_rw [he]
    dsimp only [ν]
    rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le), hΔ, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp [Complex.real_smul, hp.ne']
    · have hn := sub_ne_zero.mpr (hinj.ne hij)
      simp [hij, hn]
  obtain ⟨M, hM⟩ := orthogonal_readout ν u hi ho
  refine ⟨M, ?_⟩
  intro B hB k l
  rw [hM]
  simp_rw [he, heven]
  dsimp only [ν, arc, period]
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le),
    Measure.restrict_restrict hB, Complex.real_smul]
  push_cast
  rw [div_eq_mul_inv, mul_comm]
  dsimp only [period]
  push_cast
  congr 1
  apply setIntegral_congr_fun (hB.inter measurableSet_Ico)
  intro x _
  push_cast
  ring_nf
