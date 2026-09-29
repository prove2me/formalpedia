-- Prove2me | solution 1 for NeutrinoDecoherence.vonNeumannEntropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T08:33:52.569551+00:00
-- url     : https://prove2.me/submissions/a0e85f1b-daf0-4c94-a789-2e40b8a7f7e7

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open scoped ComplexOrder

open Matrix in
theorem nd_trace_cfc {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  simp

theorem nd_negMulLog_eq_zero {x : ℝ} (hx : 0 ≤ x) : Real.negMulLog x = 0 ↔ x * x = x := by
  rw [Real.negMulLog, neg_mul, neg_eq_zero, mul_eq_zero, Real.log_eq_zero]
  constructor
  · rintro (h | h | h | h)
    · rw [h]; ring
    · rw [h]; ring
    · rw [h]; ring
    · linarith
  · intro h
    have : x * (x - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl (by linarith)))

open NeutrinoDecoherence Matrix in
theorem solution {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) :
    0 ≤ vonNeumannEntropy ρ ∧ vonNeumannEntropy ρ ≤ Real.log (Fintype.card n) ∧
      (vonNeumannEntropy ρ = 0 ↔ ρ * ρ = ρ) ∧
      (vonNeumannEntropy ρ = Real.log (Fintype.card n) ↔
        ρ = ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ)) := by
  obtain ⟨hpsd, htr⟩ := hρ
  have hH : ρ.IsHermitian := hpsd.1
  have hsa : IsSelfAdjoint ρ := hH.isSelfAdjoint
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hpsd.eigenvalues_nonneg
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have h := hH.trace_eq_sum_eigenvalues
    rw [htr] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum] at h2
    exact h2.symm
  have hsq : cfc (fun x : ℝ => x * x) ρ = ρ * ρ := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) ρ, cfc_id' (R := ℝ) (a := ρ)]
  have hid : cfc (fun x : ℝ => x) ρ = ρ := cfc_id' (R := ℝ) (a := ρ)
  have hle1 : ∀ i, hH.eigenvalues i ≤ 1 := fun i =>
    hsum ▸ Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hS : vonNeumannEntropy ρ = ∑ i, Real.negMulLog (hH.eigenvalues i) := by
    unfold vonNeumannEntropy
    rw [nd_trace_cfc ρ hH]
    simp only [Complex.re_sum, Complex.ofReal_re]
  have hterm : ∀ i, 0 ≤ Real.negMulLog (hH.eigenvalues i) :=
    fun i => Real.negMulLog_nonneg (hnn i) (hle1 i)
  have hne : Nonempty n := by
    rcases isEmpty_or_nonempty n with h | h
    · simp at hsum
    · exact h
  have hNpos : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card n : ℝ) with hN
  have hw : ∀ i ∈ (Finset.univ : Finset n), (0 : ℝ) < N⁻¹ := fun _ _ => inv_pos.mpr hNpos
  have hw1 : ∑ _i ∈ (Finset.univ : Finset n), N⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
    field_simp
  have hmem : ∀ i ∈ (Finset.univ : Finset n), hH.eigenvalues i ∈ Set.Ici (0 : ℝ) :=
    fun i _ => Set.mem_Ici.mpr (hnn i)
  have hcenter : Real.negMulLog (∑ i, N⁻¹ • hH.eigenvalues i) = N⁻¹ * Real.log N := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
    rw [Real.negMulLog, Real.log_inv]
    ring
  have hJ := Real.concaveOn_negMulLog.le_map_sum (fun i hi => (hw i hi).le) hw1 hmem
  have hconst : ∀ c : ℝ, ρ = ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ) ↔ ∀ i, hH.eigenvalues i = c := by
    intro c
    have hc1 : ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ) = cfc (fun _ : ℝ => c) ρ := by
      rw [cfc_const c ρ, Algebra.algebraMap_eq_smul_one]
      ext i j
      simp [Matrix.one_apply]
    rw [hc1]
    constructor
    · intro h i
      have h' : cfc (fun x : ℝ => x) ρ = cfc (fun _ : ℝ => c) ρ := by rw [hid]; exact h
      have h2 := eqOn_of_cfc_eq_cfc h'
      rw [hH.spectrum_real_eq_range_eigenvalues] at h2
      exact h2 ⟨i, rfl⟩
    · intro h
      calc ρ = cfc (fun x : ℝ => x) ρ := hid.symm
        _ = cfc (fun _ : ℝ => c) ρ := cfc_congr (by
          rw [hH.spectrum_real_eq_range_eigenvalues]
          rintro _ ⟨i, rfl⟩
          exact h i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS]
    exact Finset.sum_nonneg (fun i _ => hterm i)
  · rw [hcenter] at hJ
    simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
    rw [hS]
    have := (mul_le_mul_iff_of_pos_left (inv_pos.mpr hNpos)).mp hJ
    exact this
  · rw [hS, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)]
    constructor
    · intro h
      rw [← hsq]
      conv_rhs => rw [← hid]
      apply cfc_congr
      rw [hH.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      exact (nd_negMulLog_eq_zero (hnn i)).mp (h i (Finset.mem_univ _))
    · intro h i _
      rw [← hsq] at h
      conv_rhs at h => rw [← hid]
      have h2 := eqOn_of_cfc_eq_cfc h
      rw [hH.spectrum_real_eq_range_eigenvalues] at h2
      exact (nd_negMulLog_eq_zero (hnn i)).mpr (h2 ⟨i, rfl⟩)
  · have hcast : ((Fintype.card n : ℂ)⁻¹) = (((N⁻¹ : ℝ)) : ℂ) := by
      rw [hN]; push_cast; rfl
    rw [hcast, hconst]
    constructor
    · intro hSeq
      have heq := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff_of_pos hw hw1 hmem).mp (by
        rw [hcenter]
        simp only [smul_eq_mul, ← Finset.mul_sum]
        rw [← hS, hSeq])
      intro i
      have hall : ∀ j, hH.eigenvalues j = hH.eigenvalues i :=
        fun j => heq (Finset.mem_univ j) (Finset.mem_univ i)
      have h1 : ∑ j, hH.eigenvalues j = N * hH.eigenvalues i := by
        simp only [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
      rw [hsum] at h1
      field_simp
      linarith
    · intro h
      rw [hS]
      simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
      rw [Real.negMulLog, Real.log_inv]
      field_simp
