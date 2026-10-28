-- Prove2me | solution 1 for NCLpModules.Principal.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:15:21.27174+00:00
-- url     : https://prove2.me/submissions/a2cf28fb-ea96-413b-a2ef-33fcdc96a4ef

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

open scoped Matrix ComplexOrder

namespace Aux_NCLpModules_Principal_lemma_1_2

lemma closedM {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    IsClosed (M : Set (Matrix (Fin n) (Fin n) ℂ)) :=
  Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule M.toSubalgebra)

lemma cfcM {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (D : Matrix (Fin n) (Fin n) ℂ) (hDM : D ∈ M) (f : ℝ → ℝ) : cfc f D ∈ M := by
  haveI := closedM M
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) f hDM

open scoped MatrixOrder in
lemma spec_nonneg {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.PosSemidef) :
    ∀ t ∈ spectrum ℝ D, 0 ≤ t := by
  intro t ht
  exact spectrum_nonneg_of_nonneg hD.nonneg ht

end Aux_NCLpModules_Principal_lemma_1_2

open Aux_NCLpModules_Principal_lemma_1_2 in
open NCLpModules.Principal in
theorem solution {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {p : ℝ} (hp : 0 < p)
    (D : Matrix (Fin n) (Fin n) ℂ) (hDM : D ∈ M) (hD : D.PosSemidef) :
    {z | ∃ x ∈ M, z = x * cfc (fun t : ℝ => t ^ (1 / p)) D} =
        {z | ∃ y ∈ M, z = y * supportProj D} ∧
      {z | ∃ x ∈ M, z = cfc (fun t : ℝ => t ^ (1 / p)) D * x} =
        {z | ∃ y ∈ M, z = supportProj D * y} := by
  set F := cfc (fun t : ℝ => t ^ (1 / p)) D with hF
  set s := supportProj D with hs
  set g := cfc (fun t : ℝ => if t = 0 then (0 : ℝ) else t ^ (-(1 / p))) D with hg
  have hfin : (spectrum ℝ D).Finite := Matrix.finite_real_spectrum
  have hp' : (1 / p) ≠ 0 := by positivity
  have hnn := spec_nonneg D hD
  have hFs : F * s = F := by
    rw [hF, hs, supportProj, ← cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)]
    apply cfc_congr
    intro t _
    by_cases h0 : t = 0
    · simp only [h0, if_true, mul_zero, Real.zero_rpow hp']
    · simp only [h0, if_false, mul_one]
  have hsF : s * F = F := by
    rw [hF, hs, supportProj, ← cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)]
    apply cfc_congr
    intro t _
    by_cases h0 : t = 0
    · simp only [h0, if_true, zero_mul, Real.zero_rpow hp']
    · simp only [h0, if_false, one_mul]
  have hFg : F * g = s := by
    rw [hF, hg, hs, supportProj, ← cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)]
    apply cfc_congr
    intro t ht
    by_cases h0 : t = 0
    · simp only [h0, if_true, mul_zero]
    · simp only [h0, if_false]
      have htpos : 0 < t := lt_of_le_of_ne (hnn t ht) (Ne.symm h0)
      rw [← Real.rpow_add htpos, add_neg_cancel, Real.rpow_zero]
  have hgF : g * F = s := by
    rw [hF, hg, hs, supportProj, ← cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)]
    apply cfc_congr
    intro t ht
    by_cases h0 : t = 0
    · simp only [h0, if_true, zero_mul]
    · simp only [h0, if_false]
      have htpos : 0 < t := lt_of_le_of_ne (hnn t ht) (Ne.symm h0)
      rw [← Real.rpow_add htpos, neg_add_cancel, Real.rpow_zero]
  have hFM : F ∈ M := cfcM M D hDM _
  have hgM : g ∈ M := cfcM M D hDM _
  constructor
  · ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x * F, M.mul_mem hx hFM, by rw [mul_assoc, hFs]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * g, M.mul_mem hy hgM, by rw [mul_assoc, hgF]⟩
  · ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨F * x, M.mul_mem hFM hx, by rw [← mul_assoc, hsF]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y, M.mul_mem hgM hy, by rw [← mul_assoc, hFg]⟩
