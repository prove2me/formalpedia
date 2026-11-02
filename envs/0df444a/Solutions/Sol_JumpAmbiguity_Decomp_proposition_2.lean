-- Prove2me | solution 1 for JumpAmbiguity.Decomp.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:39:34.84271+00:00
-- url     : https://prove2.me/submissions/dc08b19d-18e6-43c8-b29e-db7d478e1237

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model
import Theorems.Thm_JumpAmbiguity_Decomp_separation_A8
import Theorems.Thm_JumpAmbiguity_Decomp_diffusion_A9
import Theorems.Thm_JumpAmbiguity_Decomp_decomposition_15
import Theorems.Thm_JumpAmbiguity_Decomp_jump_exposure

namespace JumpAmbiguity.Decomp
open Matrix

lemma pihat_inv {m n : ℕ} (M : Market m n) (hS : M.Standing) (v : Fin m → ℝ) :
    M.pihat ((M.Sig.transpose)⁻¹ *ᵥ v) = v := by
  have hT : IsUnit M.Sig.transpose.det := by rw [det_transpose]; exact hS.2.1
  rw [Market.pihat, mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, one_mulVec]

lemma inv_pihat {m n : ℕ} (M : Market m n) (hS : M.Standing) (π : Fin m → ℝ) :
    (M.Sig.transpose)⁻¹ *ᵥ M.pihat π = π := by
  have hT : IsUnit M.Sig.transpose.det := by rw [det_transpose]; exact hS.2.1
  rw [Market.pihat, mulVec_mulVec, Matrix.nonsing_inv_mul _ hT, one_mulVec]

/-- Building a portfolio from a column-space part `w` and an orthogonal part `z`. -/
lemma build {m n : ℕ} (M : Market m n) (hS : M.Standing) (w z : Fin m → ℝ)
    (hw : w ∈ M.K) (hz : M.IsOrthogonalToK z) :
    M.pibar ((M.Sig.transpose)⁻¹ *ᵥ (w + z)) = w ∧
    M.piperp ((M.Sig.transpose)⁻¹ *ᵥ (w + z)) = z := by
  have h := ((decomposition_15 M hS).2 (w + z)).2.2.2 w z hw hz rfl
  unfold Market.piperp Market.pibar
  rw [pihat_inv M hS]
  exact ⟨h.1.symm, h.2.symm⟩

lemma adm_iff {m n : ℕ} (M : Market m n) (hS : M.Standing) (π : Fin m → ℝ) :
    π ∈ M.Admissible ↔ M.pibar π ∈ M.ReducedAdmissible := by
  have hK : M.pibar π ∈ M.K := ((decomposition_15 M hS).2 (M.pihat π)).1
  simp only [Market.Admissible, Market.ReducedAdmissible, Set.mem_ofPred_eq,
    jump_exposure M hS π]
  exact ⟨fun h => ⟨hK, h⟩, fun h => h.2⟩

theorem proposition_2_aux {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (π : Fin m → ℝ) :
    (π ∈ M.Admissible ∧ ∀ π' ∈ M.Admissible, M.generator π' ≤ M.generator π) ↔
      ∃ pibar : Fin m → ℝ,
        (pibar ∈ M.ReducedAdmissible ∧
          ∀ x ∈ M.ReducedAdmissible, M.reducedObj x ≤ M.reducedObj pibar) ∧
        π = Matrix.mulVec ((M.Sig.transpose)⁻¹)
          (pibar + (1 / M.γ) • M.muperp) := by
  obtain ⟨hstar, hA9⟩ := diffusion_A9 M hS
  have hperp : ∀ π, M.IsOrthogonalToK (M.piperp π) := fun π =>
    ((decomposition_15 M hS).2 (M.pihat π)).2.1
  have hpi : ∀ π, M.pihat π = M.pibar π + M.piperp π := by
    intro π; simp only [Market.piperp]; abel
  constructor
  · rintro ⟨hπ, hmax⟩
    have hπR := (adm_iff M hS π).mp hπ
    have hG := separation_A8 M hS hI π hπ
    -- the diffusion part is optimal
    have hdiff : M.piperp π = (1 / M.γ) • M.muperp := by
      set π'' := (M.Sig.transpose)⁻¹ *ᵥ (M.pibar π + (1 / M.γ) • M.muperp)
      obtain ⟨hb, hp⟩ := build M hS _ _ hπR.1 hstar
      have hadm : π'' ∈ M.Admissible := by rw [adm_iff M hS, hb]; exact hπR
      have h1 := hmax π'' hadm
      rw [separation_A8 M hS hI π'' hadm, hb, hp, hG] at h1
      have h2 := (hA9 _ (hperp π)).1
      exact (hA9 _ (hperp π)).2 (by linarith)
    refine ⟨M.pibar π, ⟨hπR, fun x hx => ?_⟩, ?_⟩
    · set π' := (M.Sig.transpose)⁻¹ *ᵥ (x + M.piperp π)
      obtain ⟨hb, hp⟩ := build M hS _ _ hx.1 (hperp π)
      have hadm : π' ∈ M.Admissible := by rw [adm_iff M hS, hb]; exact hx
      have h1 := hmax π' hadm
      rw [separation_A8 M hS hI π' hadm, hb, hp, hG] at h1
      linarith
    · rw [← hdiff, ← hpi, inv_pihat M hS]
  · rintro ⟨pb, ⟨hpb, hopt⟩, rfl⟩
    obtain ⟨hb, hp⟩ := build M hS _ _ hpb.1 hstar
    have hadm : (M.Sig.transpose)⁻¹ *ᵥ (pb + (1 / M.γ) • M.muperp) ∈ M.Admissible := by
      rw [adm_iff M hS, hb]; exact hpb
    refine ⟨hadm, fun π' hπ' => ?_⟩
    rw [separation_A8 M hS hI π' hπ', separation_A8 M hS hI _ hadm, hb, hp]
    have h1 := hopt _ ((adm_iff M hS π').mp hπ')
    have h2 := (hA9 _ (hperp π')).1
    linarith

end JumpAmbiguity.Decomp

open JumpAmbiguity.Decomp

theorem solution {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (π : Fin m → ℝ) :
    (π ∈ M.Admissible ∧ ∀ π' ∈ M.Admissible, M.generator π' ≤ M.generator π) ↔
      ∃ pibar : Fin m → ℝ,
        (pibar ∈ M.ReducedAdmissible ∧
          ∀ x ∈ M.ReducedAdmissible, M.reducedObj x ≤ M.reducedObj pibar) ∧
        π = Matrix.mulVec ((M.Sig.transpose)⁻¹)
          (pibar + (1 / M.γ) • M.muperp) :=
  JumpAmbiguity.Decomp.proposition_2_aux M hS hI π
