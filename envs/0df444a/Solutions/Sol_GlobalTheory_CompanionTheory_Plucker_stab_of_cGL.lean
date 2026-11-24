-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.stab_of_cGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:24:58.261459+00:00
-- url     : https://prove2.me/submissions/db93500c-0353-4c16-ba42-b6ff8890b33d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cmp_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_block_of_cmp
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_inv_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_mem_stab
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_map_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (A : Ad E R) (hi : Function.Injective A.i) {t₀ : Sub ι m} {γ : GL ι R} (hγ : γ ∈ A.ratGL ι)
    (h : cGL m γ ∈ stab R ({t₀} : Set (Sub ι m))) : γ ∈ stab R (t₀.1 : Set ι) := by
  obtain ⟨δ, rfl⟩ := hγ
  have key : ∀ δ : GL ι E, (∀ t, t ≠ t₀ → cmp ((Matrix.GeneralLinearGroup.map A.i δ : GL ι R) : Matrix ι ι R) t t₀ = 0) →
      ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι),
        ((Matrix.GeneralLinearGroup.map A.i δ : GL ι R) : Matrix ι ι R) r c = 0 := by
    intro δ h0 r hr c hc
    have h1 : (δ : Matrix ι ι E) r c = 0 := by
      refine block_of_cmp (δ : Matrix ι ι E) t₀ (Matrix.isUnits_det_units (cGL m δ)) (fun t ht => ?_) r hr c hc
      have h2 := h0 t ht
      rw [map_coe, cmp_map, Matrix.map_apply] at h2
      exact hi (by rw [h2, map_zero])
    rw [map_coe, Matrix.map_apply, h1, map_zero]
  rw [mem_stab] at h ⊢
  intro r hr c hc
  refine ⟨key δ (fun t ht => (h t ht t₀ rfl).1) r hr c hc, ?_⟩
  rw [← map_inv]
  refine key δ⁻¹ (fun t ht => ?_) r hr c hc
  have h3 := (h t ht t₀ rfl).2
  rw [cGL_inv_coe, ← map_inv] at h3
  exact h3
end GlobalTheory.CompanionTheory.Plucker
