-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.range_ratioU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:08:09.734613+00:00
-- url     : https://prove2.me/submissions/aa65cb28-40a1-4d5a-a5e7-2d89650084d5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_nontrivial_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_isUnit_of_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_ratioU_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_normU_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_tauU_tauU
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_ratioU_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_mem_ker_normU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution (h : ResAlg E τ q ε) (hf : IsField E) :
    (ratioU τ).range = (normU τ).ker := by
  have := nontrivial_of_resAlg h
  ext k
  constructor
  · intro hk
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hk
    rw [MonoidHom.mem_ker, normU_apply, ratioU_apply, map_div, tauU_tauU h]
    simp [div_eq_mul_inv, mul_assoc]
  · intro hk
    rw [mem_ker_normU] at hk
    obtain ⟨u, hu, -⟩ := h.basis
    have key : ∀ x : E, x + k * τ x = k * τ (x + k * τ x) := by
      intro x
      rw [map_add, map_mul, h.inv]
      linear_combination (-x) * hk
    have hx : ∃ x : E, x + k * τ x ≠ 0 := by
      by_contra hc
      push Not at hc
      have h1 := hc 1
      have h2 := hc u
      rw [map_one, mul_one] at h1
      apply hu.ne_zero
      linear_combination h2 - τ u * h1
    obtain ⟨x, hx⟩ := hx
    exact MonoidHom.mem_range.2 ⟨(isUnit_of_ne hf hx).unit, ratioU_eq_iff.2 (key x)⟩
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
