-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nF_fromCols_sel_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:13.393976+00:00
-- url     : https://prove2.me/submissions/737cee5d-8ca4-4651-97cc-1e3866446231

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_minor_le_nF
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_le_of_minors
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_norm_det_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (s : κ → ι) (C : Matrix ι κ' K)
    (hs : Function.Injective s) (hC : C.submatrix s id = 0) :
    nF (fromCols ((1 : Matrix ι ι K).submatrix s id)ᵀ C) ≤ nF C := by
  classical
  set E := (1 : Matrix ι ι K).submatrix s id with hE
  refine nF_le_of_minors _ (nF_nonneg' C) fun u => ?_
  by_cases hu : ∀ k, ∃ x, u x = s k
  swap
  · push_neg at hu
    obtain ⟨k, hk⟩ := hu
    have : ((fromCols Eᵀ C).submatrix u id).det = 0 := by
      refine det_eq_zero_of_column_eq_zero (Sum.inl k) fun x => ?_
      simpa [hE, one_apply] using hk x
    rw [this, norm_zero]
    exact nF_nonneg' C
  by_cases inj : Function.Injective u
  swap
  · rw [Function.Injective] at inj
    push_neg at inj
    obtain ⟨x, y, hxy, hne⟩ := inj
    have : ((fromCols Eᵀ C).submatrix u id).det = 0 :=
      det_zero_of_row_eq hne (by ext j; simp [hxy])
    rw [this, norm_zero]
    exact nF_nonneg' C
  choose σ hσ using hu
  have hσi : Function.Injective σ := fun a b h => hs (by rw [← hσ a, ← hσ b, h])
  let e0 : {x : κ ⊕ κ' // x ∈ Set.range (Sum.inl : κ → κ ⊕ κ')} ≃ {x // x ∈ Set.range σ} :=
    (Equiv.ofInjective _ Sum.inl_injective).symm.trans (Equiv.ofInjective σ hσi)
  let e : Equiv.Perm (κ ⊕ κ') := e0.extendSubtype
  have he : ∀ k, e (Sum.inl k) = σ k := by
    intro k
    have h := e0.extendSubtype_apply_of_mem (Sum.inl k) ⟨k, rfl⟩
    have h2 : (Equiv.ofInjective _ Sum.inl_injective).symm
        (⟨Sum.inl k, ⟨k, rfl⟩⟩ : {x : κ ⊕ κ' // x ∈ Set.range (Sum.inl : κ → κ ⊕ κ')}) = k :=
      Equiv.ofInjective_symm_apply Sum.inl_injective k
    simpa [e0, h2] using h
  have hb : ((fromCols Eᵀ C).submatrix u id).submatrix e id =
      fromBlocks 1 0 (Eᵀ.submatrix (u ∘ e ∘ Sum.inr) id) (C.submatrix (u ∘ e ∘ Sum.inr) id) := by
    ext (a | a) (b | b)
    · simp [he, hσ, hE, one_apply, hs.eq_iff, eq_comm]
    · simpa [he, hσ] using congrFun (congrFun hC a) b
    · simp
    · simp
  rw [← norm_det_perm _ e, hb, det_fromBlocks_zero₁₂, det_one, one_mul]
  exact minor_le_nF C _
end GlobalTheory.CompanionTheory.Wedge
