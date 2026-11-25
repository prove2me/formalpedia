-- Prove2me | solution 1 for GlobalTheory.CountId.lat_tw_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:27.097979+00:00
-- url     : https://prove2.me/submissions/1167308a-dd00-4526-afa7-b3470b62a7ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_tw_tw
import Theorems.Thm_GlobalTheory_CountId_lat_tw_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]
variable (O : Type) [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]
variable [IsDomain O] [Module.IsTorsionFree O E]
namespace GlobalTheory.CountId
theorem _root_.solution (e : Basis (Fin n) E V) (γ δ : GL (Fin n) E) :
    lat O (tw e δ) = lat O (tw e γ) ↔
      ∀ i j, ((δ * γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range ∧
        (((δ * γ⁻¹)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range := by
  have h1 : tw e δ = tw (tw e γ) (δ * γ⁻¹) := by rw [tw_tw, inv_mul_cancel_right]
  have h2 : tw e γ = tw (tw e δ) (δ * γ⁻¹)⁻¹ := by
    rw [tw_tw, _root_.mul_inv_rev, _root_.inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  rw [le_antisymm_iff]
  constructor
  · rintro ⟨hle, hge⟩ i j
    refine ⟨?_, ?_⟩
    · have hk := (lat_tw_le_iff O (tw e δ) (δ * γ⁻¹)⁻¹).1 (by rw [← h2]; exact hge) i j
      rwa [_root_.inv_inv] at hk
    · exact (lat_tw_le_iff O (tw e γ) (δ * γ⁻¹)).1 (by rw [← h1]; exact hle) i j
  · intro h
    constructor
    · rw [h1]
      exact (lat_tw_le_iff O _ _).2 fun i j => (h i j).2
    · rw [h2]
      exact (lat_tw_le_iff O _ _).2 fun i j => by rw [_root_.inv_inv]; exact (h i j).1
end GlobalTheory.CountId
