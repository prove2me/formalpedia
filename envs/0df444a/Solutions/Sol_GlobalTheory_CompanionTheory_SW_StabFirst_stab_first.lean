-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.stab_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:22:50.344811+00:00
-- url     : https://prove2.me/submissions/038790e5-d01f-49d8-aba0-31eaa4414173

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_act_first_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mem_range_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mem_HFin_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_act_iota
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_isEmbedding_iotaHom
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_isClosed_range_iotaHom
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_t2_tensor_product

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R], ∃ ι : HA R σ J →* HA R σ (blockOne (algebraMap F E t) J), IsClosedEmbedding ι ∧ (∀ u, (HA.mat R σ _ (ι u) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) = blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) ∧ (∀ h, h ∈ ι.range ↔ actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) ∧ (∀ u, HA.mat R σ _ (ι u) ∈ HFin R σ (blockOne (algebraMap F E t) J) ↔ HA.mat R σ J u ∈ HFin R σ J) ∧ ∀ (u : HA R σ J) (n : ℕ) (X : Fin n → Fin M → R ⊗[F] E), actW R σ _ (ι u) (consTup X) = consTup (actW R σ J u X) := by
  intro F E _ _ _ _ _ σ hCM M J _ t ht R _ _ _ _ _
  have hs : algebraMap F E t ≠ 0 := by
    simpa using ht
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : T2Space (R ⊗[F] E) := t2_tensor_product R
  refine ⟨iotaHom R σ J (algebraMap F E t), ?_, fun _ => rfl, ?_, ?_, ?_⟩
  · exact ⟨isEmbedding_iotaHom R σ J _, isClosed_range_iotaHom R σ J _ hs⟩
  · intro h
    rw [mem_range_iff R σ J _ hs h]
    exact (act_first_iff R σ J _ (n := 0) h).symm
  · exact fun u => mem_HFin_iff R σ J _ hs u
  · exact fun u n X => act_iota R σ J _ u X
end GlobalTheory.CompanionTheory.SW.StabFirst
