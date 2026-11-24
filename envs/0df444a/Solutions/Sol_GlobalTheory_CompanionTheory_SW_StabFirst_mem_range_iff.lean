-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:15:50.117285+00:00
-- url     : https://prove2.me/submissions/38ee8bf3-a729-47e6-99ca-810bf8821d7e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_coe_blockGL
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_exists_blockGL
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_of_blockGL_mem_HR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mat_iotaHom

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution (hs : s ≠ 0) (h : HA R σ (blockOne s J)) :
    h ∈ (iotaHom R σ J s).range ↔
      ((HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) 0 0 = 1 ∧
        ∀ i : Fin M, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) i.succ 0 = 0) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [mat_iotaHom, coe_blockGL]
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨h0, hi⟩
    have hu : IsUnit (inclR (F := F) R s) := (isUnit_iff_ne_zero.2 hs).map (inclR (F := F) R)
    have hm : HA.mat R σ _ h ∈ UJ (sigR R σ) (blockOne (inclR (F := F) R s) (JR (F := F) R J)) := by
      have := mat_mem R σ _ h
      unfold HR at this
      rwa [JR_blockOne] at this
    obtain ⟨g, hg⟩ := exists_blockGL _ _ hu hm h0 hi
    have hgm : g ∈ HR R σ J := by
      apply of_blockGL_mem_HR R σ J s
      rw [hg]
      exact mat_mem R σ _ h
    exact ⟨mkHA R σ J g hgm, mat_injective R σ _ hg⟩
end GlobalTheory.CompanionTheory.SW.StabFirst
