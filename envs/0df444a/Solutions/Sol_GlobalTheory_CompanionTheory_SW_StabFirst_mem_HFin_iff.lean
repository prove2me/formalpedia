-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.mem_HFin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:45.746533+00:00
-- url     : https://prove2.me/submissions/2c10ba6b-7e88-4052-b234-5b94aa31931d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_blockGL_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_of_blockGL_mem_UJ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_exists_blockGL
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_bc_blockGL
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
theorem _root_.solution (hs : s ≠ 0) (u : HA R σ J) :
    HA.mat R σ _ (iotaHom R σ J s u) ∈ HFin R σ (blockOne s J) ↔ HA.mat R σ J u ∈ HFin R σ J := by
  rw [mat_iotaHom]
  constructor
  · rintro ⟨γ, hγ, e⟩
    rcases subsingleton_or_nontrivial (R ⊗[F] E) with hK | hK
    · have : Subsingleton (GL (Fin M) (R ⊗[F] E)) := inferInstance
      rw [Subsingleton.elim (HA.mat R σ J u) 1]
      exact one_mem _
    · have inj : Function.Injective (inclR (F := F) (E := E) R) := by
        exact RingHom.injective _
      have ent : ∀ a b, inclR (F := F) R ((γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) a b) =
          blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E)) a b := by
        intro a b
        exact congrFun (congrFun (congrArg (fun g : GL (Fin (M + 1)) (R ⊗[F] E) =>
          (g : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))) e) a) b
      have h0 : (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) 0 0 = 1 :=
        inj (by rw [ent]; simp)
      have hi : ∀ i : Fin M, (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i.succ 0 = 0 :=
        fun i => inj (by rw [ent]; simp)
      obtain ⟨g, rfl⟩ := exists_blockGL _ _ (isUnit_iff_ne_zero.2 hs) hγ h0 hi
      refine ⟨g, of_blockGL_mem_UJ _ _ _ hγ, ?_⟩
      apply blockGL_injective
      rw [← bc_blockGL]
      exact e
  · rintro ⟨g, hg, e⟩
    exact ⟨blockGL g, blockGL_mem_UJ _ _ _ hg, by rw [bc_blockGL, e]⟩
end GlobalTheory.CompanionTheory.SW.StabFirst
