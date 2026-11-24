-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.sigma_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:46.356033+00:00
-- url     : https://prove2.me/submissions/668a9245-7f8c-4292-91f1-00b1d6e04a8a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_mem_unitGL_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_aut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution [IsGalois k E] {n : ℕ} (τ : E ≃ₐ[k] E) (g : GL (Fin n) E) :
    sigmaGL τ g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) E := by
  have h1 : ∀ i j, ((sigmaGL τ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      τ ((g : Matrix (Fin n) (Fin n) E) i j) := fun _ _ => rfl
  have h2 : ∀ i j, (((sigmaGL τ g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      τ (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    rw [← map_inv]
    rfl
  simp only [iwahori, Set.mem_setOf_eq, mem_unitGL_iff, h1, h2, val_aut]
end GlobalTheory.CompanionTheory.TfLoc.Iw
