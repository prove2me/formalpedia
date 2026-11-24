-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.incl_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:02:39.417622+00:00
-- url     : https://prove2.me/submissions/23974d07-3fd4-47d0-b8aa-39a63ef88449

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_mem_unitGL_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_algebraMap_le_one_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_algebraMap_lt_one_iff

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
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [FiniteDimensional k E]
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution {n : ℕ} (g : GL (Fin n) k) :
    incl g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) k := by
  have h1 : ∀ i j, ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j) := fun _ _ => rfl
  have h2 : ∀ i j, (((incl g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      algebraMap k E (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := by
    intro i j
    rw [← map_inv]
    rfl
  simp only [iwahori, Set.mem_setOf_eq, mem_unitGL_iff, h1, h2, val_algebraMap_le_one_iff,
    val_algebraMap_lt_one_iff]
end GlobalTheory.CompanionTheory.TfLoc.Iw
