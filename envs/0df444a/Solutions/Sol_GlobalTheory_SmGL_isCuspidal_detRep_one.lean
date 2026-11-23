-- Prove2me | solution 1 for GlobalTheory.SmGL.isCuspidal_detRep_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:22.190889+00:00
-- url     : https://prove2.me/submissions/0105e40c-bb32-4250-a668-7188df00be27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL
theorem _root_.solution {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsCuspidal (detRep (Fin 1) χ) := by
  refine ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, fun s d e he => absurd ?_ he⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  simpa using (mem_unipRad.1 hu).2 a i i
end GlobalTheory.SmGL
