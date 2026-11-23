-- Prove2me | solution 1 for GlobalTheory.SmGL.isSpherical_detRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:40.664154+00:00
-- url     : https://prove2.me/submissions/e28e36f6-53a4-484c-9f64-8a431b302e47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd

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
theorem _root_.solution {χ : kˣ →* ℂˣ} (h : IsUnram χ) : IsSpherical (detRep n χ) := by
  refine (Submodule.ne_bot_iff _).2 ⟨1, ?_, one_ne_zero⟩
  rintro ⟨_, g, rfl⟩
  have : χ (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g)) = 1 := by
    apply h
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
        algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  simp [detRep, this]
end GlobalTheory.SmGL
