-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.unit_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:09.01075+00:00
-- url     : https://prove2.me/submissions/6ed745f8-2f13-4288-bb7c-36c4723dcde5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₁) (hu : IsUnit x) (hσ : σ₁ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((x, 1) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (x, 1) = (x, 1)) ∧
      ((x, 1) : R₁ × R₂) * (1 - (e, 0)) = 1 - (e, 0) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨hu, isUnit_one⟩, ?_⟩, ?_⟩
  · show (σ₁ x, σ₂ 1) = (x, 1)
    rw [hσ, map_one]
  · exact Prod.ext (by simpa using h1) (by simp)
end GlobalTheory.UnitLemma.Desc
