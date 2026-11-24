-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.unit_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:09.724329+00:00
-- url     : https://prove2.me/submissions/e6b11ce5-ca7e-45e9-9e28-7e135bd0541a

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
    (x e : R₂) (hu : IsUnit x) (hσ : σ₂ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((1, x) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (1, x) = (1, x)) ∧
      ((1, x) : R₁ × R₂) * (1 - (0, e)) = 1 - (0, e) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨isUnit_one, hu⟩, ?_⟩, ?_⟩
  · show (σ₁ 1, σ₂ x) = (1, x)
    rw [hσ, map_one]
  · exact Prod.ext (by simp) (by simpa using h1)
end GlobalTheory.UnitLemma.Desc
