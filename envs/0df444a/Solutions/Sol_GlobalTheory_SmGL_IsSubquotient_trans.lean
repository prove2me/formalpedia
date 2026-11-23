-- Prove2me | solution 1 for GlobalTheory.SmGL.IsSubquotient.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:41.677585+00:00
-- url     : https://prove2.me/submissions/53250f9e-31c7-42a5-90da-854aa03e2f3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff

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
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
namespace GlobalTheory.SmGL
namespace IsSubquotient
theorem _root_.solution {τ : Representation F G U} {σ : Representation F G W}
    {ρ : Representation F G V} (h₁ : IsSubquotient τ σ) (h₂ : IsSubquotient σ ρ) :
    IsSubquotient τ ρ := by
  obtain ⟨S, f, hf⟩ := h₁
  obtain ⟨T, g, hg⟩ := h₂
  let R : Subrepresentation ρ :=
    ⟨(S.toSubmodule.comap g.toLinearMap).map T.toSubmodule.subtype, by
      rintro x _ ⟨v, hv, rfl⟩
      refine ⟨T.toRepresentation x v, ?_, rfl⟩
      show g (T.toRepresentation x v) ∈ S.toSubmodule
      rw [g.isIntertwining]
      exact S.apply_mem_toSubmodule x hv⟩
  have hRT : R.toSubmodule ≤ T.toSubmodule := by
    rintro _ ⟨v, -, rfl⟩; exact v.2
  have hmem : ∀ v : R.toSubmodule, (g.toLinearMap ∘ₗ Submodule.inclusion hRT) v ∈ S.toSubmodule := by
    rintro ⟨_, v, hv, rfl⟩; exact hv
  refine ⟨R, ⟨f.toLinearMap ∘ₗ LinearMap.codRestrict S.toSubmodule _ hmem, fun x => ?_⟩, fun u => ?_⟩
  · ext v
    show f _ = τ x (f _)
    rw [← f.isIntertwining]
    congr 1
    apply Subtype.ext
    exact g.isIntertwining _ _ x (Submodule.inclusion hRT v)
  · obtain ⟨w, rfl⟩ := hf u
    obtain ⟨v, hv⟩ := hg w
    refine ⟨⟨v, v, by show g v ∈ S.toSubmodule; rw [hv]; exact w.2, rfl⟩, ?_⟩
    show f _ = f w
    congr 1
    exact Subtype.ext hv
end IsSubquotient
end GlobalTheory.SmGL
