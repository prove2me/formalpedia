-- Prove2me | solution 1 for GlobalTheory.SmGL.IsSubquotient.of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:19.798817+00:00
-- url     : https://prove2.me/submissions/561e99e4-a142-4ab8-a92c-4813e564a8fd

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
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V}
    (f : σ.IntertwiningMap ρ) (hf : Function.Injective f) : IsSubquotient σ ρ := by
  let R : Subrepresentation ρ := ⟨LinearMap.range f.toLinearMap, by
    rintro x _ ⟨v, rfl⟩
    exact ⟨σ x v, f.isIntertwining _ _ x v⟩⟩
  let e := LinearEquiv.ofInjective f.toLinearMap hf
  refine ⟨R, ⟨e.symm.toLinearMap, fun x => ?_⟩, e.symm.surjective⟩
  ext v
  obtain ⟨w, rfl⟩ := e.surjective v
  show e.symm _ = σ x (e.symm (e w))
  rw [e.symm_apply_apply, LinearEquiv.symm_apply_eq]
  exact Subtype.ext (f.isIntertwining _ _ x w).symm
end IsSubquotient
end GlobalTheory.SmGL
