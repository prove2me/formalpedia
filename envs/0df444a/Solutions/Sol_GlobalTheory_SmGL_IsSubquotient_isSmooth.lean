-- Prove2me | solution 1 for GlobalTheory.SmGL.IsSubquotient.isSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:08.882788+00:00
-- url     : https://prove2.me/submissions/c9d5a10a-8c0a-4f0b-aebe-541cd2984c14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_of_nhds

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
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GlobalTheory.SmGL
namespace IsSubquotient
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V}
    (h : IsSubquotient σ ρ) (hρ : IsSmooth ρ) : IsSmooth σ := by
  obtain ⟨S, f, hf⟩ := h
  refine isSmooth_of_nhds fun w => ?_
  obtain ⟨v, rfl⟩ := hf w
  refine Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) fun g hg => ?_
  show σ g (f v) = f v
  rw [← f.isIntertwining]
  congr 1
  exact Subtype.ext hg
end IsSubquotient
end GlobalTheory.SmGL
