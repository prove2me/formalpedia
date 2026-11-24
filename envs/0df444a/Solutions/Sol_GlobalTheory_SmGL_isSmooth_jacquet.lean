-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_jacquet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:14.645343+00:00
-- url     : https://prove2.me/submissions/373a508f-3995-49b9-9395-1aabe280da98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Theorems.Thm_GlobalTheory_SmGL_jacquet_mk
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
theorem _root_.solution [TopologicalSpace H] [IsTopologicalGroup H] {ρ : Representation F G V}
    (hρ : IsSmooth ρ) (N : Subgroup G) (s : H →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (hc : Continuous s) :
    IsSmooth (jacquet ρ N s hs) := by
  refine isSmooth_of_nhds fun w => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine Filter.mem_of_superset (((hρ v).preimage hc).mem_nhds (by simp)) fun g hg => ?_
  have hg' : ρ (s g) v = v := hg
  show jacquet ρ N s hs g _ = _
  rw [jacquet_mk, hg']
end GlobalTheory.SmGL
