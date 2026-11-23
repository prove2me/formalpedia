-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:03.832432+00:00
-- url     : https://prove2.me/submissions/f51a7e15-f59d-469c-a797-176419588d22

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
theorem _root_.solution {ρ : Representation F G V} (hρ : IsSmooth ρ) {χ : G →* Fˣ}
    (hχ : IsSmoothChar χ) : IsSmooth (twist ρ χ) :=
  isSmooth_of_nhds fun v => Filter.mem_of_superset (((hρ v).inter hχ).mem_nhds (by simp)) (by
    rintro g ⟨h1, h2⟩
    have h1' : ρ g v = v := h1
    have h2' : χ g = 1 := h2
    simp [h1', h2'])
end GlobalTheory.SmGL
