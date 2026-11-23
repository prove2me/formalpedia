-- Prove2me | solution 1 for GlobalTheory.SmGL.IsSmoothChar.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:09.906382+00:00
-- url     : https://prove2.me/submissions/7a4f4c3c-a014-48fd-8766-23624d1245b2

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
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GlobalTheory.SmGL
namespace IsSmoothChar
theorem _root_.solution {χ ψ : G →* Fˣ} (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    IsSmoothChar (χ * ψ) :=
  Subgroup.isOpen_mono (H₁ := χ.ker ⊓ ψ.ker)
    (fun g hg => by simp [MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2]) (IsOpen.inter hχ hψ)
end IsSmoothChar
end GlobalTheory.SmGL
