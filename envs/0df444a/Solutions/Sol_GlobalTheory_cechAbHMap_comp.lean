-- Prove2me | solution 1 for GlobalTheory.cechAbHMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:27.682629+00:00
-- url     : https://prove2.me/submissions/407e2f06-e3ae-48d5-9943-a69c6c1e769b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : Type w} [TopologicalSpace T] {ι : Type}
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) {Q Q' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}}
  (V : Opens T) (U : ι → Opens T)
variable [LinearOrder ι]
variable {P}
namespace GlobalTheory
theorem _root_.solution (φ : P ⟶ Q) (ψ : Q ⟶ Q') (n : ℕ) :
    cechAbHMap V U (φ ≫ ψ) n = cechAbHMap V U φ n ≫ cechAbHMap V U ψ n :=
  (cechAbHFunctor V U n).map_comp φ ψ
end GlobalTheory
