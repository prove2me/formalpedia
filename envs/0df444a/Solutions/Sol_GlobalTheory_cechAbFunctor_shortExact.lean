-- Prove2me | solution 1 for GlobalTheory.cechAbFunctor_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:30.020283+00:00
-- url     : https://prove2.me/submissions/8b648d63-80c3-4768-ab48-92fb5cfabd46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Theorems.Thm_GlobalTheory_cechFunctor_shortExact


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
namespace GlobalTheory
theorem _root_.solution (S : ShortComplex ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}))
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (op (cechOpen V U s))) ∧
      Function.Exact (S.f.app (op (cechOpen V U s))) (S.g.app (op (cechOpen V U s))) ∧
      Function.Surjective (S.g.app (op (cechOpen V U s)))) :
    (S.map (cechAbFunctor V U)).ShortExact :=
  cechFunctor_shortExact (S.map (cechAbCubeFunctor V U)) fun s hs =>
    ModuleCat.shortComplex_shortExact _ (h s hs).2.1 (h s hs).1 (h s hs).2.2
end GlobalTheory
