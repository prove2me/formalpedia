-- Prove2me | solution 1 for GlobalTheory.cechModulesFunctor_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:45.208094+00:00
-- url     : https://prove2.me/submissions/0c58194e-2ea0-4576-88f3-c65273626d10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_cechFunctor_shortExact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable [LinearOrder ι]
namespace GlobalTheory
theorem _root_.solution (S : ShortComplex X.Modules)
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (cechOpen V U s)) ∧
      Function.Exact (S.f.app (cechOpen V U s)) (S.g.app (cechOpen V U s)) ∧
      Function.Surjective (S.g.app (cechOpen V U s))) :
    (S.map (cechModulesFunctor R V U)).ShortExact :=
  cechFunctor_shortExact (S.map (cechCubeFunctor R V U)) fun s hs =>
    ModuleCat.shortComplex_shortExact _ (h s hs).2.1 (h s hs).1 (h s hs).2.2
end GlobalTheory
