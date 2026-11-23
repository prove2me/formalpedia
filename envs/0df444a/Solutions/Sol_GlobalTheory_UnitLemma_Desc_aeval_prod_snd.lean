-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.aeval_prod_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:40.751737+00:00
-- url     : https://prove2.me/submissions/f8295a99-37d2-4fde-b950-42702e5387e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProductLatticePositionsAndTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (x : A₁ × A₂) (f : R[X]) : (aeval x f).2 = aeval x.2 f :=
  (aeval_algHom_apply (AlgHom.snd R A₁ A₂) x f).symm
end GlobalTheory.UnitLemma.Desc
