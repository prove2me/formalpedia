-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:37.095809+00:00
-- url     : https://prove2.me/submissions/38c90f50-580d-4763-9672-082e08b4fba5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
theorem _root_.solution (L : Submodule (OF E) E) : polMod L * L ≤ dualLat L :=
  Submodule.mul_le.2 fun _ hξ x hx y hy => hξ.2 x hx y hy
end GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
