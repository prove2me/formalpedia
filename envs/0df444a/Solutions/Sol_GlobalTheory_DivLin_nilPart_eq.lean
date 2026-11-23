-- Prove2me | solution 1 for GlobalTheory.DivLin.nilPart_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:04:32.554801+00:00
-- url     : https://prove2.me/submissions/3e3fc4cb-fc2d-451c-98ca-600956d29b19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]
namespace GlobalTheory.DivLin
theorem _root_.solution (l : ℕ) (M : I → Module.End O H) (t : I → R) :
    nilPart l M R t = (lPrime l : R) • ∑ i, t i • (M i).baseChange R := rfl
end GlobalTheory.DivLin
