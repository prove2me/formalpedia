-- Prove2me | solution 1 for GlobalTheory.map_liesOver_of_flat_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:56.188671+00:00
-- url     : https://prove2.me/submissions/61ebaef2-7535-4953-a0ee-98d400530b92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (p : Ideal A) [p.IsPrime] [(p.map (algebraMap A B)).IsPrime] :
    (p.map (algebraMap A B)).LiesOver p := by
  obtain ⟨P, hP, _, hl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p)
    (q := (p.map (algebraMap A B)).under A) (p.map (algebraMap A B)) Ideal.le_comap_map
  have : P = p.map (algebraMap A B) :=
    le_antisymm hP (Ideal.map_le_iff_le_comap.2 hl.over.le)
  exact this ▸ hl
end GlobalTheory
