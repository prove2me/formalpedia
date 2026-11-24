-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TwistUnit.adjoin_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:18.500914+00:00
-- url     : https://prove2.me/submissions/15cce4dc-2a78-4b2a-bd28-adf49ec6804e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemAdjoinOfMulEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TwistUnit
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.TwistUnit
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s : A} (L : Submodule O A)
    (hL : ∀ y ∈ L, s * y ∈ L) {a : A} (ha : a ∈ Algebra.adjoin O {s}) : ∀ y ∈ L, a * y ∈ L := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact hL
  | algebraMap r =>
    intro y hy
    rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]; exact L.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]; exact hx _ (hz y hy)
end GlobalTheory.UnitLemma.TwistUnit
