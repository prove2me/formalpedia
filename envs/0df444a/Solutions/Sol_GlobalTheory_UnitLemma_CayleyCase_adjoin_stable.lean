-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.adjoin_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:50.09894+00:00
-- url     : https://prove2.me/submissions/8e96544f-4dae-44fa-9561-5217131e102b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a : A) (L : Submodule O A)
    (hL : ∀ y ∈ L, a * y ∈ L) : ∀ z ∈ Algebra.adjoin O ({a} : Set A), ∀ y ∈ L, z * y ∈ L := by
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hL
  | algebraMap r => intro y hy; rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x y _ _ hx hy => intro w hw; rw [add_mul]; exact L.add_mem (hx w hw) (hy w hw)
  | mul x y _ _ hx hy => intro w hw; rw [mul_assoc]; exact hx _ (hy w hw)
end GlobalTheory.UnitLemma.CayleyCase
