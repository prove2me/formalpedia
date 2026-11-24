-- Prove2me | solution 1 for GlobalTheory.DivLin.nilPart_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:30:06.644869+00:00
-- url     : https://prove2.me/submissions/937a4c83-ac8b-46c0-ba75-232710bbbb07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
import Theorems.Thm_P2M_GlobalTheory_DivLin_baseChange_mul__56c41815aef1
import Theorems.Thm_GlobalTheory_DivLin_nilPart_eq

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
theorem _root_.solution {M : I → Module.End O H} (f : Module.End O H) (hM : ∀ i, Commute (M i) f) (l : ℕ) (t : I → R) :
    Commute (nilPart l M R t) (f.baseChange R) := by
  rw [nilPart_eq]
  refine Commute.smul_left ?_ _
  refine Commute.sum_left _ _ _ fun i _ => Commute.smul_left ?_ _
  show _ * _ = _ * _
  rw [← baseChange_mul', ← baseChange_mul', (hM i).eq]
end GlobalTheory.DivLin
