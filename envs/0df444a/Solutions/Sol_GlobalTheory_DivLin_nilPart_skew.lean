-- Prove2me | solution 1 for GlobalTheory.DivLin.nilPart_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:41:06.746826+00:00
-- url     : https://prove2.me/submissions/c0940428-b335-43ef-bcf1-592060797aa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
import Theorems.Thm_GlobalTheory_DivLin_nilPart_eq
import Theorems.Thm_GlobalTheory_DivLin_baseChange_skew_iso
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]
namespace GlobalTheory.DivLin
theorem _root_.solution (B : LinearMap.BilinForm O H) {M : I → Module.End O H}
    (hskew : ∀ i x y, B (M i x) y + B x (M i y) = 0) (hiso : ∀ i j x y, B (M i x) (M j y) = 0) (l : ℕ) (t : I → R)
    (x y : R ⊗[O] H) :
    B.baseChange R (nilPart l M R t x) y + B.baseChange R x (nilPart l M R t y) = 0 := by
  simp only [nilPart_eq, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [← smul_add, ← Finset.sum_add_distrib]
  simp only [← smul_add]
  rw [Finset.sum_eq_zero fun i _ => by rw [(baseChange_skew_iso R B (hskew i) (hiso i i) x y).1, smul_zero], smul_zero]
end GlobalTheory.DivLin
