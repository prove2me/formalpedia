-- Prove2me | solution 1 for GlobalTheory.DiscClass.abs_norm_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:46.076814+00:00
-- url     : https://prove2.me/submissions/ef0f3402-0c14-43f0-ba0a-36a202d85cf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
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
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DiscClass
namespace GlobalTheory.DiscClass
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (x : K) :
    ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ‖φK x‖ ^ 2 := by
  have hcx : (InfinitePlace.mk φK).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro e
    apply hc
    ext y
    simp only [RingHom.comp_apply]
    rw [← ComplexEmbedding.conjugate_coe_eq, e]
  have hpos : 0 < InfinitePlace.nrComplexPlaces K := by
    classical
    unfold InfinitePlace.nrComplexPlaces
    convert Fintype.card_pos_iff.2 (⟨⟨_, hcx⟩⟩ : Nonempty {w : InfinitePlace K // w.IsComplex})
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
  have huniq : ∀ w : InfinitePlace K, w = InfinitePlace.mk φK := fun w =>
    Fintype.card_le_one_iff.1 hcard.le w _
  have hp := InfinitePlace.prod_eq_abs_norm x
  have e : (∏ w : InfinitePlace K, w x ^ w.mult) = InfinitePlace.mk φK x ^ (InfinitePlace.mk φK).mult := by
    rw [Fintype.prod_eq_single (InfinitePlace.mk φK) fun w hw => absurd (huniq w) hw]
  rw [← hp, e, InfinitePlace.apply, InfinitePlace.mult_isComplex ⟨_, hcx⟩]
end GlobalTheory.DiscClass
