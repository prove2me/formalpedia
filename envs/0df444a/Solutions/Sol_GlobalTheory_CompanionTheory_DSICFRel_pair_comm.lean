-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.pair_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:22.649017+00:00
-- url     : https://prove2.me/submissions/37dbbf9d-5080-4376-bd5f-20b664cf2f09

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution {ι A : Type} [DecidableEq ι] [Ring A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i j k l : ι) :
    (c i * a j) * (c k * a l) - (c k * a l) * (c i * a j) =
      (if j = k then c i * a l else 0) - (if l = i then c k * a j else 0) := by
  have h1 : a j * c k = (if j = k then 1 else 0) - c k * a j := eq_sub_of_add_eq (hac j k)
  have h2 : a l * c i = (if l = i then 1 else 0) - c i * a l := eq_sub_of_add_eq (hac l i)
  have h3 : c k * c i = - (c i * c k) := eq_neg_of_add_eq_zero_left (hcc k i)
  have h4 : a l * a j = - (a j * a l) := eq_neg_of_add_eq_zero_left (haa l j)
  have e1 : (c i * a j) * (c k * a l) = (if j = k then c i * a l else 0) - (c i * c k) * (a j * a l) := by
    rw [mul_assoc, ← mul_assoc (a j), h1]
    split_ifs <;> noncomm_ring
  have e2 : (c k * a l) * (c i * a j) = (if l = i then c k * a j else 0) - (c k * c i) * (a l * a j) := by
    rw [mul_assoc, ← mul_assoc (a l), h2]
    split_ifs <;> noncomm_ring
  rw [e1, e2, h3, h4]
  noncomm_ring
end GlobalTheory.CompanionTheory.DSICFRel
