-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.complMap_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:36.5224+00:00
-- url     : https://prove2.me/submissions/632fea25-0343-4383-9bed-c9b97546311a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt
import Theorems.Thm_P2M_GlobalTheory_GeomRegFibTransport_eval__complMap_5470ea4b5f5f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems
namespace GlobalTheory.GeomRegFibTransport
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (h : I.map (RingHom.id R) ≤ I)
    (x : AdicCompletion I R) : complMap (RingHom.id R) I I h x = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]
end GlobalTheory.GeomRegFibTransport
