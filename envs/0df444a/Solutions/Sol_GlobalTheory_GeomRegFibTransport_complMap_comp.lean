-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.complMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:35.234235+00:00
-- url     : https://prove2.me/submissions/adfe49bd-ef03-4fa7-8cdf-308333542a19

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
theorem _root_.solution {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (e : R →+* S)
    (e' : S →+* T) (I : Ideal R) (J : Ideal S) (K : Ideal T) (h : I.map e ≤ J) (h' : J.map e' ≤ K)
    (x : AdicCompletion I R) :
    complMap e' J K h' (complMap e I J h x) = complMap (e'.comp e) I K
      (by rw [← Ideal.map_map]; exact (Ideal.map_mono h).trans h') x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap, evalₐ_complMap, evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]
end GlobalTheory.GeomRegFibTransport
