-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.geomRegFib_adicCompletion_of_essFiniteType_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:34.51214+00:00
-- url     : https://prove2.me/submissions/ccc20062-d352-4f6a-adb0-46438606af08

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_exists_loc
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_compl_equiv
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_transport

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
theorem _root_.solution :
    (∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], ReciprocityTheory.AnForm.R.FinalTheorems.QERing A) →
      ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A],
        ReciprocityTheory.AnForm.R.FinalTheorems.GeomRegFib A (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  intro hQE A _ _ _
  obtain ⟨A₀, _, _, p, _, ⟨e⟩⟩ := exists_loc A
  have h2 := ((hQE A₀).2.1 p).2
  obtain ⟨f, hf⟩ := compl_equiv _ _ e (maximalIdeal (Localization.AtPrime p)) (maximalIdeal A)
    (map_ringEquiv_maximalIdeal e)
  exact transport _ _ _ _ e f hf h2
end GlobalTheory.GeomRegFibTransport
