-- Prove2me | solution 1 for GlobalTheory.quasiIso_extendScalars_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:30.439182+00:00
-- url     : https://prove2.me/submissions/7b62dd06-ba34-415c-94e5-a62961b2be98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_quasiIso_iff_coneExact
import Theorems.Thm_GlobalTheory_coneExact_lTensor_of_quasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    {S : Type w} [CommRing S] (f : R →+* S) :
    QuasiIso (((ModuleCat.extendScalars.{u, w, v} f).mapHomologicalComplex _).map φ) :=
  (quasiIso_iff_coneExact _).2 (coneExact_lTensor_of_quasiIso φ hK hC n hnK hnC
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
end GlobalTheory
