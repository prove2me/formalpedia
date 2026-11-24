-- Prove2me | solution 1 for GlobalTheory.quasiIso_tensorLeft_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:31.270418+00:00
-- url     : https://prove2.me/submissions/11410486-e6f7-4823-9a84-3c3d38d6ee1f

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
theorem _root_.solution {K C : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ C)
    [QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : ModuleCat.{u} R) :
    QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ) :=
  (quasiIso_iff_coneExact _).2 (coneExact_lTensor_of_quasiIso φ hK hC n hnK hnC M)
end GlobalTheory
