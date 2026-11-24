-- Prove2me | solution 1 for GlobalTheory.flat_zero_of_quasiIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:33.244258+00:00
-- url     : https://prove2.me/submissions/fae7c8f5-7319-4c65-b877-994db7ace5f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_ConeExact_flat_zero
import Theorems.Thm_GlobalTheory_cochain_d_d_apply
import Theorems.Thm_GlobalTheory_cochain_comm_apply
import Theorems.Thm_GlobalTheory_quasiIso_iff_coneExact

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
    [hφ : QuasiIso φ] (hK : ∀ p, 1 ≤ p → Module.Flat R (K.X p))
    (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p)) :
    Module.Flat R (K.X 0) :=
  haveI : ∀ p, Module.Flat R (K.X (p + 1)) := fun p => hK _ (Nat.le_add_left 1 p)
  ConeExact.flat_zero (K := fun p => K.X p) (C := fun p => C.X p)
    (dK := fun p => (K.d p (p + 1)).hom) (dC := fun p => (C.d p (p + 1)).hom)
    (φ := fun p => (φ.f p).hom) ((quasiIso_iff_coneExact φ).1 hφ)
    (fun _ => cochain_d_d_apply K _ _ _) (fun _ => cochain_d_d_apply C _ _ _)
    (fun _ => cochain_comm_apply φ _ _) n
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnK p hp))
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnC p hp))
end GlobalTheory
