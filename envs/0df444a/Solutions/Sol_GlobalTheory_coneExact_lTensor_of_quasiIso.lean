-- Prove2me | solution 1 for GlobalTheory.coneExact_lTensor_of_quasiIso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:28.929056+00:00
-- url     : https://prove2.me/submissions/cc06527f-36ec-43f5-99f1-21ca6bd55175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
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
    [hφ : QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : Type*) [AddCommGroup M] [Module R M] :
    ConeExact (K := fun p => M ⊗[R] K.X p) (C := fun p => M ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.lTensor M) (fun p => (C.d p (p + 1)).hom.lTensor M)
      (fun p => (φ.f p).hom.lTensor M) :=
  ConeExact.lTensor (K := fun p => K.X p) (C := fun p => C.X p)
    (dK := fun p => (K.d p (p + 1)).hom) (dC := fun p => (C.d p (p + 1)).hom)
    (φ := fun p => (φ.f p).hom) ((quasiIso_iff_coneExact φ).1 hφ)
    (fun _ => cochain_d_d_apply K _ _ _) (fun _ => cochain_d_d_apply C _ _ _)
    (fun _ => cochain_comm_apply φ _ _) n
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnK p hp))
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnC p hp)) M
end GlobalTheory
