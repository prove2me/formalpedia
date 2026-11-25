-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.isLocalizedModule_of_ringHom_of_qcqs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:09:12.006131+00:00
-- url     : https://prove2.me/submissions/71c240b8-ebb6-432e-a725-ebb7883df744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_zero_of_isCompact
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_res_of_qcqs
import Theorems.Thm_GlobalTheory_QCoh_isUnit_res_of_le_basicOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable [F.IsQuasicoherent]
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) {A : Type*} [CommRing A]
    (φ : A →+* Γ(X, U)) (a : A) (h : V ≤ U) (hV : V = X.basicOpen (φ a))
    [Module A Γ(F, U)] [Module A Γ(F, V)]
    (hsU : ∀ (r : A) (s : Γ(F, U)), r • s = φ r • s)
    (hsV : ∀ (r : A) (s : Γ(F, V)), r • s = X.presheaf.map (homOfLE h).op (φ r) • s)
    (l : Γ(F, U) →ₗ[A] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsLocalizedModule.Away a l := by
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun s ↦ ?_) (fun t ht ↦ ?_)
  · have := (isUnit_res_of_le_basicOpen (φ a) h hV.le).map
      (algebraMap Γ(X, V) (Module.End Γ(X, V) Γ(F, V)))
    rw [Module.End.isUnit_iff] at this ⊢
    convert this using 1
    ext s
    exact hsV a s
  · obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res_of_qcqs F hU hU' (φ a) h hV s
    exact ⟨n, t, by rw [hsV, hl, map_pow, map_pow, ht]⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isCompact F hU (φ a) h hV t (by rw [← hl, ht])
    exact ⟨n, by rw [hsU, map_pow, hn]⟩
end GlobalTheory.QCoh.Qcqs
