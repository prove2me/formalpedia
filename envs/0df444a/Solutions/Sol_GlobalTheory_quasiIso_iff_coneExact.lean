-- Prove2me | solution 1 for GlobalTheory.quasiIso_iff_coneExact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:55.990056+00:00
-- url     : https://prove2.me/submissions/222c0960-d477-45b1-baf8-de7d0e9293f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_cochain_comm_apply
import Theorems.Thm_GlobalTheory_quasiIsoAt_zero_iff
import Theorems.Thm_GlobalTheory_quasiIsoAt_succ_iff

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
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIso φ ↔ ConeExact (K := fun p => K.X p) (C := fun p => C.X p)
      (fun p => (K.d p (p + 1)).hom) (fun p => (C.d p (p + 1)).hom) (fun p => (φ.f p).hom) := by
  rw [quasiIso_iff]
  constructor
  · intro h
    have h0 := (quasiIsoAt_zero_iff φ).1 (h 0)
    have h1 := fun p => (quasiIsoAt_succ_iff φ p).1 (h (p + 1))
    refine ⟨fun x hx hx' => h0.2 x hx' hx, fun c k hc hk => ?_, fun p c k hc hk => ?_⟩
    · obtain ⟨w, rfl⟩ := (h1 0).2 k c hk hc
      obtain ⟨x, hx, hx'⟩ := h0.1 (c - (φ.f 0).hom w)
        (by rw [map_sub, cochain_comm_apply, sub_eq_zero]; exact hc)
      exact ⟨x + w, by rw [map_add, hx', sub_add_cancel], by rw [map_add, hx]; exact zero_add _⟩
    · obtain ⟨w, rfl⟩ := (h1 (p + 1)).2 k c hk hc
      obtain ⟨x, z, hx, hx'⟩ := (h1 p).1 (c - (φ.f (p + 1)).hom w)
        (by rw [map_sub, cochain_comm_apply, sub_eq_zero]; exact hc)
      exact ⟨z, x + w, by rw [map_add, ← add_assoc, hx', sub_add_cancel],
        by rw [map_add, hx, zero_add]⟩
  · rintro ⟨h0, h1, h2⟩ (_ | p)
    · refine (quasiIsoAt_zero_iff φ).2 ⟨fun y hy => ?_, fun x hx hx' => h0 x hx' hx⟩
      obtain ⟨x, hx, hx'⟩ := h1 y 0 (by rw [map_zero]; exact hy) (map_zero _)
      exact ⟨x, hx', hx⟩
    · refine (quasiIsoAt_succ_iff φ p).2 ⟨fun y hy => ?_, fun x z hx hz => ?_⟩
      · obtain ⟨z, x, hx, hx'⟩ := h2 p y 0 (by rw [map_zero]; exact hy) (map_zero _)
        exact ⟨x, z, hx', hx⟩
      · cases p with
        | zero =>
          obtain ⟨w, -, hw⟩ := h1 z x hz hx
          exact ⟨w, hw⟩
        | succ p =>
          obtain ⟨-, w, -, hw⟩ := h2 p z x hz hx
          exact ⟨w, hw⟩
end GlobalTheory
