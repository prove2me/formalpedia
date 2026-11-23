-- Prove2me | solution 1 for GlobalTheory.GramCount.Prim.map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:04.037802+00:00
-- url     : https://prove2.me/submissions/0057425e-6c36-41b9-b48e-8cf9a3bf5a24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Theorems.Thm_GlobalTheory_GramCount_map_ip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}
namespace GlobalTheory.GramCount
namespace Prim
theorem _root_.solution {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) :
    Prim c' (fun a i => φ (x a i)) := by
  unfold Prim at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨fun b i => φ (y b i), fun a b => ?_⟩
  show ip c' (fun i => φ (x a i)) (fun i => φ (y b i)) = _
  rw [← map_ip c c' φ hφ (x a) (y b), hy a b]
  split_ifs <;> simp
end Prim
end GlobalTheory.GramCount
