-- Prove2me | solution 1 for GlobalTheory.GramCount.prim_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:11.871104+00:00
-- url     : https://prove2.me/submissions/c3ce69a8-3819-4a0d-8324-59cb1191b177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Theorems.Thm_GlobalTheory_GramCount_map_ip
import Theorems.Thm_GlobalTheory_GramCount_prim_of_sub_mem

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
theorem _root_.solution (hc : ∀ u, c (c u) = u) {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (hs : Function.Surjective φ)
    (hk : ∀ u, φ u = 0 → IsUnit (1 + u)) {m : ℕ} {x : Fin m → Fin n → A}
    (h : Prim c' (fun a i => φ (x a i))) : Prim c x := by

  unfold Prim at h
  obtain ⟨y', hy'⟩ := h
  choose y hy using fun b i => hs (y' b i)
  apply prim_of_sub_mem c hc (RingHom.ker φ) (fun u hu => hk u (RingHom.mem_ker.mp hu)) x y
  intro a b
  have h2 : ip c' (fun i => φ (x a i)) (y' b) = if a = b then 1 else 0 := hy' a b
  have e : (fun i => φ (y b i)) = y' b := funext (hy b)
  rw [RingHom.mem_ker, map_sub, map_ip c c' φ hφ, e, h2]
  split_ifs <;> simp
end GlobalTheory.GramCount
