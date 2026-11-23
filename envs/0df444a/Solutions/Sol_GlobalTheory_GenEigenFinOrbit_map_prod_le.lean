-- Prove2me | solution 1 for GlobalTheory.GenEigenFinOrbit.map_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:34.070808+00:00
-- url     : https://prove2.me/submissions/356c242b-652f-4b47-9fe4-53f72b0a13cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)
include hst
namespace GlobalTheory.GenEigenFinOrbit
theorem _root_.solution (gs : List (End ℂ V)) (hgs : ∀ g ∈ gs, g ∈ G) : N.map gs.prod ≤ N := by
  induction gs with
  | nil => simp [Module.End.one_eq_id]
  | cons g gs ih =>
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp]
    exact (Submodule.map_mono (ih fun x hx => hgs x (by simp [hx]))).trans
      (hst g (hgs g (by simp)))
end GlobalTheory.GenEigenFinOrbit
