-- Prove2me | solution 1 for GlobalTheory.GenEigenFinOrbit.finrank_map_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:53:57.259901+00:00
-- url     : https://prove2.me/submissions/fd86ceaa-fec4-40aa-a31e-ca0a6d8c6131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_map_lt_of_pow_eq_zero
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_map_prod_le

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
include hcomm hst hnil
namespace GlobalTheory.GenEigenFinOrbit
theorem _root_.solution [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) :
    finrank ℂ (N.map gs.prod) ≤ finrank ℂ N - gs.length := by
  induction gs with
  | nil => rw [List.prod_nil, Module.End.one_eq_id, Submodule.map_id]; simp
  | cons g gs ih =>
    have hgs' : ∀ x ∈ gs, x ∈ G := fun x hx => hgs x (by simp [hx])
    have hg : g ∈ G := hgs g (by simp)
    specialize ih hgs'
    set M := N.map gs.prod with hM
    have hMN : M ≤ N := map_prod_le G N hst gs hgs'
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMN
    have hc : Commute g gs.prod :=
      Commute.list_prod_right _ _ fun x hx => hcomm g hg x (hgs' x hx)
    have hMst : M.map g ≤ M := by
      rw [hM, ← Submodule.map_comp, ← Module.End.mul_eq_comp, hc.eq, Module.End.mul_eq_comp,
        Submodule.map_comp]
      exact Submodule.map_mono (hst g hg)
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp, ← hM, List.length_cons]
    by_cases h0 : M = ⊥
    · rw [h0, Submodule.map_bot]; simp
    · have hlt := Submodule.finrank_lt_finrank_of_lt
        (map_lt_of_pow_eq_zero g K hMst (fun n hn => hnil g hg n (hMN hn)) h0)
      omega
end GlobalTheory.GenEigenFinOrbit
