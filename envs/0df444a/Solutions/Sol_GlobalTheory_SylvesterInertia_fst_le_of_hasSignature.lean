-- Prove2me | solution 1 for GlobalTheory.SylvesterInertia.fst_le_of_hasSignature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:53.731686+00:00
-- url     : https://prove2.me/submissions/713c84dd-9887-4246-8293-ef8847fb0329

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
import Theorems.Thm_GlobalTheory_SylvesterInertia_inlMap_injective
import Theorems.Thm_GlobalTheory_SylvesterInertia_inrMap_injective
import Theorems.Thm_GlobalTheory_SylvesterInertia_chg_injective
import Theorems.Thm_GlobalTheory_SylvesterInertia_pos_of_mem
import Theorems.Thm_GlobalTheory_SylvesterInertia_nonpos_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SylvesterInertia
theorem _root_.solution {J : Matrix n n ℂ} {a b a' b' : ℕ}
    (h : Formalism.UG.HasSignature J a b) (h' : Formalism.UG.HasSignature J a' b') : a ≤ a' := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  by_contra hlt
  push_neg at hlt
  set U := LinearMap.range (chg e P ∘ₗ inlMap a b)
  set N := LinearMap.range (chg e' P' ∘ₗ inrMap a' b')
  have hU : finrank ℂ U = a := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e P).comp (inlMap_injective a b))]
    simp
  have hN : finrank ℂ N = b' := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e' P').comp (inrMap_injective a' b'))]
    simp
  have hcard : Fintype.card n = a' + b' := by simpa using Fintype.card_congr e'
  have hsup : finrank ℂ ↥(U ⊔ N) ≤ Fintype.card n := by
    have := Submodule.finrank_le (U ⊔ N)
    simpa using this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U N
  have hinf : U ⊓ N ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have h1 := pos_of_mem hP (Submodule.mem_inf.1 hx).1 hx0
  have h2 := nonpos_of_mem hP' (Submodule.mem_inf.1 hx).2
  exact lt_irrefl _ (lt_of_lt_of_le h1 h2)
end GlobalTheory.SylvesterInertia
