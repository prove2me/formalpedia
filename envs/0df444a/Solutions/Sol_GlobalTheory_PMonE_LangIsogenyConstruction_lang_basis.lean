-- Prove2me | solution 1 for GlobalTheory.PMonE.LangIsogenyConstruction.lang_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:51:49.095856+00:00
-- url     : https://prove2.me/submissions/d1056c72-e4a2-422c-b875-fcd6ff38cd7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot
import Theorems.Thm_GlobalTheory_PMonE_LangIsogenyConstruction_lang_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangIsogenyConstruction
open Polynomial
variable {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
namespace GlobalTheory.PMonE.LangIsogenyConstruction
theorem _root_.solution [FiniteDimensional k V] (q : ℕ) (hq : 1 < q) (F : V →+ V)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ q • F v) (hinj : Function.Injective F) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V, ∀ i, F (b i) = b i := by
  classical
  have hs : ⊤ ≤ Submodule.span k {v : V | F v = v} := (lang_span q hq F hF hinj).ge
  let b' := Module.Basis.ofSpan hs
  haveI : Finite _ := Module.Finite.finite_basis b'
  letI := Fintype.ofFinite ((linearIndepOn_empty k id).extend (Set.empty_subset {v : V | F v = v}))
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b').symm
  refine ⟨b'.reindex e, fun i => ?_⟩
  have h1 : b' (e.symm i) ∈ {v : V | F v = v} := Module.Basis.ofSpan_subset hs ⟨e.symm i, rfl⟩
  simpa using h1
end GlobalTheory.PMonE.LangIsogenyConstruction
