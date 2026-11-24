-- Prove2me | solution 1 for GlobalTheory.InertZeta.finite_dosetOf_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:52:16.088252+00:00
-- url     : https://prove2.me/submissions/17b8607b-cd5b-4023-8ca8-ac2aaea3c67d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
import Theorems.Thm_GlobalTheory_InertZeta_exists_of_dosetOf_eq
import Theorems.Thm_Formalism_UG_P_finite_cosets_in_doset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open GlobalTheory GlobalTheory.InertZeta
open Formalism.UG
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.InertZeta
theorem _root_.solution (hK : IsCommensurated K) (S : Set G) :
    Finite {x : G ⧸ K // dosetOf K x = S} := by
  by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
  · obtain ⟨x₀, rfl⟩ := h
    have hf := Formalism.UG.P.finite_cosets_in_doset hK x₀.out
    have hs : {x : G ⧸ K | dosetOf K x = dosetOf K x₀} ⊆ {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * x₀.out * b} :=
      fun y hy => exists_of_dosetOf_eq hy
    exact (hf.subset hs).to_subtype
  · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
    infer_instance
end GlobalTheory.InertZeta
