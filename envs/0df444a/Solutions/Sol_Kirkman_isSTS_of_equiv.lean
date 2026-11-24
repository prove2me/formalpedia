-- Prove2me | solution 1 for Kirkman.isSTS_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:49:12.433271+00:00
-- url     : https://prove2.me/submissions/d4751f8b-c9c5-4d7b-970b-5086857e5a6a

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman
public import Theorems.Thm_Kirkman_IsSTSOn_map
public import Theorems.Thm_Kirkman_SteinerOp_isSTSOn_triples


set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
namespace Kirkman
theorem _root_.solution {P : Type*} [Fintype P] {v : ℕ} (S : SteinerOp P)
    (hP : Fintype.card P = v) : ∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯 := by
  classical
  exact ⟨_, S.isSTSOn_triples.map (Fintype.equivFinOfCardEq hP)⟩
end Kirkman
