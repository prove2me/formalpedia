-- Prove2me | solution 1 for KirkmanTheorem.kirkman
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:54:19.483608+00:00
-- url     : https://prove2.me/submissions/af4fb9f0-53f1-4a98-aad0-693a284f16f1

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Kirkman
public import Definitions.Def_KirkmanLib_Solution
public import Theorems.Thm_Kirkman_kirkman


set_option autoImplicit true
@[expose] public section
public section
open Finset
open KirkmanTheorem
namespace KirkmanTheorem
theorem _root_.solution (v : ℕ) (hv : 0 < v) :
    (∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯) ↔ v % 6 = 1 ∨ v % 6 = 3 :=
  Kirkman.kirkman v hv
end KirkmanTheorem
