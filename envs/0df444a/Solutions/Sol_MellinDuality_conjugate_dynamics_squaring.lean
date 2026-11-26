-- Prove2me | solution 1 for MellinDuality.conjugate_dynamics_squaring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:13.578215+00:00
-- url     : https://prove2.me/submissions/ec8c7a4a-58db-423c-98dd-14b1e909aa40

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_conjugate_dynamics


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {a : ZMod p} (ha : a ∈ fiber χ 1) :
    (fam χ 2 a).re = ∑ v ∈ fiber χ 1, parSign (a⁻¹ * v) * parSign (a⁻¹ * v ^ 2) :=
  conjugate_dynamics hp8 hχ ha
end MellinDuality
