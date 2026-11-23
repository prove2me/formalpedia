-- Prove2me | solution 1 for IsFoldable_pow_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:28:37.059932+00:00
-- url     : https://prove2.me/submissions/e9b81ca0-c461-426b-a3fc-d115af96bb9c

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_foldable_pow_domain_card
import Theorems.Thm_pow_domain_is_coset
import Theorems.Thm_P2M_IsFoldable_of_dvd__2b6a9c0f2500

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] {D : Finset F} {m n : ℕ}
    (hfold : IsFoldable D (m * n)) (hm : m > 0) :
    IsFoldable (pow_domain D m) n := by
  obtain ⟨H', a', hD'⟩ := pow_domain_is_coset (hfold.of_dvd' (dvd_mul_right m n))
  refine ⟨H', a', hD', ?_⟩
  obtain ⟨H, a, hD, hdiv⟩ := hfold
  exact Nat.dvd_of_mul_dvd_mul_left hm <|
    foldable_pow_domain_card D m ⟨H, a, hD, (dvd_mul_right m n).trans hdiv⟩ ▸ hdiv
