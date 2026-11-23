-- Prove2me | solution 1 for GlobalTheory.isKroneckerChar_of_jacobiSym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:42.881354+00:00
-- url     : https://prove2.me/submissions/b8b61181-7353-499d-935e-6abee081cbc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory
open QuadraticZeta
namespace GlobalTheory
theorem _root_.solution {d : ℕ} (hd : d % 4 = 3) {χ : DirichletCharacter ℂ d}
    (h : ∀ n : ℕ, χ n = (J(n | d) : ℤ)) : IsKroneckerChar χ := fun n hn => by
  rw [h, jacobiSym.neg _ hn]
  congr 1
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hn) with h1 | h1
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.2 (by omega))]
  · rw [ZMod.χ₄_nat_three_mod_four h1, jacobiSym.quadratic_reciprocity_three_mod_four h1 hd]
    ring
end GlobalTheory
