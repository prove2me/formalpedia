-- Prove2me | solution 1 for Malliavin.diagonal_eq_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:50.679672+00:00
-- url     : https://prove2.me/submissions/336d997c-cf33-4dec-8eed-007938f3b647

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_mem_diagonal
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
namespace Malliavin
theorem _root_.solution (n : ℕ) :
    diagonal T n = ⋃ (i : Fin n) (j : Fin n) (_ : i ≠ j), {t : Fin n → T | t i = t j} := by
  ext t
  constructor
  · intro ht
    simp only [mem_diagonal, Function.Injective] at ht
    push Not at ht
    obtain ⟨i, j, hij, hne⟩ := ht
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hne, hij⟩⟩⟩
  · intro ht hinj
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hi
    obtain ⟨hne, hij⟩ := Set.mem_iUnion.1 hj
    exact hne (hinj hij)
end Malliavin
