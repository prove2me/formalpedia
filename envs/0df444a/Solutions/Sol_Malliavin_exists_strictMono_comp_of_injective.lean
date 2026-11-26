-- Prove2me | solution 1 for Malliavin.exists_strictMono_comp_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:45.791503+00:00
-- url     : https://prove2.me/submissions/db2f3898-534d-4699-a8b0-2be734768be5

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]
namespace Malliavin
theorem _root_.solution {n : ℕ} {t : Fin n → T}
    (ht : Function.Injective t) : ∃ σ : Equiv.Perm (Fin n), StrictMono (t ∘ σ) :=
  ⟨Tuple.sort t,
    (Tuple.monotone_sort t).strictMono_of_injective (ht.comp (Tuple.sort t).injective)⟩
end Malliavin
