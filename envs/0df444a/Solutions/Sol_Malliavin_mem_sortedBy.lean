-- Prove2me | solution 1 for Malliavin.mem_sortedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:04.53498+00:00
-- url     : https://prove2.me/submissions/64a3505a-cd76-4214-957e-95479cad5268

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
theorem _root_.solution {n : ℕ} {σ : Equiv.Perm (Fin n)} {t : Fin n → T} :
    t ∈ sortedBy T n σ ↔ StrictMono (t ∘ σ) :=
  Iff.rfl
end Malliavin
