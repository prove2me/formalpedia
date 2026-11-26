-- Prove2me | solution 1 for Malliavin.mem_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:03.723163+00:00
-- url     : https://prove2.me/submissions/8f82f305-3852-4160-907f-0f742de79184

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
namespace Malliavin
theorem _root_.solution {n : ℕ} {t : Fin n → T} : t ∈ diagonal T n ↔ ¬ Function.Injective t :=
  Iff.rfl
end Malliavin
