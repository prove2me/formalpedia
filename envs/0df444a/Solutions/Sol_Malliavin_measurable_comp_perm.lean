-- Prove2me | solution 1 for Malliavin.measurable_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:18.443223+00:00
-- url     : https://prove2.me/submissions/11e87fcf-ed5a-4ba9-a775-75a3f7fac4e5

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T]
namespace Malliavin
theorem _root_.solution (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Measurable fun t : Fin n → T => t ∘ σ :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)
end Malliavin
