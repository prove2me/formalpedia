-- Prove2me | solution 1 for Malliavin.disjoint_sortedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:20.023729+00:00
-- url     : https://prove2.me/submissions/0a3fe27d-4a2f-4b3e-9e11-b4b755b9fdbd

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_injective_of_strictMono_comp
import Theorems.Thm_Malliavin_perm_eq_of_strictMono_comp

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]
namespace Malliavin
theorem _root_.solution {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : σ ≠ τ) :
    Disjoint (sortedBy T n σ) (sortedBy T n τ) := by
  rw [Set.disjoint_left]
  intro t hσ hτ
  exact h (perm_eq_of_strictMono_comp (injective_of_strictMono_comp hσ) hσ hτ)
end Malliavin
