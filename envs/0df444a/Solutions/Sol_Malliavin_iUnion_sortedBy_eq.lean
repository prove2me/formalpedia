-- Prove2me | solution 1 for Malliavin.iUnion_sortedBy_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:21.531849+00:00
-- url     : https://prove2.me/submissions/0366ea31-7c7f-4861-98cd-79de650ad2db

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_injective_of_strictMono_comp
import Theorems.Thm_Malliavin_exists_strictMono_comp_of_injective

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]
namespace Malliavin
theorem _root_.solution (n : ℕ) :
    ⋃ σ : Equiv.Perm (Fin n), sortedBy T n σ = (diagonal T n)ᶜ := by
  ext t
  constructor
  · intro ht
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 ht
    exact fun h => h (injective_of_strictMono_comp hσ)
  · intro ht
    obtain ⟨σ, hσ⟩ := exists_strictMono_comp_of_injective (not_not.1 ht)
    exact Set.mem_iUnion.2 ⟨σ, hσ⟩
end Malliavin
