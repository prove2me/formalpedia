-- Prove2me | solution 1 for Malliavin.injective_of_strictMono_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:41.636803+00:00
-- url     : https://prove2.me/submissions/00853af5-bdab-4c7d-8f03-8947023a4c68

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]
namespace Malliavin
theorem _root_.solution {n : ℕ} {t : Fin n → T} {σ : Equiv.Perm (Fin n)}
    (h : StrictMono (t ∘ σ)) : Function.Injective t := by
  have e : t = (t ∘ σ) ∘ σ.symm := by
    ext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [e]
  exact h.injective.comp σ.symm.injective
end Malliavin
