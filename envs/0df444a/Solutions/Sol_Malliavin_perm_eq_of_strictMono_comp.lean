-- Prove2me | solution 1 for Malliavin.perm_eq_of_strictMono_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:23.28141+00:00
-- url     : https://prove2.me/submissions/3e62c81e-a8fc-4edd-8e39-d0d9dc91dc4d

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_IsSymmetric_comp_left

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]
namespace Malliavin
theorem _root_.solution {n : ℕ} {t : Fin n → T} (ht : Function.Injective t)
    {σ τ : Equiv.Perm (Fin n)} (hσ : StrictMono (t ∘ σ)) (hτ : StrictMono (t ∘ τ)) : σ = τ := by
  have hrange : Set.range (t ∘ σ) = Set.range (t ∘ τ) := by
    rw [σ.surjective.range_comp, τ.surjective.range_comp]
  have h : t ∘ σ = t ∘ τ := (hσ.range_inj hτ).1 hrange
  exact Equiv.coe_fn_injective (ht.comp_left h)
end Malliavin
