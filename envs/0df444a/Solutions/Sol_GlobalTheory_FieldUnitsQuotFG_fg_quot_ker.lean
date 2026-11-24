-- Prove2me | solution 1 for GlobalTheory.FieldUnitsQuotFG.fg_quot_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:24.176392+00:00
-- url     : https://prove2.me/submissions/4d3300ea-a862-4b80-a567-5b07c39749a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.FieldUnitsQuotFG
namespace GlobalTheory.FieldUnitsQuotFG
theorem _root_.solution {G S : Type} [CommGroup G] [Finite S] (φ : G →* (S → Multiplicative ℤ)) :
    Group.FG (G ⧸ φ.ker) := by
  let e : (S → ℤ) ≃+ Additive (S → Multiplicative ℤ) :=
    { toFun := fun f => Additive.ofMul (fun v => Multiplicative.ofAdd (f v))
      invFun := fun g v => Multiplicative.toAdd (Additive.toMul g v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : Module.Finite ℤ (Additive (S → Multiplicative ℤ)) := Module.Finite.equiv e.toIntLinearEquiv
  have h1 : φ.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (Subgroup.toAddSubgroup φ.range)]
    exact (Submodule.fg_iff_addSubgroup_fg _).1 (IsNoetherian.noetherian _)
  haveI : Group.FG φ.range := (Group.fg_iff_subgroup_fg _).2 h1
  exact Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom)
    (QuotientGroup.quotientKerEquivRange φ).symm.surjective
end GlobalTheory.FieldUnitsQuotFG
