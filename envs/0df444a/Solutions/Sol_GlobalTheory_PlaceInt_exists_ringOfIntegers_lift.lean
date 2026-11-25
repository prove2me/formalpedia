-- Prove2me | solution 1 for GlobalTheory.PlaceInt.exists_ringOfIntegers_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:36.738396+00:00
-- url     : https://prove2.me/submissions/f1b09263-f4ac-4ebf-b917-7b58f5c0cebd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_PlaceIdem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRingOfIntegersLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PlaceInt
open NumberField
namespace GlobalTheory.PlaceInt
namespace _root_.GlobalTheory.PlaceInt
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (V : Type) [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] (k : Type) [Field k] [Algebra V k] [IsFractionRing V k]
    (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by
  have inj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  have hint : ∀ x : 𝓞 E, ∃ y : V, algebraMap V k y = ψ (x : E) := by
    intro x
    have h1 : IsIntegral ℤ (ψ (x : E)) := x.isIntegral_coe.map ψ.toIntAlgHom
    have h2 : IsIntegral V (ψ (x : E)) := h1.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  choose f hf using hint
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one]; simp)
            map_mul' := fun x y => inj (by rw [map_mul, hf, hf, hf]; push_cast; rw [map_mul])
            map_zero' := inj (by rw [hf, map_zero]; simp)
            map_add' := fun x y => inj (by rw [map_add, hf, hf, hf]; push_cast; rw [map_add]) },
    hf⟩
end _root_.GlobalTheory.PlaceInt
end GlobalTheory.PlaceInt
