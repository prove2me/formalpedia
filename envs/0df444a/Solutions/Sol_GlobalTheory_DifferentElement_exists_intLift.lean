-- Prove2me | solution 1 for GlobalTheory.DifferentElement.exists_intLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:51.529403+00:00
-- url     : https://prove2.me/submissions/0ea06609-b92f-4d4a-a495-2ef4c27480d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.DifferentElement
namespace GlobalTheory.DifferentElement
theorem _root_.solution (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (k : Type) [Field k] [Algebra V k] [IsFractionRing V k] (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by
  have hinj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  have h : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (x : E) := by
    intro x
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    have h1 : IsIntegral ℤ (ψ (x : E)) := (RingOfIntegers.isIntegral_coe x).map ψ.toIntAlgHom
    exact h1.tower_top
  choose s hs using h
  refine ⟨{ toFun := s, map_one' := hinj ?_, map_mul' := fun x y => hinj ?_,
            map_zero' := hinj ?_, map_add' := fun x y => hinj ?_ }, hs⟩
  · rw [hs]; simp
  · rw [map_mul, hs, hs, hs]; simp
  · rw [hs]; simp
  · rw [map_add, hs, hs, hs]; simp
end GlobalTheory.DifferentElement
