-- Prove2me | solution 1 for GlobalTheory.exists_hom_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:35.441989+00:00
-- url     : https://prove2.me/submissions/b19b0c8d-81b8-4c95-a0ff-d8cec2687ab4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEmbeddingOfHomogeneousKerEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {P L M : Type} [CommRing P] [Field L] [Field M]
    (Φ : P →+* L) (Ψ : P →+* M) (h : RingHom.ker Φ = RingHom.ker Ψ) :
    ∃ (S : Subfield L) (e : S →+* M), ∃ hS : ∀ p, Φ p ∈ S, ∀ p, e ⟨Φ p, hS p⟩ = Ψ p := by
  haveI : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime Φ
  let Q := P ⧸ RingHom.ker Φ
  let f1 : Q →+* L := RingHom.kerLift Φ
  have hf1 : Function.Injective f1 := RingHom.kerLift_injective Φ
  let f2 : Q →+* M := Ideal.Quotient.lift _ Ψ (fun a ha => by
    rw [h] at ha; exact ha)
  have hf2 : Function.Injective f2 :=
    RingHom.lift_injective_of_ker_le_ideal _ _ h.ge
  let i1 : FractionRing Q →+* L := IsFractionRing.lift hf1
  let i2 : FractionRing Q →+* M := IsFractionRing.lift hf2
  have h1 : ∀ p, i1 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Φ p := fun p => by
    simp only [i1, IsFractionRing.lift_algebraMap]
    exact RingHom.kerLift_mk Φ p
  have h2 : ∀ p, i2 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Ψ p := fun p => by
    simp only [i2, IsFractionRing.lift_algebraMap]
    rfl
  refine ⟨i1.fieldRange, i2.comp i1.rangeRestrictFieldEquiv.symm.toRingHom,
    fun p => ⟨_, h1 p⟩, fun p => ?_⟩
  have : i1.rangeRestrictFieldEquiv.symm ⟨Φ p, ⟨_, h1 p⟩⟩
      = algebraMap Q _ (Ideal.Quotient.mk _ p) := by
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (h1 p).symm
  rw [← h2 p, ← this]
  rfl
end GlobalTheory
