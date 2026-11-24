-- Prove2me | solution 1 for GlobalTheory.BaseRing.natCast_mul_mem_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:26.355694+00:00
-- url     : https://prove2.me/submissions/bb0016c7-295e-455b-9cd8-6de1d1718444

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmModelCoefficientSubringDedekindCompatibleEmbed
import Theorems.Thm_GlobalTheory_BaseRing_aeval_derivative_mul_mem_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BaseRing
open Polynomial
open IntermediateField
namespace GlobalTheory.BaseRing
theorem _root_.solution (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (T : Subring ℂ) (hT : ∀ w ∈ K, IsIntegral ℤ w → w ∈ T) {ζ : ℂ} {n : ℕ} (hn : 0 < n)
    (hζ : ζ ^ n = 1) (hζT : ζ ∈ T) {z : ℂ} (hzK : z ∈ K⟮ζ⟯) (hz : IsIntegral ℤ z) :
    (n : ℂ) * z ∈ T := by
  have : NumberField K := {}
  let A := integralClosure ℤ K
  have : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension ℚ K
  have : IsIntegrallyClosed A := integralClosure.isIntegrallyClosedOfFiniteExtension ℚ
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow hn (hζ ▸ isIntegral_one)
  have hζK : IsIntegral K ζ := hζi.tower_top
  have : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional hζK
  let x : K⟮ζ⟯ := AdjoinSimple.gen K ζ
  have hx : Algebra.adjoin K {x} = ⊤ := (adjoin.powerBasis hζK).adjoin_gen_eq_top
  have hint : ∀ y : K⟮ζ⟯, IsIntegral ℤ (y : ℂ) → IsIntegral A y := fun y hy =>
    ((isIntegral_algHom_iff (K⟮ζ⟯.val.restrictScalars ℤ) Subtype.val_injective).mp hy).tower_top
  have hxn : x ^ n = 1 := Subtype.ext hζ
  have h := aeval_derivative_mul_mem_adjoin A K hx (hint x hζi) (X ^ n - 1) (by simp [hxn])
    (hint ⟨z, hzK⟩ hz)
  have hsub : ∀ y ∈ Algebra.adjoin A {x}, (y : ℂ) ∈ T := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hζT
    | algebraMap a =>
      exact hT _ a.1.2 ((isIntegral_algHom_iff (K.val.restrictScalars ℤ) Subtype.val_injective).mpr a.2)
    | add a b _ _ ha hb => exact T.add_mem ha hb
    | mul a b _ _ ha hb => exact T.mul_mem ha hb
  have h2 := T.mul_mem hζT (hsub _ h)
  convert h2 using 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hxc : (x : ℂ) = ζ := rfl
  simp [derivative_X_pow, hxc]
  linear_combination (-(m + 1 : ℂ) * z) * hζ
end GlobalTheory.BaseRing
