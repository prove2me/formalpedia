-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_sUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:49.825341+00:00
-- url     : https://prove2.me/submissions/b01f57b1-23bd-4a18-92cd-cbe2e1147402

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_add_of_exact_of_finite_cokernel
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_funPermRep
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_units
import Theorems.Thm_GroundTheory_Global_exact_ofUnits_valuationVector
import Theorems.Thm_GroundTheory_Global_finite_quotient_range_valuationVector
import Theorems.Thm_GroundTheory_Global_ofUnits_unitsRep
import Theorems.Thm_GroundTheory_Global_valuationVector_sUnitRep
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
open GroundTheory.ProfCoh.AdditiveFunction
variable {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (L ≃ₐ[K] L))
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
    (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    letI := sUnitAction S hS
    letI := stableMulAction S hS
    d.g (Additive (S.unit L)) =
      d.toFun (S → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) S) +
        d.toFun (InfinitePlace L → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) (InfinitePlace L)) -
          d.one := by
  let _ := sUnitAction S hS
  let _ := stableMulAction S hS
  let _ := repAction (unitsRep K L)
  let _ := repAction (funPermRep ℤ (L ≃ₐ[K] L) S)
  have : Module.Finite ℤ (Additive (𝓞 L)ˣ) :=
    Module.Finite.of_injective (SUnit.ofUnits (K := L) S).toAdditive.toIntLinearMap
      (fun a b h ↦ SUnit.ofUnits_injective S (congrArg Additive.toMul h))
  have : Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) :=
    finite_quotient_range_valuationVector S
  rw [d.g_eq_add_of_exact_of_finite_cokernel (SUnit.ofUnits (K := L) S).toAdditive
      (SUnit.valuationVector (K := L) S).toAddMonoidHom (fun γ a ↦ ofUnits_unitsRep S hS γ a)
      (fun γ b ↦ valuationVector_sUnitRep S hS γ b)
      (fun a b h ↦ SUnit.ofUnits_injective S (congrArg Additive.toMul h))
      (exact_ofUnits_valuationVector S),
    d.g_units, d.g_funPermRep S]
  ring
end GroundTheory.ProfCoh.AdditiveFunction
