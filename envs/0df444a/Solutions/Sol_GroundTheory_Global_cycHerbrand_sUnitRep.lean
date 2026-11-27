-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_sUnitRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:23.573848+00:00
-- url     : https://prove2.me/submissions/bdf67971-e725-4868-a933-595d2066283e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Theorems.Thm_GroundTheory_Global_finite_quotient_range_valuationVector
import Theorems.Thm_GroundTheory_Global_exact_ofUnits_valuationVector
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_mul_of_exact
import Theorems.Thm_GroundTheory_Global_cycHerbrand_funPermRep
import Theorems.Thm_GroundTheory_Global_cycHerbrand_unitsRep
import Theorems.Thm_GroundTheory_Global_hasHerbrandQuotient_cycSubOne_of_finite
import Theorems.Thm_GroundTheory_Global_ofUnits_unitsRep
import Theorems.Thm_GroundTheory_Global_prod_card_stabilizer_finitePlace
import Theorems.Thm_GroundTheory_Global_valuationVector_sUnitRep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MulAction Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
open scoped Classical
namespace GroundTheory.Global
theorem _root_.solution (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (sUnitRep S hS) σ =
      (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
          ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ)) *
        (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  let := stableMulAction S hS
  have : Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S) := Fintype.ofFinite _
  have : Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) :=
    finite_quotient_range_valuationVector S
  have h1 := cycHerbrand_eq_mul_of_exact (unitsRep K L) (sUnitRep S hS)
    (funPermRep ℤ (L ≃ₐ[K] L) S) σ
    (i := (SUnit.ofUnits (K := L) S).toAdditive)
    (p := (SUnit.valuationVector (K := L) S).toAddMonoidHom)
    (fun a b h => SUnit.ofUnits_injective S (congrArg Additive.toMul h))
    (exact_ofUnits_valuationVector S) (fun g a => ofUnits_unitsRep S hS g a)
    (fun g b => valuationVector_sUnitRep S hS g b)
    (hasHerbrandQuotient_cycSubOne_of_finite _ hσ) (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
  rw [h1, cycHerbrand_unitsRep hσ, cycHerbrand_funPermRep hσ,
    prod_card_stabilizer_finitePlace S hS]
  ring
end GroundTheory.Global
