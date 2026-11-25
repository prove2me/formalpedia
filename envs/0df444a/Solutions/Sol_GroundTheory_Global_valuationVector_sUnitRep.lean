-- Prove2me | solution 1 for GroundTheory.Global.valuationVector_sUnitRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:55.762805+00:00
-- url     : https://prove2.me/submissions/87140af8-52e3-45b9-9b67-74ddaa89fd26

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Theorems.Thm_GroundTheory_Global_coe_sUnitMap
import Theorems.Thm_GroundTheory_Global_sUnitRep_apply

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
open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L)))
namespace GroundTheory.Global
theorem _root_.solution (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    (g : L ≃ₐ[K] L) (x : Additive (S.unit L)) :
    letI := stableMulAction S hS
    SUnit.valuationVector S (sUnitRep S hS g x) =
      funPermRep ℤ (L ≃ₐ[K] L) S g (SUnit.valuationVector S x) := by
  let := stableMulAction S hS
  funext w
  rw [funPermRep_apply, ← ofMul_toMul x, sUnitRep_apply, toMul_ofMul,
    SUnit.valuationVector_apply, SUnit.valuationVector_apply]
  congr 1
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq,
    HeightOneSpectrum.valuationOfNeZero_eq, coe_sUnitMap]
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w.1) ((x.toMul : Lˣ) : L)
  rw [smul_inv_smul] at h1
  exact h1
end GroundTheory.Global
