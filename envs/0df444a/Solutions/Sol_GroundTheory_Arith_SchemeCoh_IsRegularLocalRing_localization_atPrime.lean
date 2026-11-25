-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:21.215787+00:00
-- url     : https://prove2.me/submissions/31e97505-11b1-4840-bbe2-ce75cab5a4a9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_of_hasProjectiveDimensionLT
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_isRegularLocalRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
namespace IsRegularLocalRing
theorem _root_.solution [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim R = d :=
    ⟨_, ((isRegularLocalRing_iff R).mp inferInstance).symm⟩
  have h1 := hasProjectiveDimensionLT_of_isRegularLocalRing hd (R ⧸ p)
  have h2 : HasProjectiveDimensionLE
      ((ModuleCat.of R (R ⧸ p)).localizedModule p.primeCompl) d :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE d p.primeCompl _
  let Rp := Localization.AtPrime p
  let f := Algebra.linearMap R Rp
  let g := (p : Submodule R R).toLocalizedQuotient' Rp p.primeCompl f
  have hl : (p : Submodule R R).localized' Rp p.primeCompl f = maximalIdeal Rp := by
    rw [Ideal.localized'_eq_map, Localization.AtPrime.map_eq_maximalIdeal]
  let e : (Rp ⧸ (p : Submodule R R).localized' Rp p.primeCompl f) ≃ₗ[Rp] Rp ⧸ maximalIdeal Rp :=
    Submodule.quotEquivOfEq _ _ hl
  let g' := (e.restrictScalars R).toLinearMap ∘ₗ g
  have : IsLocalizedModule p.primeCompl g' := IsLocalizedModule.of_linearEquiv _ _ _
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R (R ⧸ p)) p.primeCompl
  let e' := (IsLocalizedModule.linearEquiv p.primeCompl
    ((ModuleCat.of R (R ⧸ p)).localizedModuleMkLinearMap p.primeCompl) g').extendScalarsOfIsLocalization
    p.primeCompl Rp
  have h3 : HasProjectiveDimensionLT (ModuleCat.of Rp (Rp ⧸ maximalIdeal Rp)) (d + 1) :=
    hasProjectiveDimensionLT_of_iso e'.toModuleIso (d + 1)
  exact isRegularLocalRing_of_hasProjectiveDimensionLT d h3
end IsRegularLocalRing
end GroundTheory.Arith.SchemeCoh
