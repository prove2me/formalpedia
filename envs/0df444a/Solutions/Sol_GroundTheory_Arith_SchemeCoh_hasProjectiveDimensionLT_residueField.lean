-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:12.653794+00:00
-- url     : https://prove2.me/submissions/f782851e-c271-46b5-9c0a-b5e1d77494f7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_isRegular_ofList_eq_maximalIdeal

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
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]
open CategoryTheory Abelian
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) :
    HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (d + 1) := by
  obtain ⟨rs, hreg, hof, hlen⟩ := exists_isRegular_ofList_eq_maximalIdeal (R := R)
  have hrs : rs.length = d := by rw [hd] at hlen; exact_mod_cast hlen
  have h := ModuleCat.projectiveDimension_quotient_eq_length.{u} (R := R) rs hreg
  have h' : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{u} (R ⧸ ofList rs))) d :=
    (projectiveDimension_le_iff _ d).mp (by rw [h, hrs])
  let e : Shrink.{u} (R ⧸ ofList rs) ≃ₗ[R] R ⧸ maximalIdeal R :=
    (Shrink.linearEquiv R _).trans (Submodule.quotEquivOfEq _ _ hof)
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso (d + 1)
end GroundTheory.Arith.SchemeCoh
