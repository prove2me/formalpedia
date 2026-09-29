-- Prove2me | solution 1 for NumberField.FiniteSIdele.isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8eca125a-9bda-55fc-9b96-27c124496301

import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import Theorems.Thm_GroupCohomology_RepPi_isZero_groupCohomology_obj
import Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_FiniteSIdele_isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (V : Set (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∈ V → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (n : ℕ) :
    Limits.IsZero (groupCohomology (GroupCohomology.RepPi.obj fun v : V =>
      Rep.coind (NumberField.FiniteSIdele.D E K v.1).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v.1)) (n + 1)) := by
  classical
  refine GroupCohomology.RepPi.isZero_groupCohomology_obj _ (n + 1) (fun v => ?_)

  refine Limits.IsZero.of_iso ?_ (groupCohomology.coindIso (NumberField.FiniteSIdele.localIntegerUnits E K v.1) (n + 1))

  have hw : ((NumberField.PlaceAbove.above E K v.1).under (𝓞 E)).asIdeal.ramificationIdx' (NumberField.PlaceAbove.above E K v.1).asIdeal = 1 :=
    hunr _ (by rw [show (NumberField.PlaceAbove.above E K v.1).under (𝓞 E) = v.1 from HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E K v.1)]; exact v.2)
  letI : Fintype (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v.1)) := Fintype.ofFinite _
  have hsub := NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one E K
    (NumberField.PlaceAbove.above E K v.1) hw ((n + 1 : ℕ) : ℤ)
  rw [Rep.tateCohomology_ofNat_succ] at hsub
  exact ModuleCat.isZero_of_subsingleton _

end S_NumberField_FiniteSIdele_isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_FiniteSIdele_isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one (solution)
