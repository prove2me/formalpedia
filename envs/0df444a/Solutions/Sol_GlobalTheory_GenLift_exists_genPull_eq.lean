-- Prove2me | solution 1 for GlobalTheory.GenLift.exists_genPull_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:23:37.292851+00:00
-- url     : https://prove2.me/submissions/2016fa0c-1992-44a3-8608-ea7bc4b039ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Theorems.Thm_GlobalTheory_GenLift_pullSec_surjective
import Theorems.Thm_GlobalTheory_GenLift_isUnit_of_isUnit_app
import Theorems.Thm_GlobalTheory_LB_globalEquiv_pullSec_f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenLift
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.GenLift
theorem _root_.solution (f : Y ⟶ X) [IsClosedImmersion f] [Surjective f] [IsAffine X]
    {L : LB X} (hL : L.IsLB) (t₀ : LB.Gen (L.pull f)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen L, t.IsGen ∧ LB.genPull L t f = t₀ := by
  obtain ⟨σ, hσ⟩ := pullSec_surjective f hL (ofSec (genSec t₀ ht₀) _)
  obtain ⟨s, rfl⟩ := (globalEquiv L).symm.surjective σ
  have e : ∀ j : (L.pull f).ι,
      (f.appLE _ _ (pull_U_le f j)).hom (s.f (j PUnit.unit)) = (t₀.s j).val := fun j => by
    rw [← globalEquiv_pullSec_f f s j]
    exact congrArg (fun z : LB.Sec (L.pull f) => z.f j)
      ((congrArg (globalEquiv (L.pull f)) hσ).trans
        ((globalEquiv (L.pull f)).apply_symm_apply (genSec t₀ ht₀)))
  have hu : ∀ i, IsUnit (s.f i) := fun i => by
    refine isUnit_of_isUnit_app f _ ?_
    have h := ((e fun _ => i).symm ▸ (t₀.s fun _ => i).isUnit :
      IsUnit ((f.appLE _ _ (pull_U_le f fun _ => i)).hom (s.f i))).map
      (resG Y (pull_U f fun _ => i).ge)
    rwa [resG_appLE, Scheme.Hom.appLE_eq_app] at h
  refine ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j), ?_⟩
  cases t₀ with | mk t₀ => ?_
  exact congrArg LB.Gen.mk (funext fun j => Units.ext (e j))
end GlobalTheory.GenLift
