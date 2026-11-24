-- Prove2me | solution 1 for GlobalTheory.PowGrp.powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:43.062789+00:00
-- url     : https://prove2.me/submissions/9dbfe123-c4f7-4eb9-bfc0-4016610c5fca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothIsMultiplicative
import Theorems.Thm_GlobalTheory_PowGrp_prop_powObj
import Theorems.Thm_GlobalTheory_PowGrp_exists_iso_powObj
import Theorems.Thm_GlobalTheory_PowGrp_prop_of_isPowGrp
import Theorems.Thm_GlobalTheory_PowGrp_relDim_powObj
import Theorems.Thm_GlobalTheory_PowGrp_geomConnected_of_isIso
import Theorems.Thm_GlobalTheory_PowGrp_geomConnected_powObj
import Theorems.Thm_GlobalTheory_PowGrp_comm_of_isPowGrp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowGrp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
attribute [local instance] smooth_isMultiplicative
namespace GlobalTheory.PowGrp
theorem _root_.solution : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), (Smooth G.hom → Smooth G'.hom) ∧ (IsSeparated G.hom → IsSeparated G'.hom) ∧ (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension (j * g) G'.hom) ∧ (IsAbelianScheme G → IsAbelianScheme G') ∧ (IsSemiAbelian G → IsCommMonObj G') := by
  intro S G' G _ _ j p
  refine ⟨prop_of_isPowGrp @Smooth p, prop_of_isPowGrp @IsSeparated p, fun g hg => ?_, fun hG => ?_,
    fun hG => comm_of_isPowGrp p hG.comm⟩
  · obtain ⟨e, he, hw⟩ := exists_iso_powObj p
    have h1 := relDim_powObj G g hg j
    have h2 : SmoothOfRelativeDimension (0 + j * g) G'.hom := by
      rw [hw]; infer_instance
    rwa [Nat.zero_add] at h2
  · refine ⟨comm_of_isPowGrp p hG.comm, prop_of_isPowGrp @Smooth p hG.smooth,
      prop_of_isPowGrp @IsProper p hG.proper, ?_⟩
    obtain ⟨e, he, hw⟩ := exists_iso_powObj p
    have := hG.smooth
    have := hG.geomConnected
    have := geomConnected_powObj G j
    have : Smooth (powObj G j).hom := prop_powObj @Smooth G ‹_› j
    have := geomConnected_of_isIso e
    rw [hw]
    exact GeometricallyConnected.comp _ _
end GlobalTheory.PowGrp
