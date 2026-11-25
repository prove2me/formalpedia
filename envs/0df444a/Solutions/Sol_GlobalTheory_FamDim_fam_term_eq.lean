-- Prove2me | solution 1 for GlobalTheory.FamDim.fam_term_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:16.281747+00:00
-- url     : https://prove2.me/submissions/71a40808-be1e-49ab-9c5c-59c08b6f33e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTermBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamDim
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
  [Algebra (FractionRing R) F] {k : ℕ}
namespace GlobalTheory.FamDim
theorem _root_.solution (hG : GlobalFnsSt) {s t : Fam D F k} {ρ : D.X} (h : s.s ρ = t.s ρ) (mu : D.X) (j) :
    (s.s (ρ + k • mu)).f j = (t.s (ρ + k • mu)).f j := by
  have hL := D.P.isLB
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG k mu ρ).1
  refine sec_ext_val hL (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu ρ u hu hc) _ _ y J hJ,
    (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (t.fe mu ρ u hu hc) _ _ y J hJ, h]
end GlobalTheory.FamDim
