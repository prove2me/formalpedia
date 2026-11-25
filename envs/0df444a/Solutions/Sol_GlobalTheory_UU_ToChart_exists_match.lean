-- Prove2me | solution 1 for GlobalTheory.UU.ToChart.exists_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:35:27.582807+00:00
-- url     : https://prove2.me/submissions/dda964bb-128a-481e-aca8-d6def48546fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
import Theorems.Thm_GlobalTheory_UU_ToChart_w_compat
import Theorems.Thm_GlobalTheory_UU_ToChart_w_rig
import Theorems.Thm_GlobalTheory_UU_ToChart_w_even
import Theorems.Thm_GlobalTheory_UU_ToChart_w_cub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ToChart
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)
namespace GlobalTheory.UU.ToChart
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G), ∃ U' : UnifPre I D A G, Match U U' :=
  fun _ _ _ _ _ _ _ _ _ U =>
    ⟨{ smooth := U.semi.smooth
       separated := U.semi.separated
       gen := U.gen
       gen_hom := U.gen_hom
       LG := U.P.L
       cubG := U.P.c
       symG := U.P.sym
       symG_gen := U.P.sym_gen
       symG_rig := U.P.sym_rig
       ext := ⟨U.wA, U.wA_gen⟩
       gt := U.gt
       gt_q := U.gt_q
       gt_t := U.gt_t
       w := U.w
       w_gen := U.w_gen
       w_rig := w_rig U
       w_even := w_even U
       w_cub := w_cub U
       w_compat := w_compat U }, ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩⟩
end GlobalTheory.UU.ToChart
