-- Prove2me | solution 1 for GlobalTheory.PhiPull.cub_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:02:35.969892+00:00
-- url     : https://prove2.me/submissions/2978010e-845e-48a7-92a6-690439f88345

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cub_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


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
noncomputable section
open GlobalTheory
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.PhiPull
theorem _root_.solution (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {T' : Over (Spec (CommRingCat.of R'))} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ)
    (hΩ : Ω = fun x => gw hD.w x.left z (J (x.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' x.left))
    (a b c : T' ⟶ D'.P.A) :
    @Eq (T'.left.presheaf.stalk z)ˣ (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' a)
      (pushHom (pull_grp hD) T' b) (pushHom (pull_grp hD) T' c))
      (Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' z J' a b c) := by
  subst hΩ
  have e := cub_pull hG hD (T' := T') hJ hJ' a b c
  have q : (lift a (lift b c)).left ≫ (cubeMapOf (pull_grp hD)).F3 = (lift (pushHom (pull_grp hD) T' a)
      (lift (pushHom (pull_grp hD) T' b) (pushHom (pull_grp hD) T' c))).left :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
  rw [q] at e
  exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q z
    (J (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' q))) rfl)
end GlobalTheory.PhiPull
