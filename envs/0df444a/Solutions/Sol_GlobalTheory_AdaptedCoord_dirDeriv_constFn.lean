-- Prove2me | solution 1 for GlobalTheory.AdaptedCoord.dirDeriv_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:04.43484+00:00
-- url     : https://prove2.me/submissions/e89023be-f691-48d5-bf9e-6fa340fa3348

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Theorems.Thm_GlobalTheory_AdaptedCoord_ex_comp
import Theorems.Thm_GlobalTheory_AdaptedCoord_eventually_le
import Theorems.Thm_GlobalTheory_AdaptedCoord_dirDeriv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
namespace AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
private theorem valAt'_constFn_of_comp_eq_id {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : x ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : ℂ) : valAt' x U (constFn p U a) = a := by
  have key : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ q.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
        𝟙 _ := by
    rintro q e rfl
    simp [Scheme.Hom.appLE]
    erw [CategoryTheory.Functor.map_id]
    simp
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ p.appLE ⊤ U (show U ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) ≫
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE_assoc]
    exact key _ _ hp
  rw [valAt', dif_pos h]
  exact congrArg (fun φ => φ.hom a) hcomp
end AdaptedCoord
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.AdaptedCoord
theorem _root_.solution {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) (a : ℂ) :
    dirDeriv u h w (constFn A.hom U a) = 0 := by
  rw [dirDeriv_apply]
  have hev : (fun z => valAt' (u.ex z).left U (constFn A.hom U a)) =ᶠ[𝓝 0] fun _ => a := by
    filter_upwards [eventually_le u h] with z hz
    exact valAt'_constFn_of_comp_eq_id _ _ (ex_comp u z) U hz a
  rw [hev.fderiv_eq]
  simp
end GlobalTheory.AdaptedCoord
