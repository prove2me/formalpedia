-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.Graded.mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:44.251289+00:00
-- url     : https://prove2.me/submissions/aea65756-3eb7-4746-9891-fab89dfb9509

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Theorems.Thm_GlobalTheory_TorusQuotientLift_Graded_map_eq
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_add
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_mul
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_add
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_zero
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_isWt_zero
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}
namespace GlobalTheory.TorusQuotientLift
namespace Graded
theorem _root_.solution (h : Graded i V) {A : Type} [CommRing A] (J : Ideal A) (α : A →+* wtZero i V)
    (x : wtZero i V) (hx : x.1 ∈ J.map ((wtZero i V).subtype.comp α)) : x ∈ J.map α := by
  classical
  have key : ∀ y ∈ J.map ((wtZero i V).subtype.comp α), ∀ c, ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧
      c * y = (a.sum fun _ x => x) ∧ ∃ z ∈ J.map α, z.1 = a 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro c
      obtain ⟨a, ha, rfl⟩ := h.1 c
      refine ⟨a.mapRange (· * (α r).1) (zero_mul _), fun χ => ?_, ?_, ⟨a 0, ha 0⟩ * α r,
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem α hr), rfl⟩
      · simpa using IsWt.mul (ha χ) (α r).2
      · rw [Finsupp.sum_mapRange_index (fun _ => rfl), Finsupp.sum_mul]
        rfl
    | zero => exact fun c => ⟨0, isWt_zero, by simp, 0, zero_mem _, rfl⟩
    | add y y' _ _ H H' =>
      intro c
      obtain ⟨a, ha, e, z, hz, f⟩ := H c
      obtain ⟨a', ha', e', z', hz', f'⟩ := H' c
      refine ⟨a + a', fun χ => (ha χ).add (ha' χ), ?_, z + z', add_mem hz hz', congrArg₂ (· + ·) f f'⟩
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), mul_add, e, e']
    | smul d y _ H =>
      intro c
      rw [smul_eq_mul, ← _root_.mul_assoc]
      exact H _
  obtain ⟨a, ha, e, z, hz, f⟩ := key _ hx 1
  rw [_root_.one_mul] at e
  have := h.map_eq (RingHom.id _) (fun _ _ h => h) ha (χ := 0) (by rw [← e]; exact x.2)
  rwa [show x = z from Subtype.ext (e.trans (this.symm.trans f.symm))]
end Graded
end GlobalTheory.TorusQuotientLift
