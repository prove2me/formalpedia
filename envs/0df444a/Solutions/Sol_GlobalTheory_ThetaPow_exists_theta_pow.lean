-- Prove2me | solution 1 for GlobalTheory.ThetaPow.exists_theta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:10.349489+00:00
-- url     : https://prove2.me/submissions/121d94da-f896-4b6f-901e-3cac824f4225

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsThetaPow
import Theorems.Thm_GlobalTheory_ThetaPow_prod_fam_zero
import Theorems.Thm_GlobalTheory_FamFree_exists_sec_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_powSec


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPow
namespace GlobalTheory.ThetaPow
theorem _root_.solution : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∃ (θ : LB.Sec (D.P.L.pull (DegPre.prB D F).left)) (σ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε n))), (∃ j, θ.f j ≠ 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval σ r z J = sval (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left) (ε := fun _ => 1) θ r z J ^ n := by
  intro hT R _ _ D F _ _ n _
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.FamFree.exists_sec_ne_zero (D := D) (F := F) hT (k := 1) le_rfl 0
  have hF₁ : FormEq (DegPre.famφ D F 0) (DegPre.famε 1)
      (fun _ : PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ)) := by
    intro U _ h
    rw [prod_fam_zero D F 1 h]
    simp
  obtain ⟨θ, hθ⟩ := exists_sec D.P.isLB hF₁ s₀
  have hθne : ∃ j, θ.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    have g0 : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), gs f y U 0 = 0 := by
      intro Y X f y U
      unfold gs
      split <;> simp
    apply hs₀
    intro j
    refine (sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j).trans rfl
    rw [← hθ _ (𝟙 _) y J hJ]
    exact ((congrArg (gs _ y _) (hc _)).trans (g0 _ _ _)).trans (g0 _ _ _).symm
  let P := H1.SectionArithmetic.powSec (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left)
    (ε := fun _ => (1 : ℤ)) (fun _ : Fin n => θ)
  have hFn : FormEq (fun p : Fin n × PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ))
      (DegPre.famφ D F 0) (DegPre.famε n) := by
    intro U _ h
    rw [prod_fam_zero D F n h]
    simp
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hFn P
  refine ⟨θ, σ, hθne, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, H1.SectionArithmetic.sval_powSec _ r z hJ]
  simp
end GlobalTheory.ThetaPow
