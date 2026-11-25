-- Prove2me | solution 1 for GlobalTheory.LocTriv.of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:28.768239+00:00
-- url     : https://prove2.me/submissions/b7ba088d-c903-4652-b74b-a252fc555427

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
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
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
variable {R A X : Type} [CommRing R] [CommRing A] [AddCommGroup X]
namespace GlobalTheory.LocTriv
theorem _root_.solution (f : R →+* A) (u : Multiplicative X →* Aˣ)
    (hs : ∀ a : A, ∃ c : X →₀ R, a = c.sum fun χ r => f r * (u (Multiplicative.ofAdd χ)).val)
    (hi : ∀ c : X →₀ R, (c.sum fun χ r => f r * (u (Multiplicative.ofAdd χ)).val) = 0 → c = 0) :
    f.Flat ∧ ∃ σ : A →+* R, σ.comp f = RingHom.id R :=  by
  classical
  letI : Algebra R A := f.toAlgebra
  have hφ : ∀ c : AddMonoidAlgebra R X,
      AddMonoidAlgebra.lift R A X ((Units.coeHom A).comp u) c =
        c.coeff.sum fun χ r => f r * (u (Multiplicative.ofAdd χ)).val :=
    fun c => AddMonoidAlgebra.lift_apply' _ _
  have hbij : Function.Bijective (AddMonoidAlgebra.lift R A X ((Units.coeHom A).comp u)) := by
    refine ⟨?_, fun a => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro c hc
      obtain ⟨c⟩ := c
      have h0 : c = 0 := hi c ((hφ _).symm.trans hc)
      subst h0
      rfl
    · obtain ⟨c, hc⟩ := hs a
      exact ⟨AddMonoidAlgebra.ofCoeff c, (hφ _).trans hc.symm⟩
  let e := AlgEquiv.ofBijective (AddMonoidAlgebra.lift R A X ((Units.coeHom A).comp u)) hbij
  refine ⟨?_, ((AddMonoidAlgebra.lift R R X 1).comp e.symm.toAlgHom).toRingHom, ?_⟩
  · have hfl : Module.Flat R (AddMonoidAlgebra R X) := inferInstance
    have : Module.Flat R A := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
    exact this
  · ext r
    exact ((AddMonoidAlgebra.lift R R X 1).comp e.symm.toAlgHom).commutes r
end GlobalTheory.LocTriv
