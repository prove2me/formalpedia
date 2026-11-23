-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.valHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:28.870901+00:00
-- url     : https://prove2.me/submissions/f1dc0776-6f2f-4774-a358-d4d88540291a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_isUnit_valR_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k : Type} [Field k] {X : Scheme.{0}}
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution [IsIntegral X] {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∀ U : X.Opens, (U : Set X).Nonempty → ⊤ ≤ y ⁻¹ᵁ U) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    Function.Injective (valHom y U h) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra h0
  have hne : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hb
    exact h0 ((basicOpen_eq_bot_iff f).1 (TopologicalSpace.Opens.ext hb))
  have := (isUnit_valR_iff y U h f).2 (hy _ hne)
  rw [valR_eq y U h, hf] at this
  exact not_isUnit_zero this
end GlobalTheory.ZH.ConePrime
