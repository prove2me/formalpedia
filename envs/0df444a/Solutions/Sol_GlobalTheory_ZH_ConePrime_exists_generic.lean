-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.exists_generic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:27.889881+00:00
-- url     : https://prove2.me/submissions/3b2728d1-4705-45e0-b1ae-ec24161f1762

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous

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
theorem _root_.solution [IsIntegral X] : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X),
    ∀ U : X.Opens, (U : Set X).Nonempty → ⊤ ≤ y ⁻¹ᵁ U := by
  refine ⟨X.residueField (genericPoint X), inferInstance, X.fromSpecResidueField (genericPoint X),
    fun U hU z _ => ?_⟩
  have : (X.fromSpecResidueField (genericPoint X)) z = genericPoint X :=
    Scheme.fromSpecResidueField_apply _ z
  change (X.fromSpecResidueField (genericPoint X)) z ∈ U
  rw [this]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
end GlobalTheory.ZH.ConePrime
