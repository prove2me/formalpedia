-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.gen_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:21:57.374596+00:00
-- url     : https://prove2.me/submissions/e5fd709c-53c0-41a1-a805-c3bc9753abfc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {D : Type} [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]
omit [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution (B : Subalgebra R D) : Function.Injective (gen R K B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  obtain ⟨⟨b, c⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) x
  have e' := congrArg (gen R K B) e
  rw [map_mul, hx, zero_mul] at e'
  have hb : b = 0 := by
    apply Subtype.ext
    have : gen R K B (algebraMap B _ b) = (b : D) := by
      show gen R K B (1 ⊗ₜ b) = _
      simp [gen]
    rw [← this, ← e']; rfl
  rw [hb, map_zero] at e
  exact (IsLocalization.map_units (TensorProduct R K B) c).mul_left_eq_zero.1 e
end GlobalTheory.SS.WeakNeronEx
