-- Prove2me | solution 1 for GlobalTheory.KS.Exist.fderiv_const_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:17.389919+00:00
-- url     : https://prove2.me/submissions/8370046c-476c-42dc-bebc-cc82f583fe16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationAlongFibreOfSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticKodairaSpencerClass
import Theorems.Thm_GlobalTheory_KS_Exist_ex_hom
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Exist
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
  (m : A₀.left ⟶ X)
namespace GlobalTheory.KS.Exist
theorem _root_.solution {R : Type} [CommRing R] {x₀ : R →+* ℂ} {p : X ⟶ Sp R} (hm : m ≫ p = A₀.hom ≫ spMap x₀)
    (r : R) (z w : Fin g → ℂ) : fderiv ℂ (fn u m ⊤ (constFn p ⊤ r)) z w = 0 := by
  have : fn u m ⊤ (constFn p ⊤ r) =
      fun _ => valAt' (spMap x₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    funext y
    refine (valAt'_appLE _ p ⊤ ⊤ le_top _ le_top).trans ?_
    rw [Category.assoc, hm, ← Category.assoc, ex_hom]
    exact congrArg (fun x => valAt' x ⊤ _) (Category.id_comp _)
  rw [this]
  simp
end GlobalTheory.KS.Exist
