-- Prove2me | solution 1 for GlobalTheory.KS.Exist.fderiv_field_hol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:22.29521+00:00
-- url     : https://prove2.me/submissions/6131f11a-dbe8-4509-8d8d-01970276fdb9

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
import Theorems.Thm_GlobalTheory_KS_Exist_dom_open
import Theorems.Thm_GlobalTheory_KS_Exist_fn_hol
import Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_mul
import Theorems.Thm_GlobalTheory_cauchyRiemann_iff_differentiableOn_complex


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
variable {R : Type} [CommRing R] {p : X ⟶ Sp R} {D : R → ℂ} {W₀ : X.Opens}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)}
namespace GlobalTheory.KS.Exist
theorem _root_.solution (W : X.Opens) (f : Γ(X, W)) {S : Set (Fin g → ℂ)} (hS : S ⊆ dom u m W)
    (h : Fin g → (Fin g → ℂ) → ℂ) (hh : ∀ a, DifferentiableOn ℂ (h a) S) :
    DifferentiableOn ℂ (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) S := by
  have e : (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) =
      fun z => ∑ a, h a z * fderiv ℂ (fn u m W f) z (Pi.single a 1) := by
    funext z
    conv_lhs => rw [show (fun a => h a z) = ∑ a, h a z • (Pi.single a 1 : Fin g → ℂ) from
      (pi_eq_sum_univ' _)]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [e]
  refine DifferentiableOn.fun_sum fun a _ => (hh a).mul ?_
  exact (((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ _ (dom_open u m W)).2 (fn_hol u m W f)).2 _).mono hS
end GlobalTheory.KS.Exist
