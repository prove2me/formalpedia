-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.leibnizL_hasDerivAt_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:33:28.42272+00:00
-- url     : https://prove2.me/submissions/a78dcf66-4885-4c8a-9411-c0dc7e9ceca7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_hasDerivAt_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_left_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_of_succ_left_order


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RegularisedIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {α : ℝ}
namespace GlobalTheory.RegularisedIntegral
theorem _root_.solution (H : SqIntegrable D α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 (m + 1) A) (hB : AdmW α cB 0 (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QL D p m A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QL D p (m + 1) A B x y) x := by
  induction m generalizing A B with
  | zero =>
    exact coef_hasDerivAt_left H (hA.1 0 le_rfl 0 (by omega)) (hA.1 0 le_rfl 1 le_rfl) (hB.1 0 le_rfl 0 (by omega))
      (hB.1 0 le_rfl 1 le_rfl) (hA.2.2 0 le_rfl 0 (by omega)) (hB.2.2 0 le_rfl 0 (by omega)) hp hx hy
  | succ m ih =>
    have h1 := ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)
    have h2 := ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3
end GlobalTheory.RegularisedIntegral
