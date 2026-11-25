-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.leibnizR_hasDerivAt_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:21.351304+00:00
-- url     : https://prove2.me/submissions/c8d3036c-5dad-4f83-952c-180eed43e33d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_leibnizL_hasDerivAt_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_right_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_weight_lower_order


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
theorem _root_.solution (H : SqIntegrable D α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l (m + 1) A) (hB : AdmW α cB l (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QR D p m l A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QR D p (m + 1) l A B x y) x := by
  induction l generalizing A B with
  | zero => exact leibnizL_hasDerivAt_left H hA hB hp hx hy
  | succ l ih =>
    have h1 := ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)
    have h2 := ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3
end GlobalTheory.RegularisedIntegral
