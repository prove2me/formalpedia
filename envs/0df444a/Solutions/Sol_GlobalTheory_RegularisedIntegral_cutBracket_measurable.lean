-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.cutBracket_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:36.847368+00:00
-- url     : https://prove2.me/submissions/1d52ff52-e9ec-4ee2-9be8-246a4cbd65c3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_leibnizR_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_square_product_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_measurableSet_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regBracket_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_stronglyMeasurable_indicator_of_continuousOn__0708fc44554f


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
theorem _root_.solution (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') : StronglyMeasurable (Bt D F F') := by
  refine stronglyMeasurable_indicator_of_continuousOn' ((measurableSet_inSS D).prod (measurableSet_Ioi.prod measurableSet_Ioi)) ?_
  have e : (fun q : SS k r × (ℝ × ℝ) => regBracket D F F' q.1 q.2.1 q.2.2) =
      fun q => ((Wd D q.2.1 * Wd D q.2.2 : ℝ) : ℂ) * QR D q.1 0 0 F F' q.2.1 q.2.2 :=
    funext fun q => regBracket_eq D F F' q.1 q.2.1 q.2.2
  rw [e]
  exact ((cutoff_square_product_continuous D).comp continuous_snd).continuousOn.mul
    (leibnizR_continuousOn H (admissibleWeight_mono hF (by omega) (by omega)) (admissibleWeight_mono hF' (by omega) (by omega)))
end GlobalTheory.RegularisedIntegral
