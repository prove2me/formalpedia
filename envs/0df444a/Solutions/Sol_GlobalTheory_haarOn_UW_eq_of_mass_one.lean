-- Prove2me | solution 1 for GlobalTheory.haarOn_UW_eq_of_mass_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:59:37.562746+00:00
-- url     : https://prove2.me/submissions/a9cb577c-63f2-4b7a-9511-25b40db92edf

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryMeasureDatumProductMeasureEqOfSameVectors
import Theorems.Thm_Formalism_FourierDecayAlt_P_haar_measure_unique_up_to_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_weyl_subgroup_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μ ν : Measure (Mt k r))
    (hμ : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) (hν : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) ν)
    (h1 : μ Set.univ = 1) (h2 : ν Set.univ = 1) : ν = μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ ν (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hμ hν.conc hν.left hν.finite_compact
  have h3 := congrArg (fun m : Measure (Mt k r) => m Set.univ) hc
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h1, h2, mul_one] at h3
  have h4 : c = 1 := by exact_mod_cast h3.symm
  rw [hc, h4, one_smul]
end GlobalTheory
