-- Prove2me | solution 1 for GroundTheory.Global.covolume_idealLattice_selfDualMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:19.241806+00:00
-- url     : https://prove2.me/submissions/de4882bc-5ffa-47c1-8ec8-89782a5495d2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ENNReal nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLattice K I) (selfDualMeasure K) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)| := by
  have h := covolume_idealLattice K I
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]
    at h
  have hF : IsAddFundamentalDomain (idealLattice K I)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) (selfDualMeasure K) :=
    (fundamentalDomain_idealLattice K I).mono Measure.smul_absolutelyContinuous
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, selfDualMeasure, measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ← measureReal_def, h, ENNReal.toReal_pow, ENNReal.toReal_ofNat, inv_pow]
  field_simp
end GroundTheory.Global
