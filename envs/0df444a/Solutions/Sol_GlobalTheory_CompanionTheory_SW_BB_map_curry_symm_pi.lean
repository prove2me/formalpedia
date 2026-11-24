-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.map_curry_symm_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:18:22.109846+00:00
-- url     : https://prove2.me/submissions/262a00b8-cf5c-4b9e-afee-af07d5f24893

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB
theorem _root_.solution {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
        (MeasurableEquiv.curry (Fin M) (Fin d) R).symm =
      Measure.pi fun _ : Fin M × Fin d => lam := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.curry (Fin M) (Fin d) R).symm.map_apply]
  have hpre : (MeasurableEquiv.curry (Fin M) (Fin d) R).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i : Fin M => Set.pi Set.univ fun k : Fin d => s (i, k) := by
    ext x
    simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall, Function.uncurry]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]
end GlobalTheory.CompanionTheory.SW.BB
