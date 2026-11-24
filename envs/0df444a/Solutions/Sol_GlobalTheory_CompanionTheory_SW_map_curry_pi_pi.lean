-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.map_curry_pi_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:35:11.294933+00:00
-- url     : https://prove2.me/submissions/b290f590-8f8a-4591-b321-e638285e9c4d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasurableCoordinateMapsTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam] (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
      (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) =
      Measure.pi fun _ : Fin M × Fin d => lam := by
  have hm : Measurable (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) := by
    fun_prop
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : Fin M => Set.univ.pi fun k : Fin d => s (i, k) := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]
end GlobalTheory.CompanionTheory.SW
