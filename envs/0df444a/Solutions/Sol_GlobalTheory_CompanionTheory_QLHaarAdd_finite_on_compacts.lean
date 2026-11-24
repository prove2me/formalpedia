-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLHaarAdd.finite_on_compacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:37.793963+00:00
-- url     : https://prove2.me/submissions/a14d8d12-5d42-4336-88f1-72bd47670ea7

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalized
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLHaarAdd
namespace GlobalTheory.CompanionTheory.QLHaarAdd
theorem _root_.solution {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] {K : Set G} (hKo : IsOpen K) (h0 : (0 : G) ∈ K)
    (dx : Measure G) [dx.IsAddLeftInvariant] (h1 : dx K = 1) : IsFiniteMeasureOnCompacts dx := by
  refine ⟨fun L hL => ?_⟩
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun x : G => (fun y => -x + y) ⁻¹' K)
    (fun x => hKo.preimage (by fun_prop))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using h0⟩)
  have hb : ∀ x : G, dx ((fun y => -x + y) ⁻¹' K) = 1 := fun x => by
    rw [measure_preimage_add dx (-x) K, h1]
  calc dx L ≤ dx (⋃ x ∈ t, (fun y => -x + y) ⁻¹' K) := measure_mono ht
    _ ≤ ∑ x ∈ t, dx ((fun y => -x + y) ⁻¹' K) := measure_biUnion_finset_le t _
    _ < ⊤ := by
      simp only [hb]
      simp [ENNReal.mul_lt_top]
end GlobalTheory.CompanionTheory.QLHaarAdd
