-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.crossingCount_fromPairing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:49:30.667571+00:00
-- url     : https://prove2.me/submissions/6571e78e-a3d3-45bc-b5e2-745d75f5cadd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatchingConversion.lean:L89-L102
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.crossingCount_fromPairing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion__MatchingAffineLift

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingConversion ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing
attribute [local instance] Classical.propDecidable

lemma pairingEdge_cross {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n))
    (v : Fin n) (hv : v ∈ U) (hp : M.1 v ∉ U) : Crosses U (pairingEdge M v) := by
  unfold pairingEdge
  split_ifs <;> simp [Crosses, hv, hp]

lemma cross_edge_inside {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n))
    (e : Edge n) (he : e ∈ (fromPairing M).1) (hc : Crosses U e) :
    ∃ v : Fin n, (v ∈ U ∧ M.1 v ∉ U) ∧ pairingEdge M v = e := by
  have hm := (mem_fromPairing M e).mp he
  rcases hc with hc | hc
  · refine ⟨e.1.1,⟨hc.1,?_⟩,(eq_pairingEdge M e hm _ (Or.inl rfl)).symm⟩
    simpa only [hm] using hc.2
  · refine ⟨e.1.2,⟨hc.2,?_⟩,(eq_pairingEdge M e hm _ (Or.inr rfl)).symm⟩
    simpa only [← hm, M.partner_partner] using hc.1

lemma pairingEdge_inside_injective {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    Function.Injective (fun v : {v : Fin n // v ∈ U ∧ M.1 v ∉ U} => pairingEdge M v.1) := by
  intro v w h
  apply Subtype.ext
  have hv := pairingEdge_incident M v.1
  have hw := pairingEdge_incident M w.1
  change pairingEdge M v.1 = pairingEdge M w.1 at h
  rw [← h] at hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact hv.symm.trans hw
  · have hm := pairingEdge_mem M v.1
    rw [hv,hw] at hm
    exact False.elim (v.2.2 (hm ▸ w.2.1))
  · have hm := pairingEdge_mem M v.1
    rw [hw,hv] at hm
    exact False.elim (w.2.2 (hm ▸ v.2.1))
  · exact hv.symm.trans hw

lemma crossingCount_fromPairing {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    crossingCount U (fromPairing M) = Fintype.card {v : Fin n // v ∈ U ∧ M.1 v ∉ U} := by
  classical
  rw [crossingCount, ← Fintype.card_coe]
  symm
  apply Fintype.card_of_bijective (f := fun v : {v : Fin n // v ∈ U ∧ M.1 v ∉ U} =>
    (⟨pairingEdge M v.1,by simp [pairingEdge_mem, pairingEdge_cross M U v.1 v.2.1 v.2.2]⟩ :
      {e // e ∈ (fromPairing M).1.filter (Crosses U)}))
  constructor
  · intro v w h
    exact pairingEdge_inside_injective M U (congrArg Subtype.val h)
  · intro e
    obtain ⟨v,hv,he⟩ := cross_edge_inside M U e.1 (Finset.mem_filter.mp e.2).1 (Finset.mem_filter.mp e.2).2
    exact ⟨⟨v,hv⟩,Subtype.ext he⟩

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.crossingCount_fromPairing := @_root_.OAI.PerfectMatchingPSD.crossingCount_fromPairing
