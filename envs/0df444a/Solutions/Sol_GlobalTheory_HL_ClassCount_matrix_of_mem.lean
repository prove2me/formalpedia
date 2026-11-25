-- Prove2me | solution 1 for GlobalTheory.HL.ClassCount.matrix_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:20.7278+00:00
-- url     : https://prove2.me/submissions/10a72b24-0760-40ff-8d44-b78fba409c73

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumClsLeEncard
import Theorems.Thm_GlobalTheory_HL_ClassCount_smul_span
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FlagUnipotent_main
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_main
import Theorems.Thm_GlobalTheory_HL_StabConj_main
import Theorems.Thm_GlobalTheory_PowMulMemOrder_main
import Theorems.Thm_GlobalTheory_PowSmulMem_main
import Theorems.Thm_GlobalTheory_T_frames_commonStabiliser_eq_pairingMatrix_stabiliser
import Theorems.Thm_GlobalTheory_T_hermitianFrames_pairingStabilizer_blockDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ClassCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
  {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.ClassCount
theorem _root_.solution {g : S.GLV} (hg : g ∈ S.K0) :
    ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s ∧ IsUni s' ∧ IsIntM L s ∧
      (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) ∧
      (∀ j, g (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, g (S.f' j) = ∑ i, s' i j • S.f' i := by
  obtain ⟨s, hs, e⟩ := (FrameOnto.unipotent_onto L r k S).1 g hg.1.1.1
  obtain ⟨s', hs', e'⟩ := (FrameOnto.unipotent_onto L r k S).2.1 g hg.1.1.2
  have hz := ((GlobalTheory.T.frames_commonStabiliser_eq_pairingMatrix_stabiliser L r k S).2 s s' hs hs').2 ⟨g, hg.1.1, e, e'⟩
  have hb := ((GlobalTheory.T.hermitianFrames_pairingStabilizer_blockDiagonal L r k S).1 s s' hs hs' hz).1
  refine ⟨s, s', hs, hs', fun i j => ?_, fun i j h => (hb i j h).1, e, e'⟩
  have h1 : g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := hg.1.2
  rw [smul_span] at h1
  have h2 : g (S.f j) ∈ Submodule.span L.O (Set.range S.f) :=
    h1 ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have li : LinearIndependent E S.f :=
    (GlobalTheory.FrameBasic.main L r k S).1.comp Sum.inl Sum.inl_injective
  have h3 := Fintype.linearIndependent_iff.1 li (fun i => s i j - c i) (by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← e j, ← hc]
    exact sub_self _) i
  rw [sub_eq_zero.1 h3]
  exact (c i).2
end GlobalTheory.HL.ClassCount
