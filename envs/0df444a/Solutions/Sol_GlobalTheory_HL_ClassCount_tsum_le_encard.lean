-- Prove2me | solution 1 for GlobalTheory.HL.ClassCount.tsum_le_encard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:34:21.544584+00:00
-- url     : https://prove2.me/submissions/c1410776-e09e-4fe1-a2e9-9b857873b1e5

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_encard_eq_tsum_fiber
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
namespace GlobalTheory.HL.ClassCount
theorem _root_.solution {G X : Type*} [Group G] [MulAction G X] (H K0 : Subgroup G) (hK : K0 ≤ H)
    (P Q : X → Prop) (w : X → ℝ)
    (hP : ∀ x, P x → ∃ h ∈ H, w x = invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) ∧
      H ⊓ MulAction.stabilizer G (h • x) ≤ K0 ∧ ∀ k ∈ K0, Q (k • h • x)) :
    (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (w o.out) * 1 else 0)
      ≤ (({x | Q x} : Set X).encard : ℝ≥0∞) := by
  rw [encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X)) Q]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  swap
  · exact zero_le
  obtain ⟨h, hh, hw, hle, hQ⟩ := hP _ ho
  have h2 : (H ⊓ MulAction.stabilizer G (h • o.out)).relIndex K0
      = (MulAction.orbit K0 (h • o.out)).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hK hg, a⟩⟩
  have h3 : MulAction.orbit K0 (h • o.out) ⊆
      {x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ Q x} := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨?_, hQ g hg⟩
    conv_rhs => rw [← Quotient.out_eq' o]
    rw [Quotient.eq'', MulAction.orbitRel_apply]
    exact ⟨⟨g * h, mul_mem (hK hg) hh⟩, mul_smul g h o.out⟩
  rw [hw, invVol, Subgroup.relIndex_eq_one.2 hle, h2, Nat.cast_one, div_one, mul_one,
    ENNReal.ofReal_natCast]
  have h4 : ((MulAction.orbit K0 (h • o.out)).ncard : ℕ∞) ≤ _ :=
    (Set.ncard_le_encard _).trans (Set.encard_le_encard h3)
  exact_mod_cast h4
end GlobalTheory.HL.ClassCount
