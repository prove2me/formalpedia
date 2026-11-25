-- Prove2me | solution 1 for GlobalTheory.HL.ClassCount.sumCls_le_encard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:35.032318+00:00
-- url     : https://prove2.me/submissions/b40179e3-fb6d-4fd6-a3e8-5ab398d35689

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
import Theorems.Thm_GlobalTheory_HL_ClassCount_tsum_le_encard
import Theorems.Thm_GlobalTheory_HL_ClassCount_sameBlock_trans
import Theorems.Thm_GlobalTheory_HL_ClassCount_isUni_mul
import Theorems.Thm_GlobalTheory_HL_ClassCount_apply_frame
import Theorems.Thm_GlobalTheory_HL_ClassCount_isIntCls_smul
import Theorems.Thm_GlobalTheory_HL_ClassCount_stab_le
import Theorems.Thm_GlobalTheory_HL_ClassCount_matrix_of_mem
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
import Theorems.Thm_GlobalTheory_T_commonStabilizer_stabilizers_commensurable_volume
import Theorems.Thm_GlobalTheory_T_hermitianDoubleCosetFrameClass_properties
import Theorems.Thm_GlobalTheory_T_latticeStabilizer_inf_le_conj_normalisingSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ClassCount
namespace GlobalTheory.HL.ClassCount
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (S.sumCls fun _ => 1) ≤ ({C : Set S.FrP | S.IsIntCls C ∧ ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ IsUni u' ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ C = S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i}.encard : ℝ≥0∞) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine tsum_le_encard S.St S.K0 (fun _ h => h.1.1) S.IsIntCls _ S.wC fun C hC => ?_
  have hC' := hC
  obtain ⟨⟨n, hn, n', hn', rfl⟩, -⟩ := hC'
  obtain ⟨h, hh, hle, u, hu, hub, e⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
  obtain ⟨u', hu', e'⟩ := (FrameOnto.unipotent_onto L r k S).2.1 (h⁻¹ * n')
    (S.N'.mul_mem (S.St.inv_mem hh).2 hn')
  refine ⟨h⁻¹, inv_mem hh, (((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 _ hC.1).2.2.2 _ (inv_mem hh)).symm, ?_, ?_⟩
  · rintro g ⟨g1, g2⟩
    have h1 : h * g * h⁻¹ ∈ MulAut.conj h • S.K0 := by
      refine hle ⟨S.St.mul_mem (S.St.mul_mem hh g1) (S.St.inv_mem hh), stab_le S _ (fun b => n' (S.f' b)) ?_⟩
      have g3 : g • h⁻¹ • _ = h⁻¹ • _ := g2
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, g3, smul_inv_smul]
    exact (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj h) (x := g)).1 h1
  · intro g hg
    obtain ⟨s, s', hs, hs', hi, hb, d, d'⟩ := matrix_of_mem S hg
    refine ⟨isIntCls_smul S hg.1.1 (isIntCls_smul S (S.St.inv_mem hh) hC), s * u, s' * u',
      isUni_mul hs hu, isUni_mul hs' hu', fun i j hij => ?_, ?_⟩
    · rw [Matrix.mul_apply]
      refine Subring.sum_mem _ fun l _ => ?_
      cases hl : sameBlock S.w.blocks i l
      · rw [hb i l hl, zero_mul]; exact zero_mem _
      · exact mul_mem (hi i l) (hub l j (sameBlock_trans _ _ _ _ hl hij))
    · rw [(GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 h⁻¹, (GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 g]
      congr 1
      · funext j
        rw [e j, apply_frame g S.f s u d]
      · funext j
        rw [← apply_frame g S.f' s' u' d', ← e' j]
        rfl
end GlobalTheory.HL.ClassCount
