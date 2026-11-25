-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.selfDualLattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:00.101772+00:00
-- url     : https://prove2.me/submissions/ed6f658d-a97d-4639-b255-eb731c317efb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_smul_right
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_smul_left
import Theorems.Thm_P2M_GlobalTheory_UnramSelfDual_smul_mem__cfd5fc8f3c8d
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_basis
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_unitary_lat
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_image
import Theorems.Thm_GlobalTheory_UnramSelfDual_sigR_algebraMap
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_of_fixed
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_norm
import Theorems.Thm_GlobalTheory_UnramSelfDual_JR_herm
import Theorems.Thm_GlobalTheory_UnramSelfDual_JR_det
import Theorems.Thm_GlobalTheory_UnramSelfDual_sd_iff
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_frame
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualLatticeActions_sigR_mem
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryLatticeOrthogonal_sigR_mem
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_frame
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_hR_self
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_sigR_sigR
import Theorems.Thm_GlobalTheory_SelfDualLatticeSplit_unit_vector_splits
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_stabLat_inf_stabVec
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_stabiliser_iso
import Theorems.Thm_GlobalTheory_UnramConjUnit_exists_sub_conj_unit
import Theorems.Thm_GlobalTheory_WittTransitivity_witt_transitive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
open GlobalTheory.SelfDualLatticeCompare
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution : SelfDualLattices := by
  intro F E _ _ _ _ _ σ h M J hJ hM v hv L hL
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  obtain ⟨⟨x₀, hx₀, hx₀1⟩, hfr⟩ := exists_frame v h hv hJ hL
  obtain ⟨e, heL, he, -⟩ := hfr x₀ hx₀ hx₀1
  have hθ := GlobalTheory.UnramConjUnit.exists_sub_conj_unit F E σ h v hv
  refine ⟨?_, fun L₁ hL₁ => ?_, fun β => ?_⟩
  · obtain ⟨b, hb⟩ := exists_basis (sd_iff v hL) heL he
    exact ⟨b, fun i j => by rw [hb, hb]; exact he i j⟩
  · obtain ⟨⟨x₁, hx₁, hx₁1⟩, hfr₁⟩ := exists_frame v h hv hJ hL₁
    obtain ⟨e₁, heL₁, he₁, -⟩ := hfr₁ x₁ hx₁ hx₁1
    obtain ⟨g, hg, -, hgL⟩ := exists_unitary_lat (sd_iff v hL) (sd_iff v hL₁) heL he heL₁ he₁
    exact ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), hgL⟩
  set B : Ev F E v := algebraMap (v.adicCompletionIntegers F) _ β with hB
  set B' : Ev F E v := algebraMap (v.adicCompletionIntegers F) _ (β⁻¹ : (v.adicCompletionIntegers F)ˣ)
    with hB'
  have hBB : B * B' = 1 := by rw [hB, hB', ← map_mul, Units.mul_inv, map_one]
  have hBO : B ∈ OEv F E v := (OEv F E v).algebraMap_mem _
  have hB'O : B' ∈ OEv F E v := (OEv F E v).algebraMap_mem _
  have hq : ∀ x, qR (Fv F v) σ J x = ((β : v.adicCompletionIntegers F) : Fv F v) ↔
      hR (Fv F v) σ J x x = B := fun x => by
    rw [hR_self _ h hJ]
    exact ((algebraMap (Fv F v) (Ev F E v)).injective.eq_iff).symm
  obtain ⟨a, ha, haB⟩ := exists_norm v h hθ B hBO (sigR_algebraMap v _) ⟨B', hB'O, hBB⟩
  have hS : a • x₀ ∈ SL σ J v L ((β : v.adicCompletionIntegers F) : Fv F v) := by
    refine ⟨smul_mem' ha hx₀, (hq _).2 ?_⟩
    have : hform (sigR (Fv F v) σ) (JR (Fv F v) J) x₀ x₀ = 1 := hx₀1
    rw [hR, h_smul_left, h_smul_right, this, mul_one, haB]
  have hunit : ∀ x, qR (Fv F v) σ J x = ((β : v.adicCompletionIntegers F) : Fv F v) →
      ∃ b ∈ OEv F E v, hR (Fv F v) σ J x x * b = 1 :=
    fun x hx => ⟨B', hB'O, by rw [(hq x).1 hx, hBB]⟩
  have hwitt : ∀ x x', qR (Fv F v) σ J x = ((β : v.adicCompletionIntegers F) : Fv F v) →
      qR (Fv F v) σ J x' = ((β : v.adicCompletionIntegers F) : Fv F v) →
      ∃ g ∈ UJ (sigR (Fv F v) σ) (JR (Fv F v) J),
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ev F E v)) *ᵥ x = x' := by
    intro x x' hx hx'
    refine GlobalTheory.WittTransitivity.witt_transitive (Ev F E v) (sigR (Fv F v) σ) (sigR_sigR _ h) (fun a ha h0 => ?_) ?_ ?_ ?_
      _ _ (JR_herm v hJ) (JR_det v hJ) x x' (((hq x).1 hx).trans ((hq x').1 hx').symm) ?_
    · obtain ⟨k, rfl⟩ := exists_of_fixed v h ha
      exact (IsUnit.mk0 k fun hk => h0 (by rw [hk, map_zero])).map _
    · rw [← map_ofNat (algebraMap F (Ev F E v)) 2]
      exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
    · rw [← map_ofNat (algebraMap F (Ev F E v)) 3]
      exact ((IsUnit.mk0 (3 : F) three_ne_zero).map _).ne_zero
    · obtain ⟨θ, -, b, -, hb⟩ := hθ
      exact ⟨θ, IsUnit.of_mul_eq_one b hb⟩
    · obtain ⟨b, -, hb⟩ := hunit x hx
      exact IsUnit.of_mul_eq_one b hb
  refine ⟨⟨_, hS⟩, fun x hx => GlobalTheory.SelfDualLatticeSplit.unit_vector_splits F E σ h _ J hJ v L hL x hx.1 (hunit x hx.2),
    fun x hx x' hx' => ?_, fun x hx => ?_, fun x hx x' hx' => ?_, fun x hx => ?_⟩
  · set a' := sigR (Fv F v) σ a * B' with ha'
    have haa : a * a' = 1 := by rw [ha']; linear_combination B' * haB + hBB
    have ha'O : a' ∈ OEv F E v := mul_mem (sigR_mem σ v ha) hB'O
    have hca : sigR (Fv F v) σ a * sigR (Fv F v) σ a' = 1 := by rw [← map_mul, haa, map_one]
    have key : ∀ y ∈ SL σ J v L ((β : v.adicCompletionIntegers F) : Fv F v),
        hR (Fv F v) σ J (a' • y) (a' • y) = 1 := fun y hy => by
      have : hform (sigR (Fv F v) σ) (JR (Fv F v) J) y y = B := (hq y).1 hy.2
      rw [hR, h_smul_left, h_smul_right, this, ← haB]
      linear_combination (a * a') * hca + haa
    obtain ⟨f, hfL, hf, hf0⟩ := hfr _ (smul_mem' ha'O hx.1) (key x hx)
    obtain ⟨f', hfL', hf', hf0'⟩ := hfr _ (smul_mem' ha'O hx'.1) (key x' hx')
    obtain ⟨g, hg, hge, hgL⟩ := exists_unitary_lat (sd_iff v hL) (sd_iff v hL) hfL hf hfL' hf'
    refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), hgL, ?_⟩
    have h1 := congrArg (fun y => a • y) (hge 0)
    simp only [hf0, hf0', Matrix.mulVec_smul, smul_smul, haa, one_smul] at h1
    exact h1
  · have h1 := GlobalTheory.UnitVectorStabEq.stabLat_inf_stabVec F E σ h _ J hJ v L hL x hx.1 (hunit x hx.2)
    obtain ⟨b, -, hb⟩ := hunit x hx.2
    obtain ⟨φ, hφ⟩ := GlobalTheory.UnitVectorStabiliser.stabiliser_iso F E σ h _ J hJ v L x (IsUnit.of_mul_eq_one b hb)
    exact ⟨h1, (MulEquiv.subgroupCongr h1).trans φ, fun g y => hφ _ y⟩
  · obtain ⟨g, hg, hgx⟩ := hwitt x x' hx.2 hx'.2
    exact ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), hgx⟩
  · obtain ⟨g, hg, hgx⟩ := hwitt _ x hS.2 hx.2
    obtain ⟨L', h1, h2, h3, h4⟩ := exists_image hL.1 hL.2.1 (sd_iff v hL) hg
    have hL' : IsSDLat σ J v L' :=
      ⟨h1, h2, fun y => (h3 y).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩⟩
    have hxL : x ∈ L' := hgx ▸ h4 _ hS.1
    exact ⟨⟨L', hL', hxL⟩, _, (GlobalTheory.SelfDualLatticeSplit.unit_vector_splits F E σ h _ J hJ v L' hL' x hxL (hunit x hx.2)).2⟩
end GlobalTheory.UnramSelfDual
