-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.Model.isQuad_isHerm_continuous_resEtaPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:29:58.944065+00:00
-- url     : https://prove2.me/submissions/f5b1d889-aeee-4c78-9a7d-03f19630fdb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ConclRankZeroRight
import Theorems.Thm_GlobalTheory_SplitUnitary_Model_isQuad_sqrt
import Theorems.Thm_GlobalTheory_HermLocal_Model_conjSqrt_apply
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_ne_one
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_one
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
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
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
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.SplitUnitary GlobalTheory.SplitUnitary.Model
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)
namespace GlobalTheory.SplitUnitary.Model
theorem _root_.solution (K : Type) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] (k : ℕ) :
    ∃ (_ : TopologicalSpace (QuadraticAlgebra K d 0)) (_ : IsModuleTopology K (QuadraticAlgebra K d 0))
      (c : QuadraticAlgebra K d 0 →ₐ[K] QuadraticAlgebra K d 0) (δ : QuadraticAlgebra K d 0)
      (Q : Matrix (Fin (2 * k)) (Fin (2 * k)) (QuadraticAlgebra K d 0)) (ψ : AddChar K ℂ)
      (χ : (QuadraticAlgebra K d 0)ˣ →* Circle),
      IsQuad c δ ∧ IsHerm c Q ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ Continuous χ ∧
        ResEtaPow (R := K) ⊥ χ (Fintype.card (Fin (2 * k))) := by
  obtain ⟨ψ, hψ⟩ := SplitWeil.exists_hasConductor_one K
  letI : TopologicalSpace (QuadraticAlgebra K d 0) := moduleTopology K _
  refine ⟨this, ⟨rfl⟩, _, _, 1, Circle.coeHom.compAddChar ψ, 1, isQuad_sqrt d, ⟨fun i j => ?_, by simp⟩,
    continuous_subtype_val.comp hψ.continuous, fun t => Circle.norm_coe _, fun h => hψ.ne_one ?_, ?_, fun a => ?_⟩
  · by_cases h : i = j
    · subst h; simp
    · simp [one_apply_ne h, one_apply_ne (Ne.symm h)]
  · ext x
    exact DFunLike.congr_fun h x
  · exact continuous_const
  · simp [pow_mul]
end GlobalTheory.SplitUnitary.Model
