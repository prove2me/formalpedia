-- Prove2me | solution 1 for LanglandsTunnell.centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/50add9e3-94d8-5962-a24e-fd9d4434b0c8

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

namespace ArchLinkAux

theorem re_signShift_nonneg (a : ZMod 2) : 0 ≤ (LanglandsTunnell.signShift a).re := by
  unfold LanglandsTunnell.signShift; split_ifs <;> simp

theorem archFactor_ne_zero_of_re_gt (P : RealArchParam) :
    ∃ M : ℝ, ∀ s : ℂ, M < s.re → P.archFactor s ≠ 0 := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    refine ⟨|u₁.re| + |u₂.re| + 1, fun s hs => ?_⟩
    have h1 := re_signShift_nonneg a₁
    have h2 := re_signShift_nonneg a₂
    have hu1 := neg_abs_le u₁.re
    have hu2 := neg_abs_le u₂.re
    have hp1 := abs_nonneg u₁.re
    have hp2 := abs_nonneg u₂.re
    simp only [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, Multiset.map_zero,
      Multiset.prod_zero, mul_one, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    refine mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ?_) (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
    · simp only [Complex.add_re]; linarith
    · simp only [Complex.add_re]; linarith
  | discrete u k hk =>
    refine ⟨|u.re| + 1, fun s hs => ?_⟩
    have hu := neg_abs_le u.re
    simp only [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, Multiset.map_zero,
      Multiset.prod_zero, one_mul, Multiset.map_singleton, Multiset.prod_singleton]
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos ?_)
    · rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · have : (s + (u + (k : ℂ) / 2)).re = s.re + u.re + (k : ℝ) / 2 := by
        rw [show (u + (k : ℂ) / 2) = u + ((k / 2 : ℝ) : ℂ) by push_cast; ring, Complex.add_re, Complex.add_re,
          Complex.ofReal_re]; ring
      rw [this]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith

end ArchLinkAux

theorem solution
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (A : RealArchParam)
    (hcen : LanglandsTunnell.Converse.IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (default : InfinitePlace ℚ)
      (A.centralExponent + 1) (A.centralSign.val : ℤ))
    (par : ZMod 2) (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ)
    (C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hC : C 1 1 ≠ 0)
    (hfac : (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
                whittakerCoefficient ℚ
                    (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ φ₀ 1 (diagOne a * g)
                  = (∏ w : InfinitePlace ℚ, Wr w (NumberField.InfinitePlace.Completion.extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                      * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g))
    (hMel : ∀ b : ZMod 2, (b = par ∨ b = par + A.centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr default t + (-1 : ℂ) ^ b.val * Wr default (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr default t + (-1 : ℂ) ^ b.val * Wr default (-t)) / (t : ℂ)) s
            = (A.twist 0 b).archFactor s) :
    σ₀ = (A.centralExponent + 1).re ∧
    (∀ z : ℝˣ, ‖(TateGlobal.archLocalChar (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) default
        (Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm.toMonoidHom z) : ℂ)‖ = |(z : ℝ)| ^ σ₀) ∧
    (∃ t : ℝˣ, Wr default ((t : ℝ) : ℂ) ≠ 0) ∧
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₀ 1 ≠ 0 := by
  classical
  have hw : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _
  set ξ' : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := ξ.comp Subgroup.topEquiv.symm.toMonoidHom with hξ'
  set u : ℂ := A.centralExponent + 1 with hu
  set e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw with he

  have hnorm_symm : ∀ z : ℝ, ‖e.symm z‖ = |z| := by
    intro z
    have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) (e.symm z)
    rw [← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, ← he, RingEquiv.apply_symm_apply,
      Real.norm_eq_abs] at h
    exact h.symm
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by simp [NumberField.InfinitePlace.mult, hw]

  have hA : ∀ x : ((default : InfinitePlace ℚ).Completion)ˣ,
      ‖((TateGlobal.archLocalChar ξ' default x : ℂˣ) : ℂ)‖ = ‖(x : (default : InfinitePlace ℚ).Completion)‖ ^ u.re := by
    intro x
    have hx : 0 < ‖(x : (default : InfinitePlace ℚ).Completion)‖ := norm_pos_iff.mpr x.ne_zero
    rw [hcen x, norm_mul, norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _),
      div_self hx.ne', one_zpow, mul_one, hmult, Nat.cast_one, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

  have hB : ∀ x : ((default : InfinitePlace ℚ).Completion)ˣ,
      TateGlobal.ideleNorm ℚ (TateGlobal.archUnitHom default x) = ‖(x : (default : InfinitePlace ℚ).Completion)‖ := by
    intro x
    unfold TateGlobal.ideleNorm
    rw [TateGlobal.archUnitHom_apply,
      NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one ℚ _
        (NumberField.AdelicVolume.archCentralUnit_snd _ _),
      Fintype.prod_unique, NumberField.AdelicVolume.archCentralUnit_fst_self, hmult, pow_one]

  have hC' : ∀ x : ((default : InfinitePlace ℚ).Completion)ˣ,
      ‖(x : (default : InfinitePlace ℚ).Completion)‖ ^ σ₀ = ‖(x : (default : InfinitePlace ℚ).Completion)‖ ^ u.re := by
    intro x
    rw [← hA x, ← hB x]
    exact (hσ₀ (TateGlobal.archUnitHom default x)).symm
  have hsymm_ne : ∀ z : ℝ, z ≠ 0 → (e.symm z : (default : InfinitePlace ℚ).Completion) ≠ 0 := by
    intro z hz h; have := hnorm_symm z; rw [h, norm_zero] at this; exact hz (abs_eq_zero.mp this.symm)
  have hσ : σ₀ = u.re := by
    have h := hC' (Units.mk0 _ (hsymm_ne 2 two_ne_zero))
    rw [Units.val_mk0, hnorm_symm] at h
    norm_num at h
    have hl := congrArg Real.log h
    rw [Real.log_rpow two_pos, Real.log_rpow two_pos] at hl
    have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    exact mul_right_cancel₀ this hl

  have hE : ∃ t : ℝˣ, Wr default ((t : ℝ) : ℂ) ≠ 0 := by
    by_contra hzero
    push Not at hzero
    obtain ⟨s₀, hs₀⟩ := hMel par (Or.inl rfl)
    obtain ⟨M, hM⟩ := ArchLinkAux.archFactor_ne_zero_of_re_gt (A.twist 0 par)
    set s : ℂ := ((max s₀ M + 1 : ℝ) : ℂ) with hs
    have hsre : s.re = max s₀ M + 1 := by rw [hs, Complex.ofReal_re]
    have h1 : s₀ < s.re := by rw [hsre]; exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
    have h2 : M < s.re := by rw [hsre]; exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
    obtain ⟨-, hmel⟩ := hs₀ s h1
    apply hM s h2
    rw [← hmel]

    unfold mellin
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    have ht0 : (t : ℝ) ≠ 0 := (Set.mem_Ioi.mp ht).ne'
    have hneg : (-t : ℝ) ≠ 0 := neg_ne_zero.mpr ht0
    have ha := hzero (Units.mk0 t ht0)
    have hb := hzero (Units.mk0 (-t) hneg)
    simp only [Units.val_mk0] at ha hb
    push_cast at hb
    simp [ha, hb]
  refine ⟨hσ, fun z => ?_, hE, ?_⟩
  ·
    rw [hA, hσ]
    congr 1
    rw [Units.coe_map]
    exact hnorm_symm z
  ·
    obtain ⟨t, ht⟩ := hE
    intro hW
    have h := hfac (TateGlobal.archUnitHom default (Units.mk0 (e.symm (t : ℝ)) (hsymm_ne _ t.ne_zero))) 1 (one_mem _)
    rw [hW, Fintype.prod_unique, TateGlobal.archUnitHom_apply, NumberField.AdelicVolume.archCentralUnit_snd,
      NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_mk0,
      ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, ← he, RingEquiv.apply_symm_apply] at h
    exact mul_ne_zero ht hC (by simpa using h.symm)

end S_LanglandsTunnell_centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
end P2MW
export P2MW.S_LanglandsTunnell_centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat (solution)
