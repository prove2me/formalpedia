-- Prove2me | solution 1 for GlobalTheory.SingleBlock.localIntegralSingleBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:47.760163+00:00
-- url     : https://prove2.me/submissions/6171c333-3422-4c0e-83cd-1a60bcb5fa88

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_le_range_of_le_GLint
import Theorems.Thm_GlobalTheory_SingleBlock_det_mem_of_mem_glInt
import Theorems.Thm_GlobalTheory_SingleBlock_det_inv_mem_of_mem_glInt
import Theorems.Thm_GlobalTheory_SingleBlock_norm_eq_one_of_finiteIndex
import Theorems.Thm_GlobalTheory_SingleBlock_isOpen_integers
import Theorems.Thm_GlobalTheory_SingleBlock_isCompact_integers
import Theorems.Thm_GlobalTheory_SingleBlock_t2Space_isNonarchimedeanLocalField_singleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_unif_ne_zero
import Theorems.Thm_GlobalTheory_SingleBlock_isLocalAt
import Theorems.Thm_GlobalTheory_SingleBlock_card_kF
import Theorems.Thm_GlobalTheory_SingleBlock_finite_kF
import Theorems.Thm_GlobalTheory_SingleBlock_relIndex_congSub
import Theorems.Thm_GlobalTheory_SingleBlock_tame_det
import Theorems.Thm_GlobalTheory_SingleBlock_nrm_det
import Theorems.Thm_GlobalTheory_SingleBlock_coe_targetLevel
import Theorems.Thm_GlobalTheory_SingleBlock_relIndex_targetLevel
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_suppJ
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_volII
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_volJadd
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_congSub_open
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_glR_compact
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_suppJ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_volII
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_volJadd
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LocalIntegralGL_blockChar_apply
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LocalIntegralGL_weilPair_one_right
import Theorems.Thm_GlobalTheory_SingleBlock_exists_of_congr
import Theorems.Thm_GlobalTheory_SingleBlock_hasCompactSupport_phiU
import Theorems.Thm_GlobalTheory_SingleBlock_index_blockPar
import Theorems.Thm_GlobalTheory_SingleBlock_isLocallyConstant_phiU
import Theorems.Thm_GlobalTheory_SingleBlock_measurableSet_suppSet
import Theorems.Thm_GlobalTheory_SingleBlock_measure_suppSet
import Theorems.Thm_GlobalTheory_SingleBlock_mul_left_mem
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_mul_right
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_notMem
import Theorems.Thm_GlobalTheory_SingleBlock_weilPairing_self_eq_measure_support
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
namespace GlobalTheory.SingleBlock
theorem _root_.solution : LocalIntegralSingleBlock := by
  intro F _ _ _ _ _ _ r t ϖ hϖ nrm hn μ η hμ hη _ P hKP hP lam hlam ν _ hν q Φ J normSq
  have hO := isOpen_integers (F := F)
  have hT : T2Space F := t2Space_isNonarchimedeanLocalField_singleBlock
  have hϖ0 := unif_ne_zero hϖ
  have hloc := isLocalAt hϖ
  have hfin := finite_kF hϖ
  have hq0 : q ≠ 0 := Nat.card_pos.ne'
  set ρ := blockChar μ P lam with hρdef
  have hΦ : Φ = phiU 𝒪[F] (ϖ : F) P ρ := rfl
  have hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub 𝒪[F] (ϖ : F) r), ρ ⟨k, hKP hk⟩ = 1 := by
    intro k hk
    rw [hρdef, blockChar_apply, hlam k hk, tame_det hϖ hμ hk]; simp
  have hidx : ((congSub 𝒪[F] (ϖ : F) r).subgroupOf P).index = Nat.card (residueImage P) :=
    relIndex_congSub hϖ hP
  have hfinGL : Finite (GL (Fin r) 𝓀[F]) := by
    have : Finite (Matrix (Fin r) (Fin r) 𝓀[F]) :=
      inferInstanceAs (Finite (Fin r → Fin r → 𝓀[F]))
    exact Finite.of_injective _ Units.val_injective
  have hidx0 : ((congSub 𝒪[F] (ϖ : F) r).subgroupOf P).index ≠ 0 := by
    rw [hidx]; exact Nat.card_pos.ne'
  have hρ1 := norm_eq_one_of_finiteIndex _ hidx0 ρ fun k hk => hρ k hk
  have hlam1 := norm_eq_one_of_finiteIndex _ hidx0 lam fun k hk => hlam k hk
  have hS : MeasurableSet (suppSet t 𝒪[F] (ϖ : F) P) :=
    measurableSet_suppSet hO ϖ.2 hϖ0 hloc hKP hP
  have hN : normSq = ((ν (suppSet t 𝒪[F] (ϖ : F) P)).toReal : ℂ) := weilPairing_self_eq_measure_support hS ρ hρ1 ν
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hvol : (ν (suppSet t 𝒪[F] (ϖ : F) P)).toReal =
      (Nat.card (residueImage P) : ℝ) * ((q : ℝ) ^ (r ^ 2))⁻¹ * ((q : ℝ) ^ (r * t))⁻¹ := by
    have h := measure_suppSet hO ϖ.2 hϖ0 hloc hKP hP ν
    rw [hν, mul_one, card_kF hϖ, ← Subgroup.index, hidx] at h
    have h' := congrArg ENNReal.toReal h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h'
    rw [← h', pow_two, mul_comm r t]
    change _ = _ * (q : ℝ) ^ _ * (q : ℝ) ^ _ * _ * _
    field_simp
  have hJ := coe_targetLevel (t := t) hϖ hP
  have hi1 : ∀ g : GL (Fin r) F, g ∉ P → weilIP ν (weilPair μ η nrm g 1 Φ) Φ = 0 := by
    intro g hg
    rw [weilPair_one_right]
    exact suppJ F r t _ _ P ρ _ nrm ν g hg
  have hi2 : ∀ g : P, weilIP ν (weilPair μ η nrm (g : GL (Fin r) F) 1 Φ) Φ =
      ((lam g : ℂˣ) : ℂ) * normSq := by
    intro g
    have hg := le_range_of_le_GLint hP g.2
    have e : ∀ x, weilPair μ η nrm (g : GL (Fin r) F) 1 Φ x = ((lam g : ℂˣ) : ℂ) * Φ x := by
      intro x
      unfold weilPair
      rw [nrm_det hn hg, hη _ (det_mem_of_mem_glInt hg) (det_inv_mem_of_mem_glInt hg), inv_one,
        Units.val_one, Matrix.one_mul, hΦ, phiU_mul_right hP ρ g, hρdef, blockChar_apply]
      simp only [map_one, inv_one, mul_one, Units.val_one, Real.one_rpow, Complex.ofReal_one,
        Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    change _ = _ * weilIP ν Φ Φ
    unfold weilIP
    simp_rw [e, mul_assoc]
    rw [integral_const_mul]
  have hv : (J.relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) : ℂ) * normSq =
      ((∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℝ) ^ i)⁻¹) : ℝ) : ℂ) := by
    rw [hN, hvol, relIndex_targetLevel hϖ hP, ← index_blockPar (residueImage P)]
    push_cast; rfl
  refine ⟨⟨isLocallyConstant_phiU hO ϖ.2 hϖ0 hloc hKP hP ρ hρ,
    hasCompactSupport_phiU isCompact_integers ϖ.2 hP ρ, hJ⟩, ⟨hi1, hi2⟩, ⟨?_, ?_⟩, ?_, ?_, hv, ?_⟩
  · intro ν₁ _ ν₂ _ h1 h2
    have a1 := volJadd F 𝒪[F] hO ϖ ϖ.2 hϖ0 hloc hfin r ν₁ P hKP hP
    have a2 := volII F 𝒪[F] hO ϖ ϖ.2 hϖ0 hfin t r ν₂
    rw [h1, mul_one, card_kF hϖ, ← Subgroup.index, hidx] at a1
    rw [h2, card_kF hϖ] at a2
    have b1 := congrArg ENNReal.toReal a1
    have b2 := congrArg ENNReal.toReal a2
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_one] at b1 b2
    rw [hN, hvol, ← b1, eq_inv_of_mul_eq_one_left b2, pow_two, mul_comm r t]
    congr 1
    change _ * (q : ℝ) ^ _ * _ * _ = _ * ((q : ℝ) ^ _)⁻¹
    field_simp
  · rw [hN, hvol]
  · intro V _ _ σ _ x₁ x₂ hx dg _
    have hPo : IsOpen (P : Set (GL (Fin r) F)) :=
      Subgroup.isOpen_mono hKP (GLRed.congSub_open _ hO _ r)
    have hPc : IsCompact (P : Set (GL (Fin r) F)) :=
      (GeneralLinearIntegersOpenCompact.glR_compact 𝒪[F] isCompact_integers r).of_isClosed_subset
        (P.isClosed_of_isOpen hPo) hP
    have e : (fun g : GL (Fin r) F =>
        weilIP ν (weilPair μ η nrm g 1 Φ) Φ * conj (inner ℂ x₂ (σ g x₁))) =
        (P : Set (GL (Fin r) F)).indicator (fun _ => normSq * conj (inner ℂ x₂ x₁)) := by
      funext g
      by_cases hg : g ∈ P
      · rw [Set.indicator_of_mem (show g ∈ (P : Set _) from hg), hi2 ⟨g, hg⟩, hx ⟨g, hg⟩,
          inner_smul_right, map_mul]
        have h1 : ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) * conj ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam1]; simp
        linear_combination (normSq * conj (inner ℂ x₂ x₁)) * h1
      · rw [Set.indicator_of_notMem (show g ∉ (P : Set _) from hg), hi1 g hg, zero_mul]
    have hZ : localZ dg ν (μ * η) nrm Φ Φ (fun g => inner ℂ x₂ (σ g x₁)) =
        (((dg (P : Set (GL (Fin r) F))).toReal : ℝ) : ℂ) * normSq * conj (inner ℂ x₂ x₁) := by
      unfold localZ
      simp_rw [← weilPair_one_right]
      rw [e, integral_indicator_const _ hPo.measurableSet, Complex.real_smul, mul_assoc]
      rfl
    refine ⟨?_, hZ, fun h1 => by rw [hZ, h1]; simp⟩
    rw [e, integrable_indicator_iff hPo.measurableSet]
    exact integrableOn_const hPc.measure_lt_top.ne
  · have key : ∀ h ∈ J, ∃ k : P, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ ∧
        ∀ x ∈ suppSet t 𝒪[F] (ϖ : F) P,
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x ∈ suppSet t 𝒪[F] (ϖ : F) P ∧
          Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x) = ((ρ k : ℂˣ) : ℂ) * Φ x := by
      intro h hh
      obtain ⟨⟨h0, e0⟩, ⟨p, hp, e1⟩, e2⟩ : h ∈ targetSet t 𝒪[F] (ϖ : F) P := hJ ▸ hh
      obtain ⟨k, hk, -⟩ := exists_of_congr ϖ.2 hϖ0 hloc hKP hP ρ hρ ⟨p, hp⟩ e1
      refine ⟨k, hk, fun x hx => mul_left_mem ϖ.2 hϖ0 hloc hKP hP ρ hρ (fun i j => ?_) k hk e2 hx⟩
      rw [← e0]
      exact ((h0 : Matrix _ _ 𝒪[F]) i j).2
    intro h hh
    obtain ⟨k, hk, hm⟩ := key h hh
    obtain ⟨k', -, hm'⟩ := key h⁻¹ (J.inv_mem hh)
    have hg : h ∈ glInt 𝒪[F] (Fin r ⊕ Fin t) :=
      (show h ∈ targetSet t 𝒪[F] (ϖ : F) P from hJ ▸ hh).1
    refine ⟨k, hk, funext fun x => ?_⟩
    have e : Φ x = ((ρ k : ℂˣ) : ℂ) *
        Φ (((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x) := by
      by_cases hx : ((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x ∈
          suppSet t 𝒪[F] (ϖ : F) P
      · rw [← (hm _ hx).2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      · rw [hΦ, phiU_of_notMem ρ hx, mul_zero, phiU_of_notMem ρ fun h1 => hx (hm' x h1).1]
    unfold weilPair
    rw [nrm_det hn hg, Pi.smul_apply, e, Units.val_one, Matrix.mul_one]
    simp only [map_one, one_mul, mul_one, Units.val_one, Real.one_rpow, Complex.ofReal_one,
      Units.val_mul, Units.val_inv_eq_inv_val, smul_eq_mul]
    field_simp
  · rw [hv]
    congr 1
    unfold dFactor localZeta
    rw [Finset.prod_inv_distrib, one_div, inv_inv]
end GlobalTheory.SingleBlock
