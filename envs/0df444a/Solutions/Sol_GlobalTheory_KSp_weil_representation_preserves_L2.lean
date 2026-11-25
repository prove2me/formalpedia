-- Prove2me | solution 1 for GlobalTheory.KSp.weil_representation_preserves_L2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:16.984471+00:00
-- url     : https://prove2.me/submissions/47fc1365-d935-4c59-80b3-d24ead1d9f54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicWeylElementGenerateUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralSqSiegelParabolicOperatorEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2Space
import Theorems.Thm_GlobalTheory_KSp_mem_sieg
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_T_bicharacterFourierTransform_twice_eq_pos_smul_reflect
import Theorems.Thm_GlobalTheory_T_hermitianMatrixColumnPairing_algebraic_properties
import Theorems.Thm_GlobalTheory_T_isSelfDualBicharacterPairing_of_symmBilinForm
import Theorems.Thm_GlobalTheory_T_lintegral_four_sq_eq_mul_of_inversion
import Theorems.Thm_GlobalTheory_T_lintegral_sq_siegelParabolicOperator_eq
import Theorems.Thm_GlobalTheory_T_quadExt_topological_properties
import Theorems.Thm_GlobalTheory_T_siegelParabolic_weylElement_generate_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ κ ω hKW μ' _ g φ
  obtain ⟨hfd, htr, hinv, ht2, hc, hn, htrc, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI := hfd
  haveI := hmt
  haveI := hgood.grp
  haveI := hgood.t2
  haveI := hgood.lc
  haveI := hgood.sc
  let N : SB (Matrix α ν E) → ℝ≥0∞ := fun f => ∫⁻ x, ‖(f : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ φ, N (ω g φ) = N φ}
      one_mem' := by intro φ; simp
      mul_mem' := by
        intro g h hg hh φ
        show N (ω (g * h) φ) = N φ
        rw [map_mul, Module.End.mul_apply, hg, hh]
      inv_mem' := by
        intro g hg φ
        have := hg (ω g⁻¹ φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hsieg : sieg c ν ≤ U := by
    intro p hp φ
    show N (ω p φ) = N φ
    simp only [N]
    rw [hKW.par p hp φ]
    exact GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ p hp φ
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψ1 hψne β hβs hβn
    simpa only [hβ] using this
  obtain ⟨C, hC, hfi⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have hpl := GlobalTheory.T.lintegral_four_sq_eq_mul_of_inversion (Matrix α ν E) hgood μ _ hpair C hC hfi
  have hw : ∀ φ : SB (Matrix α ν E), N (ω (weyl c ν) φ) = (‖κ‖ₑ ^ 2 * ENNReal.ofReal C) * N φ := by
    intro φ
    simp only [N]
    rw [hKW.wey φ]
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ (by simp), fou, hpl _ φ.2, mul_assoc]
  have hww : weyl c ν * weyl c ν ∈ sieg c ν := by
    rw [mem_sieg]
    show ((stdJ ν E) * (stdJ ν E)).toBlocks₂₁ = 0
    rw [stdJ_mul_stdJ]
    ext i j
    simp [toBlocks₂₁]
  obtain ⟨L, hLc, hLo, -⟩ := hgood.large ∅ isCompact_empty
  have hmem : (L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) ∈ SB (Matrix α ν E) := by
    refine ⟨?_, ?_⟩
    · have hcl : IsClopen (L : Set (Matrix α ν E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
      exact (LocallyConstant.charFn ℂ hcl).isLocallyConstant
    · exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  set φ₀ : SB (Matrix α ν E) := ⟨_, hmem⟩ with hφ₀
  have hN0 : N φ₀ = μ L := by
    simp only [N, hφ₀]
    have e : (fun x => ‖(L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) x‖ₑ ^ 2) =
        (L : Set (Matrix α ν E)).indicator 1 := by
      funext x
      by_cases hx : x ∈ (L : Set (Matrix α ν E)) <;> simp [hx]
    rw [e, lintegral_indicator_one hLo.measurableSet]
  have hpos : μ L ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
  set k : ℝ≥0∞ := ‖κ‖ₑ ^ 2 * ENNReal.ofReal C with hk
  have hkk : k * k = 1 := by
    have h1 : N (ω (weyl c ν * weyl c ν) φ₀) = N φ₀ := hsieg hww φ₀
    rw [map_mul, Module.End.mul_apply, hw, hw, ← mul_assoc, hN0] at h1
    have h2 := congrArg (· / μ L) h1
    simpa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.div_self hpos hfin] using h2
  have hk1 : k = 1 := by
    rcases lt_trichotomy k 1 with h | h | h
    · have : k * k ≤ k * 1 := by gcongr
      rw [hkk, mul_one] at this
      exact absurd this (not_le.mpr h)
    · exact h
    · have : 1 * k ≤ k * k := by gcongr
      rw [hkk, one_mul] at this
      exact absurd this (not_le.mpr h)
  have hwU : weyl c ν ∈ U := by
    intro φ
    show N (ω (weyl c ν) φ) = N φ
    rw [hw, hk1, one_mul]
  have htop : U = ⊤ := GlobalTheory.T.siegelParabolic_weylElement_generate_unitary F E c δ hE ν U hsieg hwU
  have hgU : g ∈ U := htop ▸ Subgroup.mem_top g
  have hμ' : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  rw [hμ', lintegral_smul_measure, lintegral_smul_measure]
  exact congrArg _ (hgU φ)
end GlobalTheory.KSp
