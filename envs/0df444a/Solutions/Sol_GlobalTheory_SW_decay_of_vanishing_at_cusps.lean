-- Prove2me | solution 1 for GlobalTheory.SW.decay_of_vanishing_at_cusps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:59:44.897893+00:00
-- url     : https://prove2.me/submissions/c99b85e3-af8b-4b4d-9279-8f16d0360aac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTubeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps
import Theorems.Thm_GlobalTheory_SW_Decay_imH_xy
import Theorems.Thm_GlobalTheory_SW_Decay_pr_im
import Theorems.Thm_GlobalTheory_SW_Decay_norm_e
import Theorems.Thm_GlobalTheory_SW_Decay_posDef_of_ge
import Theorems.Thm_GlobalTheory_SW_Decay_coef_bound
import Theorems.Thm_GlobalTheory_SW_Decay_coef_psd
import Theorems.Thm_GlobalTheory_SW_Decay_coef_posDef
import Theorems.Thm_GlobalTheory_SW_Decay_exists_fourier
import Theorems.Thm_GlobalTheory_SW_Decay_rpow_mul_exp_le
import Theorems.Thm_GlobalTheory_SW_Decay_card_pos
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_SW_TracePair_card_pos
import Theorems.Thm_GlobalTheory_T_summable_exp_neg_trace_totallyPositive_hermitian
import Theorems.Thm_GlobalTheory_T_trace_pairing_ge_detIm_pow_hermitianHalfSpace
import Theorems.Thm_GlobalTheory_re_trace_mul_nonneg_of_posSemidef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory.SW.Decay
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N R : ℕ) (δ s : ℝ), 0 < N → 0 < R → 0 < δ → 0 ≤ s → ∃ C : ℝ, ∀ (f : CM Ψ N N → ℂ) (B : ℝ), DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} → (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N, f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) → (∀ Z ∈ HnGe Ψ N (δ / 4), ‖f Z‖ ≤ B) → (∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0)) → ∀ Z ∈ HnGe Ψ N δ, ‖f Z‖ * detIm Z ^ s ≤ C * B := by
  intro E _ _ _ Ψ hΨ N R δ s hN hR hδ hs
  obtain ⟨m, c, T, X, hc, hinj, hT, hXc, hX, hF⟩ := exists_fourier hΨ N R hR
  obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace E Ψ hΨ N c hN hc
  have hsum := GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian E Ψ hΨ N c (π * δ / 2) hc (by positivity)
  set S : Set (Fin m → ℤ) := {ν | ∀ τ : Ψ, ((T ν).map τ.1).PosSemidef} with hS
  have hsum' : Summable fun ν : S =>
      Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re)) := by
    have hi : Function.Injective fun ν : S => (⟨T ν.1, (hT _).1, (hT _).2, ν.2⟩ :
        {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧
          ∀ τ : Ψ, (T.map τ.1).PosSemidef}) :=
      fun ν μ h => Subtype.ext (hinj (Subtype.mk.inj h))
    have := hsum.comp_injective hi
    simpa only [Function.comp_def] using this
  set σ := ∑' ν : S, Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re)) with hσ
  have hσ0 : 0 ≤ σ := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hd : (0 : ℝ) < ((Ψ.card * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (card_pos hΨ) hN
  set d : ℝ := ((Ψ.card * N : ℕ) : ℝ)
  obtain ⟨C, hC⟩ := rpow_mul_exp_le (b := π * k) (p := d * s) (by positivity) (by positivity)
  refine ⟨C * σ, fun f B hf hper hB hv Z hZ => ?_⟩
  obtain ⟨a, ha, hfa⟩ := hF f hf hper
  have hη : 0 < δ / 4 := by positivity
  have hZ' : Z ∈ Hn Ψ N := fun τ => posDef_of_ge hδ (hZ τ)
  have hB0 : 0 ≤ B := by
    refine (norm_nonneg _).trans (hB (fun _ => 0 + I • (((δ / 4 : ℝ) : ℂ) • 1)) fun τ => ?_)
    rw [imH_xy isHermitian_zero (posDef_of_ge hη (by simpa using PosSemidef.zero)).1]
    simpa using PosSemidef.zero
  have hD : 0 < detIm Z :=
    Finset.prod_pos fun τ _ => (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.det_re_pos_im (hZ' τ)).1
  set u := detIm Z ^ (1 / d) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hD _
  have hus : detIm Z ^ s = u ^ (d * s) := by
    rw [hu, ← Real.rpow_mul hD.le]; congr 1; field_simp
  have h1 : HasSum (fun ν : S => a ν.1 * cexp (2 * π * I * pr (T ν.1) Z)) (f Z) := by
    have hsupp : Function.support (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) ⊆ S :=
      fun ν hν τ => coef_psd hX (hT ν).1 hη hB (ha ν) (left_ne_zero_of_mul hν) τ
    have := (hasSum_subtype_iff_of_support_subset hsupp).2 (hfa Z hZ')
    simpa only [Function.comp_def] using this
  have h2 : ‖f Z‖ ≤ B * Real.exp (-(π * k * u)) * σ := by
    refine h1.norm_le_of_bounded (hsum'.hasSum.mul_left _) fun ν => ?_
    by_cases h0 : a ν.1 = 0
    · rw [h0, zero_mul, norm_zero]; positivity
    have hpd := coef_posDef hXc hX (hT ν.1).1 hη hf hB (ha ν.1) hv h0
    have b1 := coef_bound hX (hT ν.1).1 hη hB (ha ν.1)
      (Y := fun _ => ((δ / 4 : ℝ) : ℂ) • 1) (fun _ => by simpa using PosSemidef.zero)
    have b2 := hk' _ (hT ν.1).1 (hT ν.1).2 hpd Z hZ'
    have tr : ∀ η : ℝ, ∑ τ : Ψ, ((T ν.1).map τ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re
        = η * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re := by
      intro η
      simp only [Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, re_ofReal_mul,
        Finset.mul_sum]
    have b3 : δ * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re ≤
        ∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re := by
      rw [← tr]
      refine Finset.sum_le_sum fun τ _ => ?_
      have := GlobalTheory.re_trace_mul_nonneg_of_posSemidef (ν.2 τ) (hZ τ)
      rw [Matrix.mul_sub, trace_sub, map_sub, sub_nonneg] at this
      exact this
    rw [tr] at b1
    rw [norm_mul, norm_e, pr_im (hT ν.1).1]
    refine (mul_le_mul_of_nonneg_right b1 (Real.exp_pos _).le).trans ?_
    rw [mul_assoc B, mul_assoc B, ← Real.exp_add, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0
    replace b2 : k * u ≤ _ := b2
    generalize ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re = p at b3 ⊢
    generalize ∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re = q at b2 b3 ⊢
    have := add_le_add (mul_le_mul_of_nonneg_left b2 Real.pi_pos.le)
      (mul_le_mul_of_nonneg_left b3 Real.pi_pos.le)
    linarith
  calc ‖f Z‖ * detIm Z ^ s ≤ B * Real.exp (-(π * k * u)) * σ * u ^ (d * s) := by
        rw [hus]; gcongr
    _ = u ^ (d * s) * Real.exp (-(π * k * u)) * σ * B := by ring
    _ ≤ C * σ * B := by gcongr; exact hC u hu0
end GlobalTheory.SW
