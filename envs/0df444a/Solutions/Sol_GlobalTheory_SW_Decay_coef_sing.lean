-- Prove2me | solution 1 for GlobalTheory.SW.Decay.coef_sing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:46.576383+00:00
-- url     : https://prove2.me/submissions/b53ec5bb-321b-4b23-a338-6576dd41b894

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
import Theorems.Thm_GlobalTheory_SW_Decay_volume_cube
import Theorems.Thm_GlobalTheory_SW_Decay_imH_xy
import Theorems.Thm_GlobalTheory_SW_Decay_posDef_of_ge
import Theorems.Thm_GlobalTheory_SW_Decay_norm_integrand_le
import Theorems.Thm_GlobalTheory_SW_Decay_trace_vecMulVec
import Theorems.Thm_GlobalTheory_IsSiegel_smul


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Decay
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}
variable {m : ℕ} {X : (Fin m → ℝ) → CM Ψ N N} {f : CM Ψ N N → ℂ} {T : Matrix (Fin N) (Fin N) E}
  {a : ℂ} {η B : ℝ}
namespace GlobalTheory.SW.Decay
theorem _root_.solution (hXc : Continuous X) (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T)
    (hη : 0 < η)
    (hf : DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N})
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) {v : Fin N → E}
    (hv : ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0))
    (hTv : T *ᵥ v = 0) : a = 0 := by
  set P : CM Ψ N N := fun τ => vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) with hP
  set Y : ℝ → CM Ψ N N := fun t τ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (t : ℂ) • P τ
    with hYdef
  have hY : ∀ t, 0 ≤ t → ∀ τ, (Y t τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
    intro t ht τ
    simp only [hYdef, add_sub_cancel_left]
    exact (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have hTP : ∀ τ : Ψ, (T.map τ.1 * P τ).trace = 0 := by
    intro τ
    rw [hP, trace_vecMulVec]
    have : T.map τ.1 *ᵥ (fun a => τ.1 (v a)) = 0 := by
      ext i
      have := congrArg τ.1 (congrFun hTv i)
      simpa [mulVec, dotProduct] using this
    rw [this, dotProduct_zero]
  have hpush : ∀ x t, (fun τ => X x τ + I • Y t τ) = pushZ Ψ (fun τ => X x τ + I • Y 0 τ) v t := by
    intro x t
    funext τ
    simp only [hYdef, pushZ, hP, smul_add, smul_smul, ofReal_zero, mul_zero, zero_smul, add_zero,
      add_assoc]
    rfl
  have hpr : ∀ x t, pr T (fun τ => X x τ + I • Y t τ) = pr T (fun τ => X x τ + I • Y 0 τ) := by
    intro x t
    simp [pr, hYdef, Matrix.mul_add, hTP]
  have htr : ∀ t, ∑ τ : Ψ, (T.map τ.1 * Y t τ).trace.re = ∑ τ : Ψ, (T.map τ.1 * Y 0 τ).trace.re := by
    intro t
    simp [hYdef, Matrix.mul_add, hTP]
  have hH : ∀ t, 0 ≤ t → ∀ x, (fun τ => X x τ + I • Y t τ) ∈ Hn Ψ N := fun t ht x τ => by
    have := posDef_of_ge hη (hY t ht τ)
    simpa only [imH_xy (hX x τ) this.1] using this
  haveI : IsFiniteMeasure (volume.restrict (cube m)) :=
    isFiniteMeasure_restrict.2 (by rw [volume_cube]; exact ENNReal.one_ne_top)
  have lim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (cube m))
    (l := atTop) (F := fun (t : ℝ) x => f (fun τ => X x τ + I • Y t τ) *
      cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y t τ)))) (f := fun _ => 0)
    (fun _ => B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y 0 τ).trace.re))
    ((eventually_ge_atTop 0).mono fun t ht => by
      have hc : Continuous fun x => (fun τ => X x τ + I • Y t τ : CM Ψ N N) :=
        hXc.add continuous_const
      refine (Continuous.mul (hf.continuousOn.comp_continuous hc (hH t ht)) ?_).aestronglyMeasurable
      refine Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul ?_))
      exact continuous_finset_sum _ fun τ _ =>
        (continuous_const.matrix_mul ((continuous_apply τ).comp hc)).matrix_trace)
    ((eventually_ge_atTop 0).mono fun t ht => ae_of_all _ fun x => by
      rw [← htr t]; exact norm_integrand_le hX hT hη hB (hY t ht) x)
    (integrable_const _)
    (ae_of_all _ fun x => by
      have := (hv _ (hH 0 le_rfl x)).mul_const
        (cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y 0 τ))))
      rw [zero_mul] at this
      exact this.congr fun t => by rw [hpr x t, hpush x t])
  rw [integral_zero] at lim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) lim
  exact (eventually_ge_atTop 0).mono fun t ht => ha _ fun τ => posDef_of_ge hη (hY t ht τ)
end GlobalTheory.SW.Decay
