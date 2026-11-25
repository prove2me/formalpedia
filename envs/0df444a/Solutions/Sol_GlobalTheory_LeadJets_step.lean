-- Prove2me | solution 1 for GlobalTheory.LeadJets.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:37.941579+00:00
-- url     : https://prove2.me/submissions/a8203389-8ab4-4fb3-8e76-5d2de38c8e69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
import Theorems.Thm_GlobalTheory_LeadJets_leadVal_add
import Theorems.Thm_GlobalTheory_LeadJets_leadVal_diffOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_taylor_expansion_local_coordinates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics
open GlobalTheory GlobalTheory.LeadJets
noncomputable section
variable {n δ m : ℕ} {U : Fin m → Set (V n)} {f w : Fin m → V n → ℂ}
  {s : Fin m → V n → Fin n → ℂ} {t : Fin m → V n → Fin δ → ℂ}
namespace GlobalTheory.LeadJets
theorem _root_.solution {T a0 a : ℕ} (ha : a < a0) (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j)
    (cc : (Fin n → ℕ) → Fin δ → ℂ)
    (hcc : ∀ j, (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ cc' : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc') =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
  classical
  set ζ : Fin m → V n → V n := fun j z => (WithLp.toLp 2 fun k => s j z k / w j z : V n) with hζdef
  have loc : ∀ j, ∃ U' : Set (V n), IsOpen U' ∧ (0 : V n) ∈ U' ∧ U' ⊆ U j ∧
      (∀ v ∈ U', w j v ≠ 0) ∧ DifferentiableOn ℂ (ζ j) U' ∧ ζ j 0 = 0 := by
    intro j
    refine ⟨U j ∩ w j ⁻¹' {0}ᶜ, (hw j).continuousOn.isOpen_inter_preimage (hU j)
      isOpen_compl_singleton, ⟨h0 j, hw0 j⟩, Set.inter_subset_left, fun v hv => hv.2, ?_, ?_⟩
    · refine differentiableOn_euclidean.2 fun k => ?_
      have hdiv : DifferentiableOn ℂ (fun v => s j v k * (w j v)⁻¹) (U j ∩ w j ⁻¹' {0}ᶜ) :=
        ((hs j k).mono Set.inter_subset_left).mul
          (((hw j).mono Set.inter_subset_left).inv fun v hv => hv.2)
      exact hdiv.congr fun v _ => by simp [hζdef, div_eq_mul_inv]
    · ext k
      simp [hζdef, hs0]
  have hb : ∀ j, ∃ b : (Fin n → ℕ) → ℂ,
      (fun v => (f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) -
        ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    intro j
    obtain ⟨U', hUo, hxU, hUt, -, hζ, hζ0⟩ := loc j
    obtain ⟨b, hb⟩ := taylor_expansion_local_coordinates (a := a)
      (fun v => f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) (ζ j) U' 0 hUo hxU
      (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 cc)).mono hUt) hζ hζ0 (hcoord j)
      (by simpa only [sub_zero] using hcc j)
    exact ⟨b, by simpa only [sub_zero] using hb⟩
  choose bb hbb using hb
  choose dd hdd using fun α => hsurj (fun j => bb j α / w j 0 ^ T)
  refine ⟨fun α k => cc α k + if ∑ q, α q = a then dd α k else 0, fun j => ?_⟩
  obtain ⟨U', hUo, hxU, hUt, hUw, hζ, hζ0⟩ := loc j
  have hxt : U j ∈ 𝓝 (0 : V n) := (hU j).mem_nhds (h0 j)
  have hζO : (fun v => ζ j v) =O[𝓝 0] fun v => v := by
    have := (hζ.differentiableAt (hUo.mem_nhds hxU)).hasFDerivAt.isBigO_sub
    simpa only [hζ0, sub_zero] using this
  have hQ : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
      (fun v => ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ a := by
    intro α hα
    have hsum := Finset.Nat.mem_antidiagonalTuple.1 hα
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)).trans (hζO.norm_norm.pow a)
    calc ‖∏ k, ζ j v k ^ α k‖
        = ∏ k, ‖ζ j v k‖ ^ α k := by simp only [norm_prod, norm_pow]
      _ ≤ ∏ k, ‖ζ j v‖ ^ α k :=
          Finset.prod_le_prod (fun k _ => by positivity)
            (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ _) _)
      _ = 1 * ‖‖ζ j v‖ ^ a‖ := by
          rw [Finset.prod_pow_eq_pow_sum, hsum, one_mul, norm_pow, norm_norm]
  have hφ : ∀ α, (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k)
        =O[𝓝 0] fun v => ‖v‖ ^ 1 := by
    intro α
    have hd : DifferentiableAt ℂ (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k) 0 := by
      refine (differentiableAt_const _).sub ((((hw j).differentiableAt hxt).pow T).mul ?_)
      exact DifferentiableAt.fun_sum fun k _ => ((ht j k).differentiableAt hxt).const_mul _
    have h00 : bb j α - w j 0 ^ T * ∑ k, dd α k * t j 0 k = 0 := by
      rw [hdd α j, mul_div_cancel₀ _ (pow_ne_zero _ (hw0 j)), sub_self]
    have := hd.hasFDerivAt.isBigO_sub
    rw [h00] at this
    simp only [sub_zero] at this
    exact (this.trans (isBigO_refl _ _).norm_right).congr_right fun v => (pow_one _).symm
  have h2 : (fun v => ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
      (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
      =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    have hterm : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
        (fun v => (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) :=
      fun α hα => ((hφ α).mul (hQ α hα)).congr_right fun v => by ring
    exact (IsBigO.sum hterm).congr_left fun v => Finset.sum_apply _ _ _
  refine ((hbb j).add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hUo.mem_nhds hxU] with v hv
  beta_reduce
  rw [leadVal_add _ _ _ ha ha0 cc dd (hUw v hv)]
  simp only [hζdef, PiLp.toLp_apply, sub_mul, Finset.sum_sub_distrib]
  ring
end GlobalTheory.LeadJets
