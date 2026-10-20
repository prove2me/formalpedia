-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeakSequences.bidual_separate_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:36:30.607207+00:00
-- url     : https://prove2.me/submissions/4f716016-2608-41d6-ad56-8964f01c04b3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/BidualSeparation.lean:L39-L87
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.bidual_separate_finite. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation

-- ---- from OAI.Analysis.LipschitzEquivalence.BidualSeparation ----
namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped NNReal Topology BigOperators
open Filter Set
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_unit_pos_of_lt_norm (T : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) (hT : c < ‖T‖) :
    ∃ x : E, ‖x‖ = 1 ∧ c < T x := by
  have hnot : ¬ ∀ x : E, ‖T x‖ ≤ c*‖x‖ := by
    intro h
    exact (not_le.mpr hT) (T.opNorm_le_bound hc h)
  push Not at hnot
  obtain ⟨x,hx⟩ := hnot
  have hxnorm : 0 < ‖x‖ := by
    by_contra! h
    have : x = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    simp [this] at hx
  let y : E := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by
    rw [norm_smul,norm_inv,Real.norm_of_nonneg hxnorm.le,inv_mul_cancel₀ hxnorm.ne']
  have hTy : c < |T y| := by
    change c < |T (‖x‖⁻¹ • x)|
    rw [map_smul,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hxnorm]
    rw [← Real.norm_eq_abs]
    have h := mul_lt_mul_of_pos_left hx (inv_pos.mpr hxnorm)
    have he : ‖x‖⁻¹ * (c * ‖x‖) = c := by
      rw [mul_left_comm,inv_mul_cancel₀ hxnorm.ne',mul_one]
    rwa [he] at h
  rcases le_total 0 (T y) with hpos | hneg
  · exact ⟨y,hy,by simpa only [abs_of_nonneg hpos] using hTy⟩
  · exact ⟨-y,by simpa using hy,by simpa only [map_neg,abs_of_nonpos hneg] using hTy⟩

theorem bidual_separate_finite (φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ) {d : ℝ} (hd : 0 < d)
    (hfar : ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖)
    {n : ℕ} (x : Fin n → E) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ = 1 ∧ (∀ i, f (x i) = 0) ∧ d/2 < φ f := by
  classical
  let A : (E →L[ℝ] ℝ) →ₗ[ℝ] (Fin n → ℝ) := {
    toFun := fun f i => f (x i)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let p : Submodule ℝ (E →L[ℝ] ℝ) := A.ker
  let : NormedAddCommGroup p := inferInstance
  let : NormedSpace ℝ p := inferInstance
  let φp : p →L[ℝ] ℝ := φ.comp p.subtypeL
  obtain ⟨ψ,hψ,hψnorm⟩ := exists_extension_norm_eq p φp
  have hann : (φ-ψ).toLinearMap ∈ (A.ker).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro f hf
    change φ f-ψ f = 0
    exact sub_eq_zero.mpr (hψ ⟨f,hf⟩).symm
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker A] at hann
  obtain ⟨l,hl⟩ := hann
  let z : E := ∑ i, l (Pi.single i 1) • x i
  have heq : φ-ψ = NormedSpace.inclusionInDoubleDual ℝ E z := by
    ext f
    have hlf := DFunLike.congr_fun hl f
    change l (A f) = φ f-ψ f at hlf
    change φ f-ψ f = f z
    rw [← hlf]
    change l (fun i => f (x i)) = f (∑ i, l (Pi.single i 1) • x i)
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
    have hexp : (fun i => f (x i)) = ∑ i, f (x i) • (Pi.single i 1 : Fin n → ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hexp,map_sum]
    simp only [map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdnorm : d ≤ ‖φp‖ := by
    have h := hfar z
    rw [← heq] at h
    have he : φ-(φ-ψ) = ψ := by ext f; simp
    rw [he,hψnorm] at h
    exact h
  obtain ⟨f,hfnorm,hfφ⟩ := exists_unit_pos_of_lt_norm φp (half_pos hd).le (by linarith)
  refine ⟨f.val,hfnorm,?_,hfφ⟩
  intro i
  exact congr_fun f.property i

end LipschitzCounterexample.WeakSequences
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
open scoped NNReal Topology BigOperators
open Filter Set


theorem solution.{uE} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.bidual_separate_finite.{uE} := @_root_.OAI.LipschitzCounterexample.WeakSequences.bidual_separate_finite.{uE}
