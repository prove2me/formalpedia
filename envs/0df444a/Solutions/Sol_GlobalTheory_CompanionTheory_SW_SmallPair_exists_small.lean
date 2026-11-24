-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SmallPair.exists_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:07.863702+00:00
-- url     : https://prove2.me/submissions/ee8a3b55-5c4f-4eb7-a474-f325cb2c782c

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_bigM_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_det_bigM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SmallPair
namespace GlobalTheory.CompanionTheory.SW.SmallPair
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ]
    [Nonempty ι]
    (b : Module.Basis κ ℝ (ι → ℝ)) (S : AddSubgroup (ι → ℝ)) (hS : ∀ i, b i ∈ S) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ τ : ι → ℂ, (∀ w, 0 < (τ w).im) →
      ∃ u ∈ S, ∃ v ∈ S, (u ≠ 0 ∨ v ≠ 0) ∧ ∀ w,
        |√(τ w).im * u w| ≤ R ∧ |(τ w).re / √(τ w).im * u w + 1 / √(τ w).im * v w| ≤ R := by
  classical
  let b₂ : Module.Basis ((_ : Fin 2) × κ) ℝ (Fin 2 × ι → ℝ) :=
    (Pi.basis fun _ : Fin 2 => b).map (LinearEquiv.curry ℝ ℝ (Fin 2) ι).symm
  have hb₂ : ∀ (ji : (_ : Fin 2) × κ) (k : Fin 2) (w : ι),
      b₂ ji (k, w) = (Pi.single ji.1 (b ji.2) : Fin 2 → ι → ℝ) k w := by
    intro ji k w
    simp [b₂, Module.Basis.map_apply, Pi.basis_apply]
  have hfund := ZSpan.isAddFundamentalDomain' b₂ (volume : Measure (Fin 2 × ι → ℝ))
  have hfin : volume (ZSpan.fundamentalDomain b₂) ≠ ∞ :=
    (ZSpan.fundamentalDomain_isBounded b₂).measure_lt_top.ne
  set V : ℝ := (volume (ZSpan.fundamentalDomain b₂)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hproj : ∀ z ∈ Submodule.span ℤ (Set.range b₂), ∀ k : Fin 2,
      (fun w => z (k, w)) ∈ S := by
    intro z hz k
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ji, rfl⟩ := hx
      by_cases hk : k = ji.1
      · subst hk
        have : (fun w => b₂ ji (ji.1, w)) = b ji.2 := by
          funext w; simp [hb₂]
        rw [this]; exact hS _
      · have : (fun w => b₂ ji (k, w)) = 0 := by
          funext w; simp [hb₂, Pi.single_eq_of_ne hk]
        rw [this]; exact S.zero_mem
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx =>
      have : (fun w => (a • x) (k, w)) = a • (fun w => x (k, w)) := by
        funext w; simp
      rw [this]; exact S.zsmul_mem hx a
  refine ⟨V + 1, by positivity, fun τ hτ => ?_⟩
  let f : (Fin 2 × ι → ℝ) →ₗ[ℝ] (Fin 2 × ι → ℝ) := Matrix.toLin' (bigM τ)
  have hdet : LinearMap.det f = 1 := by
    simp only [f, LinearMap.det_toLin', det_bigM τ hτ]
  let s : Set (Fin 2 × ι → ℝ) := f ⁻¹' Metric.closedBall 0 (V + 1)
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simpa [s, map_neg] using hx
  have hconv : Convex ℝ s := (convex_closedBall _ _).linear_preimage f
  have hcard : 1 ≤ Fintype.card (Fin 2 × ι) := Fintype.card_pos
  have hvol : volume (ZSpan.fundamentalDomain b₂) * 2 ^ Module.finrank ℝ (Fin 2 × ι → ℝ)
      < volume s := by
    rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact one_ne_zero),
      hdet, Real.volume_pi_closedBall _ (by positivity), Module.finrank_fintype_fun_eq_card]
    have h1 : volume (ZSpan.fundamentalDomain b₂) = ENNReal.ofReal V :=
      (ENNReal.ofReal_toReal hfin).symm
    rw [h1]
    simp only [inv_one, abs_one, ENNReal.ofReal_one, one_mul]
    have h2 : (2 : ℝ≥0∞) ^ Fintype.card (Fin 2 × ι)
        = ENNReal.ofReal (2 ^ Fintype.card (Fin 2 × ι)) := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    rw [h2, ← ENNReal.ofReal_mul hV0]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    rw [mul_pow, mul_comm]
    have h3 : V < (V + 1) ^ Fintype.card (Fin 2 × ι) :=
      calc V < V + 1 := by linarith
        _ = (V + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ (by linarith) hcard
    exact mul_lt_mul_of_pos_left h3 (by positivity)
  have hcount : Countable (Submodule.span ℤ (Set.range b₂)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b₂))
    infer_instance
  obtain ⟨⟨x, hx⟩, hne, hmem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund hsymm hconv hvol
  have hx' : x ∈ Submodule.span ℤ (Set.range b₂) := hx
  refine ⟨_, hproj x hx' 0, _, hproj x hx' 1, ?_, fun w => ?_⟩
  · by_contra hcon
    push_neg at hcon
    apply hne
    apply Subtype.ext
    funext ⟨k, w⟩
    fin_cases k
    · exact congrFun hcon.1 w
    · exact congrFun hcon.2 w
  · have hball : ‖f x‖ ≤ V + 1 := by
      simpa [s] using hmem
    have hco : ∀ k, |f x (k, w)| ≤ V + 1 := fun k => by
      have := (pi_norm_le_iff_of_nonneg (by positivity)).mp hball (k, w)
      simpa using this
    have e : ∀ k, f x (k, w) = ∑ j, block (τ w) k j * x (j, w) := fun k => by
      simp only [f, Matrix.toLin'_apply]
      exact bigM_mulVec τ x k w
    have h0 := hco 0
    have h1 := hco 1
    rw [e] at h0 h1
    simpa [block, Fin.sum_univ_two] using And.intro h0 h1
end GlobalTheory.CompanionTheory.SW.SmallPair
