-- Prove2me | solution 1 for GlobalTheory.cloud_node_projection_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:55.577166+00:00
-- url     : https://prove2.me/submissions/6d939826-f915-44f2-9ff8-b2d6277484f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterLeSuccAndSqSumLePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormEigenLePowMulNormSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasEigenvalueSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevSubspaceMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSumEigenprojectorLeOfResolventBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CloudNodeProjectionNormLowLevel
import Theorems.Thm_GlobalTheory_cloud_node_projector_bound
import Theorems.Thm_GlobalTheory_T_splitCasimir_resolvent_circle_bounds
import Theorems.Thm_GlobalTheory_T_unitary_glModule_proj_components_level_add_two
import Theorems.Thm_GlobalTheory_card_filter_le_succ_and_sq_sum_le_pow
import Theorems.Thm_GlobalTheory_lev_subspace_mono
import Theorems.Thm_GlobalTheory_shape_position
import Theorems.Thm_GlobalTheory_splitCas_eigenvalue_summand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hM hF hA hS hj hw c
  obtain ⟨hb, -, hpos⟩ := GlobalTheory.shape_position n kk j ε μ bv hS (by omega)
  obtain ⟨L0, Ladd, Lsmul, -⟩ := GlobalTheory.lev_subspace_mono M n ε E μ hM.1 hM.2.1
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hM.2.1 (fun s => (hF s).2.1) hA hw
  have heig := GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hM hF hA
  have hnb : (n : ℝ) ≤ bv := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by have := hS.2.1; omega : 1 ≤ n)
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ h1 (by norm_num)
    have h3 := hS.2.2.2.2.2
    have h4 : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    linarith
  have hcard := (GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv hS.1 hS.2.1 hnb).1
  let e : PiLp 2 (fun _ : Fin n => M) ≃ₗ[ℂ] (Fin n → M) := WithLp.linearEquiv 2 ℂ (Fin n → M)
  have hn : ∀ x : PiLp 2 (fun _ : Fin n => M), ‖x‖ ^ 2 = ∑ d, ‖e x d‖ ^ 2 := fun x => PiLp.norm_sq_eq_of_L2 _ x
  let T0 : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
    LinearMap.pi fun b => -∑ a, (E b a) ∘ₗ (LinearMap.proj a : (Fin n → M) →ₗ[ℂ] M)
  have hT0 : ∀ x, T0 x = splitCas E x := by
    intro x
    funext b
    simp [T0, splitCas]
  let T : PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := e.symm.toLinearMap ∘ₗ T0 ∘ₗ e.toLinearMap
  have hT : ∀ x, e (T x) = splitCas E (e x) := by
    intro x
    rw [← hT0]
    exact e.apply_symm_apply _
  let p : Fin n → PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := fun s =>
    e.symm.toLinearMap ∘ₗ io s ∘ₗ pr s ∘ₗ e.toLinearMap
  have hp : ∀ s x, e (p s x) = io s (pr s (e x)) := fun s x => e.apply_symm_apply _
  let x₀ : PiLp 2 (fun _ : Fin n => M) := e.symm (Pi.single c w)
  have hx₀ : e x₀ = Pi.single c w := e.apply_symm_apply _
  have hx₀n : ‖x₀‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [hn, hx₀, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [hd]
    · simp
  let VV : Submodule ℂ (PiLp 2 (fun _ : Fin n => M)) := Submodule.span ℂ (Set.range fun s => p s x₀)
  have hfd : FiniteDimensional ℂ VV := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hsum : ∀ x, ∑ i, p i x = x := by
    intro x
    apply e.injective
    rw [map_sum]
    simp only [hp]
    exact hA.sum_io_pr _
  have hx₀V : x₀ ∈ VV := by
    rw [← hsum x₀]
    exact VV.sum_mem fun i _ => Submodule.subset_span ⟨i, rfl⟩
  have hpV : ∀ i, ∀ x ∈ VV, p i x ∈ VV := by
    intro i x hx
    have : VV ≤ VV.comap (p i) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      show p i (p s x₀) ∈ VV
      by_cases h : i = s
      · subst h
        have : p i (p i x₀) = p i x₀ := by
          apply e.injective
          rw [hp, hp, hA.pr_io]
        rw [this]
        exact Submodule.subset_span ⟨i, rfl⟩
      · have : p i (p s x₀) = 0 := by
          apply e.injective
          rw [hp, hp, hA.pr_io_ne i s h, map_zero, map_zero]
        rw [this]
        exact VV.zero_mem
    exact this hx
  have hlev : ∀ x ∈ VV, ∀ d, Lev ε E μ (j + 2) (e x d) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      intro d
      rw [hp, hx₀]
      exact hcomp s c d
    | zero => intro d; rw [map_zero]; exact L0 _
    | add x y _ _ hx hy => intro d; rw [map_add]; exact Ladd _ _ _ (hx d) (hy d)
    | smul a x _ hx => intro d; rw [map_smul]; exact Lsmul _ _ _ (hx d)
  have hres := fun x (hx : x ∈ VV) =>
    GlobalTheory.T.splitCasimir_resolvent_circle_bounds M n ε E μ kk (j + 2) bv (e x) hM hS (by omega) (hlev x hx)
  have key := cloud_node_projector_bound (PiLp 2 (fun _ : Fin n => M)) n kk bv VV T p
    (fun s => -μ s + (1 - (n : ℝ)) / 2) hfd hb hsum ?_ hpos ?_ hcard ?_ ?_ x₀ hx₀V
  · refine ⟨?_, fun s hs => ?_⟩
    · have h := pow_le_pow_left₀ (norm_nonneg _) key.1 2
      rw [mul_pow, hx₀n, hn, map_sum] at h
      simp only [hp, hx₀] at h
      exact h
    · have h := pow_le_pow_left₀ (norm_nonneg _) (key.2 s hs) 2
      rw [mul_pow, hx₀n, hn, hp, hx₀] at h
      exact h
  · intro i x hx
    refine ⟨hpV i x hx, ?_⟩
    apply e.injective
    rw [hT, map_smul, hp, heig]
  · intro a b hab
    rw [le_abs]
    rcases lt_or_gt_of_ne hab with h | h
    · right
      have := hS.2.2.1 a b h
      linarith
    · left
      have := hS.2.2.1 b a h
      linarith
  · intro ζ hζ x hx
    have h := (hres x hx).1 ζ hζ
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, map_sub, map_smul, hT]
    exact h
  · intro x hx
    have h := (hres x hx).2
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, hT]
    exact h
end GlobalTheory
