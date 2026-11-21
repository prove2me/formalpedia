-- Prove2me | solution 1 for MasulloGRH.scalar_expansion_of_weak_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:26:38.102192+00:00
-- url     : https://prove2.me/submissions/66c56334-ccfd-4ee9-a98d-28ba84ceb453

import Theorems.Thm_MasulloGRH_exists_tendsto_atTop_summable_mul
import Theorems.Thm_MasulloGRH_summable_smul_of_isVonNBounded
import Theorems.Thm_MasulloGRH_eq_of_forall_strongDual_eq
import Theorems.Thm_MasulloGRH_tendsto_smul_zero_of_isVonNBounded

set_option autoImplicit false

open MasulloGRH

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hL : IsHLCS G)
    (B : Set G) (w : ℕ → G) (Y : ℕ → StrongDual ℂ G) (c : ℕ → ℝ)
    (hw : Bornology.IsVonNBounded ℂ (Set.range w)) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c)
    (hY : ∀ n, ∀ x ∈ B, ‖Y n x‖ ≤ 1)
    (hrep : ∀ (f : StrongDual ℂ G), ∀ x ∈ B,
      HasSum (fun n => (c n : ℂ) * Y n x * f (w n)) (f x)) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ) (a : ℕ → (Submodule.span ℂ B) →ₗ[ℂ] ℂ),
      Filter.Tendsto y Filter.atTop (nhds (0 : G)) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n (x : Submodule.span ℂ B), (x : G) ∈ B → ‖a n x‖ ≤ c n) ∧
      ∀ x : Submodule.span ℂ B, HasSum (fun n => a n x • y n) (x : G) := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hL
  haveI := hp.topologicalAddGroup
  haveI := hp.continuousSMul
  obtain ⟨μ, hμ1, hμ, hcμ⟩ := exists_tendsto_atTop_summable_mul c hc0 hc
  have hμ0 : ∀ n, (μ n : ℂ) ≠ 0 := fun n => by
    have := hμ1 n; exact_mod_cast (show μ n ≠ 0 by linarith)
  -- main claim: for x in span B the weak series converges to x
  have key : ∀ x ∈ Submodule.span ℂ B,
      HasSum (fun n => ((c n : ℂ) * Y n x) • w n) x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hxB =>
      have hs : Summable (fun n => ((c n : ℂ) * Y n x) • w n) := by
        apply summable_smul_of_isVonNBounded G hC ⟨⟨ι, ‹_›, p, hp⟩, hT2⟩ w hw
        refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hc
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)]
        nlinarith [hY n x hxB, hc0 n, norm_nonneg (Y n x)]
      obtain ⟨S, hS⟩ := hs
      have : S = x := by
        apply eq_of_forall_strongDual_eq G ⟨⟨ι, ‹_›, p, hp⟩, hT2⟩
        intro f
        have h1 := f.hasSum hS
        have h2 := hrep f x hxB
        refine h1.unique ?_
        simpa [map_smul, smul_eq_mul] using h2
      subst this; exact hS
    | zero => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : G)) 0)
    | add x z _ _ hx hz =>
      simpa [map_add, mul_add, add_smul] using hx.add hz
    | smul t x _ hx =>
      have := hx.const_smul t
      convert this using 1
      funext n
      simp [map_smul, smul_smul, smul_eq_mul]
      ring_nf
  refine ⟨fun n => ((μ n)⁻¹ : ℂ) • w n, fun n => c n * μ n,
    fun n => ((c n * μ n : ℝ) : ℂ) • ((Y n).toLinearMap ∘ₗ (Submodule.span ℂ B).subtype),
    ?_, ?_, hcμ, ?_, ?_⟩
  · apply tendsto_smul_zero_of_isVonNBounded G ⟨⟨ι, ‹_›, p, hp⟩, hT2⟩ w hw
    have : Filter.Tendsto (fun n => (μ n)⁻¹) Filter.atTop (nhds 0) := hμ.inv_tendsto_atTop
    have := (Complex.continuous_ofReal.tendsto 0).comp this
    simpa [Function.comp_def] using this
  · intro n; exact mul_nonneg (hc0 n) (by linarith [hμ1 n])
  · intro n x hxB
    simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, ContinuousLinearMap.coe_coe, smul_eq_mul, norm_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hc0 n) (by linarith [hμ1 n]))]
    have := hY n x hxB
    have h0 : 0 ≤ c n * μ n := mul_nonneg (hc0 n) (by linarith [hμ1 n])
    nlinarith [norm_nonneg (Y n x)]
  · intro x
    convert key x x.2 using 1
    funext n
    simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, ContinuousLinearMap.coe_coe, smul_eq_mul, smul_smul]
    congr 1
    have := hμ0 n
    push_cast
    field_simp
