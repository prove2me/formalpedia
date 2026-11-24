-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:17.974357+00:00
-- url     : https://prove2.me/submissions/ac2cde48-b786-4072-bc59-6aa5edf4a28f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFourierUnfolding
import Theorems.Thm_GlobalTheory_CompanionTheory_UnfoldAbs_hasSum_integral_of_norm_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_UnfoldAbs_setIntegral_eq_zero_of_translate
import Theorems.Thm_GlobalTheory_CompanionTheory_UnfoldAbs_integrable_of_lattice_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnfoldAbs
namespace GlobalTheory.CompanionTheory.UnfoldAbs
theorem _root_.solution : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ)
    (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  intro A X Y _ _ _ lam _ Λ _ 𝓖 h𝓖 h1 _ c y0 F F0 ch hF hch hnorm hmul hΛ M hb τ hτ hcτ e he hfib
    hF0 hν
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by simp [h1]⟩

  have hsub : ∀ {Z : Type} (j : Z → X), Function.Injective j → ∀ b,
      Summable (fun z => ‖F (j z) b‖) ∧ ∑' z, ‖F (j z) b‖ ≤ M := by
    intro Z j hj b
    refine ⟨(hb b).1.comp_injective hj, ?_⟩
    exact (tsum_comp_le_tsum_of_inj (hb b).1 (fun _ => norm_nonneg _) hj).trans (hb b).2
  have key : ∀ {Z : Type} [Countable Z] (j : Z → X), Function.Injective j →
      HasSum (fun z => ∫ b in 𝓖, F (j z) b * ch b ∂lam)
        (∫ b in 𝓖, (∑' z, F (j z) b) * ch b ∂lam) := by
    intro Z _ j hj
    have := hasSum_integral_of_norm_bound (lam.restrict 𝓖) (fun z b => F (j z) b * ch b)
      (fun z => ((hF (j z)).mul hch).restrict) M (fun b => by
        simpa [hnorm] using hsub j hj b)
    simpa only [tsum_mul_right] using this

  have hF0e : F0 = F (e 0) := by
    funext b
    have := hF0 0 b
    simpa using this.symm
  have hint0 : Integrable F0 lam := by
    refine integrable_of_lattice_bound lam Λ 𝓖 h𝓖 h1 F0 (hF0e ▸ hF (e 0)) M (fun b => ?_)
    simpa only [hF0] using hsub e he b
  refine ⟨hint0, ?_⟩

  have hT := key (Z := X) id Function.injective_id
  simp only [id] at hT
  have hsig := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hT
  have hg : HasSum (fun y => ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam)
      (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) :=
    hsig.sigma (fun y => key (Z := {x // c x = y}) Subtype.val Subtype.val_injective)

  have hzero : ∀ y, y ≠ y0 → ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam = 0 := by
    intro y hy
    obtain ⟨ν, hν1, hνq⟩ := hν y hy
    refine setIntegral_eq_zero_of_translate lam Λ 𝓖 h𝓖 _ ν (ch ν) hν1 (fun l b => ?_) (fun b => ?_)
    · have hs : ∑' z : {x // c x = y}, F z ((l : A) + b) = ∑' z : {x // c x = y}, F z b := by
        calc ∑' z : {x // c x = y}, F z ((l : A) + b)
            = ∑' z : {x // c x = y}, F (τ l z) b := tsum_congr fun z => hτ l z b
          _ = ∑' z : {x // c x = y}, F z b :=
            ((τ l).subtypeEquiv (p := fun x => c x = y) (q := fun x => c x = y)
              (fun a => by rw [hcτ])).tsum_eq (fun z : {x // c x = y} => F z b)
      rw [hs, hmul, hΛ, one_mul]
    · have hs : ∑' z : {x // c x = y}, F z (ν + b) = ∑' z : {x // c x = y}, F z b :=
        tsum_congr fun z => hνq z z.2 b
      rw [hs, hmul]
      ring
  have hT' := hg.unique (hasSum_single y0 (fun y hy => hzero y hy))
  rw [hT']

  let ee : Λ ≃ {x // c x = y0} := Equiv.ofBijective
    (fun l => ⟨e l, (hfib _).2 ⟨l, rfl⟩⟩)
    ⟨fun a b h => he (congrArg Subtype.val h), fun q => by
      obtain ⟨l, hl⟩ := (hfib q).1 q.2
      exact ⟨l, Subtype.ext hl⟩⟩
  have hsum : ∀ b, ∑' z : {x // c x = y0}, F z b = ∑' l : Λ, F (e l) b := fun b =>
    (ee.tsum_eq (fun z => F z b)).symm
  simp_rw [hsum]
  rw [← (key e he).tsum_eq]
  have hint1 : Integrable (fun b => F0 b * ch b) lam :=
    hint0.mono (hint0.aestronglyMeasurable.mul hch) (ae_of_all _ fun b => by simp [hnorm])
  rw [h𝓖.integral_eq_tsum'' _ hint1]
  refine tsum_congr fun l => ?_
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  change F (e l) b * ch b = F0 ((l : A) + b) * ch ((l : A) + b)
  rw [hF0, hmul, hΛ, one_mul]
end GlobalTheory.CompanionTheory.UnfoldAbs
