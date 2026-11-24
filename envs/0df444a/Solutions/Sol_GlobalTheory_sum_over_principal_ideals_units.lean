-- Prove2me | solution 1 for GlobalTheory.sum_over_principal_ideals_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:08.727267+00:00
-- url     : https://prove2.me/submissions/7f900489-8caa-4b25-b694-c3c29e3df06f

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNonzeroIntegersPrincipalIdealsUnits
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [NumberField K] (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : 𝓞 K → E) : f 0 = 0 → ∀ (c : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → E) (β : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → (𝓞 K)ˣ → ℝ) (b : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → ℝ), (∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, HasSum (fun u : (𝓞 K)ˣ => f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))) (c J)) → (∀ (J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}) (u : (𝓞 K)ˣ), ‖f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))‖ ≤ β J u) → (∀ J, HasSum (β J) (b J)) → Summable b → HasSum f (∑' J, c J) := by
  intro hf0 c β b hc hbd hβ hbs
  classical
  let gen : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → 𝓞 K := fun J => haveI := J.2.2; Submodule.IsPrincipal.generator J.1
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {gen J} = J.1 := fun J => by
    haveI := J.2.2
    exact Submodule.IsPrincipal.span_singleton_generator J.1
  have hgen0 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, gen J ≠ 0 := fun J => by
    intro h
    apply J.2.1
    rw [← hspan J, h, Ideal.span_singleton_eq_bot]
  let g : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) → 𝓞 K := fun p => (p.2 : 𝓞 K) * gen p.1
  have hginj : Function.Injective g := by
    rintro ⟨J, u⟩ ⟨J', u'⟩ h
    simp only [g] at h
    have hJ : J = J' := by
      apply Subtype.ext
      rw [← hspan J, ← hspan J', Ideal.span_singleton_eq_span_singleton]
      have h1 : gen J = ((u⁻¹ * u' : (𝓞 K)ˣ) : 𝓞 K) * gen J' := by
        rw [Units.val_mul, mul_assoc, ← h, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rw [h1]
      exact (associated_unit_mul_left _ _ (Units.isUnit _))
    subst hJ
    have hu : u = u' := Units.ext (mul_right_cancel₀ (hgen0 J) h)
    subst hu
    rfl
  have hrange : ∀ x ∉ Set.range g, f x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, hf0]
    · exfalso
      apply hx
      let J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} := ⟨Ideal.span {x}, by rwa [Ne, Ideal.span_singleton_eq_bot], ⟨⟨x, rfl⟩⟩⟩
      have hass : Associated (gen J) x := by
        rw [← Ideal.span_singleton_eq_span_singleton, hspan J]
      obtain ⟨u, hu⟩ := hass
      exact ⟨⟨J, u⟩, by simp only [g]; rw [mul_comm]; exact hu⟩
  have hnorm : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => β p.1 p.2) := by
    rw [summable_sigma_of_nonneg]
    · refine ⟨fun J => (hβ J).summable, ?_⟩
      simpa [(hβ _).tsum_eq] using hbs
    · intro p
      exact (norm_nonneg _).trans (hbd p.1 p.2)
  have hF : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => f (g p)) :=
    Summable.of_norm_bounded hnorm (fun p => hbd p.1 p.2)
  have hcs : HasSum c (∑' p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ), f (g p)) :=
    HasSum.sigma hF.hasSum (fun J => hc J)
  rw [hcs.tsum_eq]
  exact (hginj.hasSum_iff hrange).mp hF.hasSum
end GlobalTheory
