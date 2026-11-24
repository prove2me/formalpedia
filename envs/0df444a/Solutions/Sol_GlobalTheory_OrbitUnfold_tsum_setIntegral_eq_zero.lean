-- Prove2me | solution 1 for GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:34:05.080858+00:00
-- url     : https://prove2.me/submissions/678847e1-910e-4e1c-8a04-9bccb7fa1fc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits
import Theorems.Thm_GlobalTheory_OrbitUnfold_nullMeasurableSet_pull
import Theorems.Thm_GlobalTheory_OrbitUnfold_aedisjoint_pull
import Theorems.Thm_GlobalTheory_OrbitUnfold_setIntegral_pull
import Theorems.Thm_GlobalTheory_OrbitUnfold_setLIntegral_pull
import Theorems.Thm_GlobalTheory_OrbitUnfold_isFundamentalDomain_iUnion_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Set
open scoped ENNReal Pointwise
namespace GlobalTheory
namespace OrbitUnfold
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
private theorem selfEquivSigmaOrbits_symm_mk {G X : Type} [Group G] [MulAction G X]
    (ω : MulAction.orbitRel.Quotient G X) (x : MulAction.orbit G ω.out) :
    (MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, x⟩ = x := rfl
end OrbitUnfold
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
open GlobalTheory.OrbitUnfold
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
namespace GlobalTheory.OrbitUnfold
namespace _root_.GlobalTheory.OrbitUnfold
theorem _root_.solution :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H)
      [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y]
      [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ,
      (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) →
      ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ →
      (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν →
        IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) →
      ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  intro H _ _ _ ν _ Γ _ Y _ _ 𝓕 hF Φ hmeas hinv hfin hzero
  have horbit : ∀ y₀ : Y, ∑' a : MulAction.orbit Γ y₀, ∫ h in 𝓕, Φ a h ∂ν = 0 := by
    intro y₀
    have hO : ∀ γ : Γ, γ • y₀ ∈ MulAction.orbit Γ y₀ := fun γ => MulAction.mem_orbit y₀ γ
    choose σ hσ using fun a : MulAction.orbit Γ y₀ =>
      (MulAction.mem_orbit_iff.1 a.2 : ∃ g : Γ, g • y₀ = a)
    have hT := _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO σ hσ
    have hshift : ∀ a : MulAction.orbit Γ y₀, ∀ h, Φ a ((σ a : H) * h) = Φ y₀ h := fun a h => by
      rw [← hinv (σ a) y₀ h, hσ]
    have hpt : ∀ a : MulAction.orbit Γ y₀,
        ∫ h in 𝓕, Φ a h ∂ν = ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), Φ y₀ h ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (σ a : H) (Φ a)]
      simp only [hshift]
    have hlpt : ∀ a : MulAction.orbit Γ y₀,
        ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (σ a : H) (fun h => ‖Φ a h‖ₑ)]
      simp only [hshift]
    have hσinj : Function.Injective σ := fun a b hab =>
      Subtype.ext (by rw [← hσ a, ← hσ b, hab])
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν)
        fun a : MulAction.orbit Γ y₀ => _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) :=
      fun a b hab => _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull hF (hσinj.ne hab)
    have hint : IntegrableOn (Φ y₀)
        (⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
      refine ⟨(hmeas y₀).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ h in ⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν
          ≤ ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν :=
            lintegral_iUnion_le _ _
        _ = ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by simp only [hlpt]
        _ ≤ ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
            ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
        _ < ⊤ := lt_top_iff_ne_top.2 hfin
    simp only [hpt]
    rw [← integral_iUnion_ae (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hdisj hint]
    exact hzero y₀ _ hT hint
  have hsum : Summable fun y => ∫ h in 𝓕, Φ y h ∂ν := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun y => ?_
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono (ENNReal.ne_top_of_tsum_ne_top hfin y)
      (enorm_integral_le_lintegral_enorm _)
  have hs' := ((MulAction.selfEquivSigmaOrbits Γ Y).symm.summable_iff
    (f := fun y => ∫ h in 𝓕, Φ y h ∂ν)).2 hsum
  rw [← (MulAction.selfEquivSigmaOrbits Γ Y).symm.tsum_eq (fun y => ∫ h in 𝓕, Φ y h ∂ν)]
  simp only [Function.comp_def] at hs'
  rw [Summable.tsum_sigma hs']
  simp only [Function.comp_apply, selfEquivSigmaOrbits_symm_mk, horbit, tsum_zero]
end _root_.GlobalTheory.OrbitUnfold
end GlobalTheory.OrbitUnfold
