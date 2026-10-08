-- Prove2me | solution 1 for HighDimStat.Minimax.estimation_to_testing_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:22:35.173807+00:00
-- url     : https://prove2.me/submissions/c3dedbee-6582-4ec1-98fa-fd3517238118

import Mathlib
import Definitions.Def_HighDimStat_Minimax_MinimaxRisk
import Definitions.Def_HighDimStat_Minimax_IsSeparated
import Definitions.Def_HighDimStat_Minimax_IsJointTestingMeasure

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory

namespace CexC7fcc83f

/-- Bool with the trivial sigma-algebra. -/
def X : Type := Bool

instance instMS : MeasurableSpace X := ⊥

instance instDec : DecidableEq X := inferInstanceAs (DecidableEq Bool)

theorem const_of_meas {β : Type} [MeasurableSpace β] [MeasurableSingletonClass β]
    (f : X → β) (hf : Measurable f) (a b : X) : f b = f a := by
  have h : MeasurableSet[(⊥ : MeasurableSpace X)] (f ⁻¹' {f a}) :=
    hf (measurableSet_singleton (f a))
  rcases MeasurableSpace.measurableSet_bot_iff.mp h with h | h
  · have ha : a ∈ f ⁻¹' {f a} := rfl
    rw [h] at ha
    exact ha.elim
  · have hb : b ∈ f ⁻¹' {f a} := by rw [h]; trivial
    exact hb

theorem lintegral_eq_zero_of (μ : Measure X) (f : X → ENNReal) (p : X) (hp : f p = 0) :
    ∫⁻ x, f x ∂μ = 0 := by
  rw [lintegral_def]
  refine le_antisymm (iSup₂_le fun g hg => ?_) bot_le
  have hgp : g p = 0 := by
    have h1 : g p ≤ f p := hg p
    rw [hp] at h1
    exact le_antisymm h1 bot_le
  have hg0 : g = 0 := by
    ext x
    rw [const_of_meas (⇑g) g.measurable p x, hgp]
    rfl
  rw [hg0]
  simp

def ρ : X → X → ℝ := fun x y => if x = y then 0 else 1

def θs : Fin 2 → X := (![false, true] : Fin 2 → Bool)

theorem h01 : θs 0 ≠ θs 1 := fun h => Bool.false_ne_true h

theorem ρ_nonneg : ∀ x y, 0 ≤ ρ x y := by
  intro x y; unfold ρ; split_ifs <;> norm_num

theorem ρ_refl : ∀ x, ρ x x = 0 := by
  intro x; unfold ρ; rw [if_pos rfl]

theorem ρ_symm : ∀ x y, ρ x y = ρ y x := by
  intro x y; unfold ρ
  by_cases hxy : x = y
  · subst hxy; rfl
  · rw [if_neg hxy, if_neg (Ne.symm hxy)]

theorem ρ_tri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z := by
  intro x y z; unfold ρ
  by_cases h1 : x = z
  · rw [if_pos h1]; split_ifs <;> norm_num
  · rw [if_neg h1]
    by_cases h2 : x = y
    · rw [if_pos h2, if_neg (fun h3 => h1 (h2.trans h3))]; norm_num
    · rw [if_neg h2]; split_ifs <;> norm_num

theorem hsep : HighDimStat.Minimax.IsSeparated ρ θs (1 / 2) := by
  intro j k hjk
  fin_cases j <;> fin_cases k
  · exact absurd rfl hjk
  · show 2 * (1 / 2 : ℝ) ≤ ρ (θs 0) (θs 1)
    unfold ρ; rw [if_neg h01]; norm_num
  · show 2 * (1 / 2 : ℝ) ≤ ρ (θs 1) (θs 0)
    unfold ρ; rw [if_neg (Ne.symm h01)]; norm_num
  · exact absurd rfl hjk

def a0 : Fin 2 × X := ((0 : Fin 2), (false : Bool))
def b1 : Fin 2 × X := ((1 : Fin 2), (true : Bool))

noncomputable def Q : Measure (Fin 2 × X) :=
  (1 / 2 : ENNReal) • (Measure.dirac a0 + Measure.dirac b1)

instance instQ : IsProbabilityMeasure Q := by
  constructor
  simp only [Q, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.div_mul_cancel] <;> norm_num

theorem hQ : HighDimStat.Minimax.IsJointTestingMeasure
    (fun p : X => Measure.dirac p) θs Q := by
  intro j s hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with h | h
  · subst h
    simp
  · subst h
    have hm : MeasurableSet ({j} ×ˢ (Set.univ : Set X)) :=
      (measurableSet_singleton j).prod MeasurableSet.univ
    rw [Q, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hm,
      Measure.dirac_apply' _ hm, measure_univ, smul_eq_mul]
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · rw [Set.indicator_of_mem
          (show a0 ∈ ({(0 : Fin 2)} ×ˢ (Set.univ : Set X)) from
            ⟨Set.mem_singleton _, Set.mem_univ _⟩),
        Set.indicator_of_notMem
          (show b1 ∉ ({(0 : Fin 2)} ×ˢ (Set.univ : Set X)) from
            fun h => absurd (h.1 : b1.1 = 0) (by decide))]
      simp
    · rw [Set.indicator_of_notMem
          (show a0 ∉ ({(1 : Fin 2)} ×ˢ (Set.univ : Set X)) from
            fun h => absurd (h.1 : a0.1 = 1) (by decide)),
        Set.indicator_of_mem
          (show b1 ∈ ({(1 : Fin 2)} ×ˢ (Set.univ : Set X)) from
            ⟨Set.mem_singleton _, Set.mem_univ _⟩)]
      simp

theorem test_lb (ψ : {f : X → Fin 2 // Measurable f}) :
    (1 / 2 : ENNReal) ≤ Q {p : Fin 2 × X | ψ.1 p.2 ≠ p.1} := by
  have hc : ψ.1 (true : Bool) = ψ.1 (false : Bool) :=
    const_of_meas ψ.1 ψ.2 (false : Bool) (true : Bool)
  simp only [Q, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  by_cases h0 : ψ.1 (false : Bool) = 0
  · have hb : b1 ∈ {p : Fin 2 × X | ψ.1 p.2 ≠ p.1} := by
      show ψ.1 (true : Bool) ≠ 1
      rw [hc, h0]; decide
    rw [Measure.dirac_apply_of_mem hb]
    calc (1 / 2 : ENNReal) = 1 / 2 * 1 := by simp
      _ ≤ 1 / 2 * (Measure.dirac a0 {p : Fin 2 × X | ψ.1 p.2 ≠ p.1} + 1) := by
        gcongr; exact le_add_self
  · have ha : a0 ∈ {p : Fin 2 × X | ψ.1 p.2 ≠ p.1} := by
      show ψ.1 (false : Bool) ≠ 0
      exact h0
    rw [Measure.dirac_apply_of_mem ha]
    calc (1 / 2 : ENNReal) = 1 / 2 * 1 := by simp
      _ ≤ 1 / 2 * (1 + Measure.dirac b1 {p : Fin 2 × X | ψ.1 p.2 ≠ p.1}) := by
        gcongr; exact le_self_add

theorem risk_zero :
    HighDimStat.Minimax.minimaxRisk (fun p : X => Measure.dirac p) (id : X → X) ρ id = 0 := by
  unfold HighDimStat.Minimax.minimaxRisk
  refine le_antisymm ?_ bot_le
  refine (iInf_le _ (⟨id, measurable_id⟩ : {f : X → X // Measurable f})).trans ?_
  refine iSup_le fun p => ?_
  rw [lintegral_eq_zero_of _ _ p (by simp [ρ])]

theorem cex : ¬ (∀ {𝒳 Ω Idx : Type} [MeasurableSpace 𝒳] [MeasurableSpace Ω]
    (measure : Idx → Measure 𝒳) [∀ p, IsProbabilityMeasure (measure p)]
    (θ : Idx → Ω) (ρ : Ω → Ω → ℝ)
    (hρ_nonneg : ∀ x y, 0 ≤ ρ x y) (hρ_refl : ∀ x, ρ x x = 0)
    (hρ_symm : ∀ x y, ρ x y = ρ y x) (hρ_tri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (Φ : ℝ → ℝ) (hΦ : ∀ x y, 0 ≤ x → x ≤ y → Φ x ≤ Φ y) (hΦ0 : ∀ x, 0 ≤ x → 0 ≤ Φ x)
    {M : ℕ} (θs : Fin M → Ω) (δ : ℝ) (hδ : 0 < δ)
    (hsep : HighDimStat.Minimax.IsSeparated ρ θs δ)
    (Prep : Fin M → Idx) (hPrep : ∀ j, θ (Prep j) = θs j)
    (Q : Measure (Fin M × 𝒳)) [IsProbabilityMeasure Q]
    (hQ : HighDimStat.Minimax.IsJointTestingMeasure measure Prep Q),
    ENNReal.ofReal (Φ δ) *
      (⨅ ψ : {f : 𝒳 → Fin M // Measurable f}, Q {p : Fin M × 𝒳 | ψ.1 p.2 ≠ p.1}) ≤
      HighDimStat.Minimax.minimaxRisk measure θ ρ Φ) := by
  intro h
  have key := @h X X X instMS instMS (fun p : X => Measure.dirac p) inferInstance
    (id : X → X) ρ ρ_nonneg ρ_refl ρ_symm ρ_tri
    id (fun x y _ hxy => hxy) (fun x hx => hx)
    2 θs (1 / 2) (by norm_num) hsep
    θs (fun j => rfl) Q instQ hQ
  rw [risk_zero] at key
  have hinf : (1 / 2 : ENNReal) ≤
      ⨅ ψ : {f : X → Fin 2 // Measurable f}, Q {p : Fin 2 × X | ψ.1 p.2 ≠ p.1} :=
    le_iInf test_lb
  have hpos : (0 : ENNReal) < ENNReal.ofReal (id (1 / 2 : ℝ)) *
      ⨅ ψ : {f : X → Fin 2 // Measurable f}, Q {p : Fin 2 × X | ψ.1 p.2 ≠ p.1} := by
    refine ENNReal.mul_pos ?_ ?_
    · simp
    · exact (lt_of_lt_of_le (by norm_num) hinf).ne'
  exact absurd key (not_le.mpr hpos)

end CexC7fcc83f

open MeasureTheory HighDimStat.Minimax in
theorem solution : ¬ (∀ {𝒳 Ω Idx : Type} [MeasurableSpace 𝒳] [MeasurableSpace Ω]
    (measure : Idx → Measure 𝒳) [∀ p, IsProbabilityMeasure (measure p)]
    (θ : Idx → Ω) (ρ : Ω → Ω → ℝ)
    (hρ_nonneg : ∀ x y, 0 ≤ ρ x y) (hρ_refl : ∀ x, ρ x x = 0)
    (hρ_symm : ∀ x y, ρ x y = ρ y x) (hρ_tri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (Φ : ℝ → ℝ) (hΦ : ∀ x y, 0 ≤ x → x ≤ y → Φ x ≤ Φ y) (hΦ0 : ∀ x, 0 ≤ x → 0 ≤ Φ x)
    {M : ℕ} (θs : Fin M → Ω) (δ : ℝ) (hδ : 0 < δ) (hsep : IsSeparated ρ θs δ)
    (Prep : Fin M → Idx) (hPrep : ∀ j, θ (Prep j) = θs j)
    (Q : Measure (Fin M × 𝒳)) [IsProbabilityMeasure Q]
    (hQ : IsJointTestingMeasure measure Prep Q),
    ENNReal.ofReal (Φ δ) *
      (⨅ ψ : {f : 𝒳 → Fin M // Measurable f}, Q {p : Fin M × 𝒳 | ψ.1 p.2 ≠ p.1}) ≤
      minimaxRisk measure θ ρ Φ) := by
  exact CexC7fcc83f.cex
