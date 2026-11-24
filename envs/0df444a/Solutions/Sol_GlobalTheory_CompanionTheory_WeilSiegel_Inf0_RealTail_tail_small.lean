-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:43.801538+00:00
-- url     : https://prove2.me/submissions/8afa7a64-e50a-4777-a56a-afb8fdb25c46

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_setLIntegral_le_of_dyadic
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_volume_near_le
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_volume_far_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
theorem _root_.solution : ∀ (P ι : Type) [Fintype P] [Fintype ι] (a : ℕ), 0 < a →
    ∀ (Q : (P → ι → ℝ) → (P → ℝ)), Measurable Q → ∀ C : ℝ≥0,
    (∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U) →
    ∀ f : (P → ι → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
    (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') →
    ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (P → ℝ), MeasurableSet U →
      ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
  intro P ι _ _ a ha Q hQ C hbox f _hfm hf0 hdec ε hε
  obtain ⟨M, hM⟩ : ∃ M, M = a * Fintype.card P := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ := hdec (M + 1)
  obtain ⟨C2, hC2⟩ := hdec (M + 1 + 1)
  have hsn : ∀ x : P → ι → ℝ, 0 ≤ ∑ w, ‖x w‖ := fun x =>
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hC1n : 0 ≤ C1 :=
    (mul_nonneg (hf0 0) (pow_nonneg (by have := hsn 0; linarith) _)).trans (hC1 0)
  have hC2n : 0 ≤ C2 :=
    (mul_nonneg (hf0 0) (pow_nonneg (by have := hsn 0; linarith) _)).trans (hC2 0)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (C : ℝ) := ⟨_, rfl⟩
  have hcn : 0 ≤ c := hc ▸ C.2
  have hCc : (C : ℝ≥0∞) = ENNReal.ofReal c := by rw [hc, ENNReal.ofReal_coe_nnreal]
  obtain ⟨A1, hA1⟩ : ∃ A : ℝ, A = 2 * C1 * 2 ^ (M + 1) * c := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : ℝ, A = 2 * C2 * 2 ^ (M + 1) * c := ⟨_, rfl⟩
  have hA1n : 0 ≤ A1 := hA1 ▸ by positivity
  have hA2n : 0 ≤ A2 := hA2 ▸ by positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Fintype.card P : ℝ) := ⟨_, rfl⟩
  have hrn : 0 ≤ r := hr ▸ by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε / (2 * (r * A1 + 1))) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * A2 / ε + 1 := ⟨_, rfl⟩
  have hD : 0 < r * A1 + 1 := by positivity
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * (r * A1 + 1)) := by rw [hδdef]; exact min_le_right _ _
  have hR : 0 < R := by rw [hRdef]; positivity
  refine ⟨δ, R, hδ, hR, fun U hU => ?_⟩
  have hnear : ∀ v, ∫⁻ x in Q ⁻¹' U ∩ {x | ‖x v‖ < δ}, ENNReal.ofReal (f x) ≤
      ENNReal.ofReal (A1 * δ ^ a) * volume U := by
    intro v
    have hT : MeasurableSet (Q ⁻¹' U ∩ {x : P → ι → ℝ | ‖x v‖ < δ}) :=
      (hQ hU).inter (measurableSet_lt (continuous_apply v).norm.measurable measurable_const)
    have := setLIntegral_le_of_dyadic f hf0 M C1 hC1n _ hT (fun x _ => hC1 x)
      ((C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a) * volume U)
      (fun j => by rw [hM]; exact volume_near_le hbox hδ hδ1 v hU j)
    refine this.trans (le_of_eq ?_)
    rw [hA1, hCc, mul_assoc (2 * C1 * 2 ^ (M + 1)) c,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * C1 * 2 ^ (M + 1)),
      ENNReal.ofReal_mul hcn]
    ring
  have hfar : ∫⁻ x in Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}, ENNReal.ofReal (f x) ≤
      ENNReal.ofReal (A2 / (1 + R)) * volume U := by
    have hY : {x : P → ι → ℝ | ∃ w, R < ‖x w‖} = ⋃ w, {x | R < ‖x w‖} := by
      ext x; simp
    have hT : MeasurableSet (Q ⁻¹' U ∩ {x : P → ι → ℝ | ∃ w, R < ‖x w‖}) := by
      refine (hQ hU).inter ?_
      rw [hY]
      exact MeasurableSet.iUnion fun w =>
        measurableSet_lt measurable_const (continuous_apply w).norm.measurable
    have hK : ∀ x ∈ Q ⁻¹' U ∩ {x : P → ι → ℝ | ∃ w, R < ‖x w‖},
        f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) ≤ C2 / (1 + R) := by
      rintro x ⟨-, w, hw⟩
      have hle : ‖x w‖ ≤ ∑ w, ‖x w‖ :=
        Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
      have h1 : 1 + R ≤ 1 + ∑ w, ‖x w‖ := by linarith
      have hnn : 0 ≤ f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) :=
        mul_nonneg (hf0 x) (pow_nonneg (by have := hsn x; linarith) _)
      rw [le_div_iff₀ (by positivity)]
      calc f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) * (1 + R)
          ≤ f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) * (1 + ∑ w, ‖x w‖) :=
            mul_le_mul_of_nonneg_left h1 hnn
        _ = f x * (1 + ∑ w, ‖x w‖) ^ (M + 1 + 1) := by ring
        _ ≤ C2 := hC2 x
    have := setLIntegral_le_of_dyadic f hf0 M (C2 / (1 + R)) (by positivity) _ hT hK
      ((C : ℝ≥0∞) * volume U) (fun j => by rw [hM]; exact volume_far_le hbox _ hU j)
    refine this.trans (le_of_eq ?_)
    have e : A2 / (1 + R) = (2 * (C2 / (1 + R)) * 2 ^ (M + 1)) * c := by rw [hA2]; ring
    rw [e, hCc, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (C2 / (1 + R)) * 2 ^ (M + 1))]
    ring
  have hsub : Q ⁻¹' U ∩ (coreR δ R : Set (P → ι → ℝ))ᶜ ⊆
      (⋃ v, Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∪ (Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}) := by
    rintro x ⟨hxU, hxc⟩
    simp only [coreR, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hxc
    obtain ⟨w, hw⟩ := hxc
    by_cases h : δ ≤ ‖x w‖
    · exact Or.inr ⟨hxU, w, not_le.mp fun h' => hw ⟨h, h'⟩⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨w, hxU, not_le.mp h⟩)
  have hreal : r * (A1 * δ ^ a) + A2 / (1 + R) ≤ ε := by
    have h1 : δ ^ a ≤ δ := pow_le_of_le_one hδ.le hδ1 ha.ne'
    have h2 : r * A1 * δ ≤ ε / 2 := by
      calc r * A1 * δ ≤ (r * A1 + 1) * (ε / (2 * (r * A1 + 1))) := by
            apply mul_le_mul (by linarith) hδ2 hδ.le hD.le
        _ = ε / 2 := by field_simp
    have h3 : A2 / (1 + R) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity), hRdef]
      have : ε / 2 * (1 + (2 * A2 / ε + 1)) = ε + A2 := by field_simp; ring
      rw [this]; linarith
    have h4 : r * (A1 * δ ^ a) ≤ r * A1 * δ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  calc ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x)
      ≤ ∫⁻ x in (⋃ v, Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∪ (Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}),
          ENNReal.ofReal (f x) := lintegral_mono_set hsub
    _ ≤ (∫⁻ x in ⋃ v, Q ⁻¹' U ∩ {x | ‖x v‖ < δ}, ENNReal.ofReal (f x)) +
        (∫⁻ x in Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}, ENNReal.ofReal (f x)) :=
          lintegral_union_le _ _ _
    _ ≤ (∑ v : P, ENNReal.ofReal (A1 * δ ^ a) * volume U) +
        ENNReal.ofReal (A2 / (1 + R)) * volume U := by
          refine add_le_add ?_ hfar
          refine (lintegral_iUnion_le _ _).trans ?_
          rw [tsum_fintype]
          exact Finset.sum_le_sum fun v _ => hnear v
    _ = ENNReal.ofReal (r * (A1 * δ ^ a) + A2 / (1 + R)) * volume U := by
          have hpos : 0 ≤ A1 * δ ^ a := by positivity
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hrn,
            hr, ENNReal.ofReal_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            add_mul, mul_assoc]
    _ ≤ ENNReal.ofReal ε * volume U := by
          gcongr
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
