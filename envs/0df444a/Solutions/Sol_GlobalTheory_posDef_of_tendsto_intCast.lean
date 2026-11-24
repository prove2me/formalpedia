-- Prove2me | solution 1 for GlobalTheory.posDef_of_tendsto_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:10.689855+00:00
-- url     : https://prove2.me/submissions/d7710aa2-05be-4452-b034-f73968c98f4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Module TensorProduct
namespace GlobalTheory
section SecondDifference
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]
namespace HasConstSecondDiff
variable {f : X → A}
end HasConstSecondDiff
end SecondDifference
section Definite
private theorem continuous_quadraticForm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) : Continuous Q := by
  have h : Continuous fun v => (QuadraticMap.associated Q).toContinuousBilinearMap v v := by
    fun_prop
  exact h.congr fun v => QuadraticMap.associated_eq_self_apply ℝ Q v
end Definite
section RealExtension
variable {X : Type*} [AddCommGroup X]
example : HasConstSecondDiff (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) ∧
    (∀ x : ℤ, (((-x : ℤ) : ℝ) ^ 2 + 1) = (x : ℝ) ^ 2 + 1) ∧
    Tendsto (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) cofinite atTop := by
  refine ⟨fun a a' μ ν => ?_, fun x => by simp, tendsto_atTop_add_const_right _ _ ?_⟩
  · simp only [secondDiff]
    push_cast
    ring
  · have h : Tendsto (fun x : ℤ => |(x : ℝ)|) cofinite atTop := by
      rw [Int.cofinite_eq, tendsto_sup]
      exact ⟨tendsto_abs_atBot_atTop.comp (tendsto_intCast_atBot_iff.2 tendsto_id),
        tendsto_abs_atTop_atTop.comp tendsto_intCast_atTop_atTop⟩
    simpa [Function.comp_def] using (tendsto_pow_atTop two_ne_zero).comp h
end RealExtension
end GlobalTheory
end

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Finite ι] (Q : QuadraticForm ℝ (ι → ℝ))
    (h : Tendsto (fun n : ι → ℤ => Q fun i => (n i : ℝ)) cofinite atTop) : Q.PosDef := by
  have := Fintype.ofFinite ι
  have hc : Continuous Q := continuous_quadraticForm Q

  have key : ∀ v : ι → ℝ, v ≠ 0 → ¬ (Q v < 0 ∨ (Q v = 0 ∧ ∀ r, QuadraticMap.polar Q v r = 0)) := by
    intro v hv hQ
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).bddAbove_image hc.continuousOn
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).bddAbove_image
      (f := fun r => -QuadraticMap.polar Q v r)
      (Q.polarBilin v).continuous_of_finiteDimensional.neg.continuousOn

    let n : ℕ → ι → ℤ := fun t i => ⌊(t : ℝ) * v i⌋
    have hn : Tendsto n atTop cofinite := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
      have hi' : v i ≠ 0 := hi
      have h₁ : Tendsto (fun t => n t i) atTop cofinite := by
        rw [Int.cofinite_eq]
        rcases hi'.lt_or_gt with h₀ | h₀
        · exact (tendsto_floor_atBot.comp
            (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg h₀)).mono_right le_sup_left
        · exact (tendsto_floor_atTop.comp
            (tendsto_natCast_atTop_atTop.atTop_mul_const h₀)).mono_right le_sup_right
      intro s hs
      have := h₁ (Set.Finite.compl_mem_cofinite ((Set.Finite.image (fun m => m i) hs)))
      rw [mem_map] at this ⊢
      filter_upwards [this] with t ht
      by_contra hts
      exact ht ⟨n t, hts, rfl⟩
    have hval : ∀ t : ℕ, ∃ r ∈ Set.Icc (0 : ι → ℝ) 1, (Q fun i => (n t i : ℝ)) =
        (t : ℝ) * (t * Q v + -QuadraticMap.polar Q v r) + Q r := by
      intro t
      refine ⟨fun i => Int.fract ((t : ℝ) * v i),
        ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩, ?_⟩
      have e : (fun i => (n t i : ℝ)) = (t : ℝ) • v + -fun i => Int.fract ((t : ℝ) * v i) := by
        ext i
        simp [n, ← sub_eq_add_neg]
      rw [e, QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_neg,
        QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_left]
      simp only [smul_eq_mul]
      ring
    have hev : ∀ᶠ t : ℕ in atTop, (Q fun i => (n t i : ℝ)) ≤ C := by
      rcases hQ with h₀ | ⟨h₀, h₁⟩
      · filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg h₀).eventually_le_atBot
          (-D)] with t ht
        obtain ⟨r, hr, e⟩ := hval t
        have h₂ : Q r ≤ C := hC ⟨r, hr, rfl⟩
        have h₃ : -QuadraticMap.polar Q v r ≤ D := hD ⟨r, hr, rfl⟩
        have h₄ : (t : ℝ) * (t * Q v + -QuadraticMap.polar Q v r) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg t) (by linarith)
        linarith
      · refine Eventually.of_forall fun t => ?_
        obtain ⟨r, hr, e⟩ := hval t
        have h₂ : Q r ≤ C := hC ⟨r, hr, rfl⟩
        rw [e, h₀, h₁]
        simpa using h₂
    obtain ⟨t, h₁, h₂⟩ := (hev.and ((h.comp hn).eventually_gt_atTop C)).exists
    exact absurd h₁ (not_le.2 h₂)
  have hnn : ∀ v, 0 ≤ Q v := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · exact not_lt.1 fun h₀ => key v hv (Or.inl h₀)
  intro v hv
  refine (hnn v).lt_of_ne' fun h₀ => key v hv (Or.inr ⟨h₀, fun r => ?_⟩)
  by_contra hr
  have := hnn ((-(Q r + 1) / QuadraticMap.polar Q v r) • v + r)
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.polar_smul_left, h₀,
    smul_zero, smul_eq_mul, div_mul_cancel₀ _ hr] at this
  linarith
end GlobalTheory
