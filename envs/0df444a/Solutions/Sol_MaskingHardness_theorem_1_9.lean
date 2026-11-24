-- Prove2me | solution 1 for MaskingHardness.theorem_1_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:12:05.679667+00:00
-- url     : https://prove2.me/submissions/60bdfeea-35db-489d-8c7f-b7dbd39d10e1

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_IsMaskingChannel
import Definitions.Def_MaskingHardness_lossObjective
import Definitions.Def_MaskingHardness_channelFidelity
import Theorems.Thm_MaskingHardness_theorem_1_9_z_form
import Theorems.Thm_MaskingHardness_theorem_1_9_radius

open MaskingHardness

theorem solution {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (hdom : ∀ y z, z ∉ stdSimplex ℝ (Fin k) → h y z = ⊥)
    (hgh : ∀ y, IsConvConcConj (fun a => ((g y a : ℝ) : EReal)) (h y))
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest
        {v : EReal | ∃ W : X → Matrix (Fin k) (Fin k) ℝ,
          IsMaskingChannel D c ε W ∧ v = channelFidelity D h W}
        (⨅ lam : ι → ℝ, ((lossObjective D c g ε lam : ℝ) : EReal)) ∧
      (0 < ε → (∃ v : ℝ, ∀ y a, v ≤ g y (centered a)) →
        ∃ lam₀ : ι → ℝ, IsLeast (Set.range (lossObjective D c g ε))
          (lossObjective D c g ε lam₀)) := by
  constructor
  · -- the channel form is the z-form, read column by column
    have hz := theorem_1_9_z_form D hD c g h hdom hgh ε hε
    have hset : {v : EReal | ∃ W : X → Matrix (Fin k) (Fin k) ℝ,
          IsMaskingChannel D c ε W ∧ v = channelFidelity D h W} =
        {v : EReal | ∃ z : X → Fin k → Fin k → ℝ,
          (∀ x y, z x y ∈ stdSimplex ℝ (Fin k)) ∧
          (∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ (z x y - fun _ => (k : ℝ)⁻¹))| ≤ ε) ∧
          v = ∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (z x y)} := by
      ext v
      constructor
      · rintro ⟨W, ⟨hW1, hW2⟩, rfl⟩
        refine ⟨fun x y i => W x i y, fun x y => hW1 x y, fun i => ?_, rfl⟩
        exact hW2 i
      · rintro ⟨z, hz1, hz2, rfl⟩
        refine ⟨fun x i y => z x y i, ⟨fun x y => hz1 x y, fun i => ?_⟩, rfl⟩
        exact hz2 i
    rw [hset]; exact hz
  · rintro hεpos ⟨v, hv⟩
    set F := lossObjective D c g ε with hF
    -- lower semicontinuity of each `g y`, from the supremum formula
    have hglsc : ∀ y, LowerSemicontinuous (g y) := by
      intro y
      have hE : LowerSemicontinuous (fun a => ((g y a : ℝ) : EReal)) := by
        have : (fun a => ((g y a : ℝ) : EReal)) =
            fun a => ⨆ b, h y b - ((a ⬝ᵥ b : ℝ) : EReal) := funext (hgh y).1
        rw [this]
        apply lowerSemicontinuous_iSup
        intro b
        apply Continuous.lowerSemicontinuous
        induction h y b using EReal.rec with
        | bot => simpa using continuous_const
        | top =>
          have : (fun a : Fin k → ℝ => (⊤ : EReal) - ((a ⬝ᵥ b : ℝ) : EReal)) = fun _ => ⊤ := by
            funext a; exact EReal.top_sub_coe _
          rw [this]; exact continuous_const
        | coe t =>
          have : (fun a : Fin k → ℝ => (t : EReal) - ((a ⬝ᵥ b : ℝ) : EReal)) =
              fun a => (((t - a ⬝ᵥ b : ℝ)) : EReal) := by
            funext a; rw [EReal.coe_sub]
          rw [this]
          exact continuous_coe_real_ereal.comp (by fun_prop)
      intro a r hr
      have := hE a (r : EReal) (show (r : EReal) < (g y a : EReal) by exact_mod_cast hr)
      filter_upwards [this] with a' ha'
      exact_mod_cast ha'
    have hFlsc : LowerSemicontinuous F := by
      have hterm : ∀ x y, LowerSemicontinuous
          (fun lam : ι → ℝ => D x y * g y (centered (combo c lam x))) := by
        intro x y
        have hcont : Continuous (fun lam : ι → ℝ => centered (combo c lam x)) := by
          unfold centered combo; fun_prop
        have h1 : LowerSemicontinuous (fun lam : ι → ℝ => g y (centered (combo c lam x))) :=
          (hglsc y).comp hcont
        intro lam
        exact ContinuousAt.comp_lowerSemicontinuousAt (g := fun t => D x y * t)
          (by fun_prop) (h1 lam) (fun s t hst => mul_le_mul_of_nonneg_left hst (hD.1 x y))
      have hsum : LowerSemicontinuous
          (fun lam : ι → ℝ => ∑ x, ∑ y, D x y * g y (centered (combo c lam x))) := by
        apply lowerSemicontinuous_sum; intro x _
        apply lowerSemicontinuous_sum; intro y _
        exact hterm x y
      have hpen : Continuous (fun lam : ι → ℝ => ε * ∑ i, |lam i|) := by fun_prop
      exact hsum.add hpen.lowerSemicontinuous
    -- the ℓ₁ ball of radius r
    set r : ℝ := (∑ x, ∑ y, D x y * g y 0 - v) / ε with hr
    have hr0 : 0 ≤ r := by
      have : v ≤ ∑ x, ∑ y, D x y * g y 0 := by
        have h1 : ∑ x, ∑ y, D x y * v ≤ ∑ x, ∑ y, D x y * g y 0 := by
          apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
          have := hv y 0
          have hc0 : centered (0 : Fin k → ℝ) = 0 := by funext i; simp [centered]
          rw [hc0] at this
          exact mul_le_mul_of_nonneg_left this (hD.1 x y)
        have h2 : ∑ x, ∑ y, D x y * v = v := by
          simp_rw [← Finset.sum_mul, hD.2, one_mul]
        linarith
      exact div_nonneg (by linarith) hεpos.le
    set B : Set (ι → ℝ) := {lam | ∑ i, |lam i| ≤ r} with hB
    have hBc : IsCompact B := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_le (by fun_prop) continuous_const
      · apply (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := r)).subset
        intro lam hlam
        rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr0]
        intro i
        rw [Real.norm_eq_abs]
        exact le_trans (Finset.single_le_sum (f := fun i => |lam i|)
          (fun j _ => abs_nonneg (lam j)) (Finset.mem_univ i)) hlam
    have hB0 : (0 : ι → ℝ) ∈ B := by simp [hB, hr0]
    obtain ⟨lam₀, hlam₀B, hmin⟩ := (hFlsc.lowerSemicontinuousOn B).exists_isMinOn ⟨0, hB0⟩ hBc
    refine ⟨lam₀, ⟨lam₀, rfl⟩, ?_⟩
    rintro _ ⟨lam, rfl⟩
    by_cases hl : lam ∈ B
    · exact hmin hl
    · have hl' : r < ∑ i, |lam i| := lt_of_not_ge hl
      have := theorem_1_9_radius D hD c g ε hεpos v hv lam hl'
      exact le_trans (hmin hB0) this.le
