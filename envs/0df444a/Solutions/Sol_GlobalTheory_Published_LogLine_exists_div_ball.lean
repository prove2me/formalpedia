-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.exists_div_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:20.314512+00:00
-- url     : https://prove2.me/submissions/0207ae17-c177-4731-b6c2-50d460ca4008

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv_apply
import Theorems.Thm_GlobalTheory_differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution {a : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} {i : Fin n} (hc : c i = 0)
    (ha : DifferentiableOn ℂ a (ball c r)) (h0 : ∀ z ∈ ball c r, z i = 0 → a z = 0) :
    ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b (ball c r) ∧ ∀ z ∈ ball c r, a z = z i * b z := by
  set p : ℝ → (Fin n → ℂ) → (Fin n → ℂ) :=
    fun t z => z + (((t : ℂ) - 1) * z i) • (Pi.single i 1 : Fin n → ℂ) with hp
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, ∀ z ∈ ball c r, p t z ∈ ball c r := by
    intro t ht z hz
    have hr := pos_of_mem_ball hz
    rw [uIcc_of_le zero_le_one] at ht
    rw [ball_pi c hr] at hz ⊢
    intro j _
    have hj := hz j (mem_univ j)
    by_cases hji : j = i
    · subst hji
      rw [mem_ball_iff_norm, hc, sub_zero] at hj ⊢
      have : p t z j = t * z j := by simp [hp]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) hj
    · have : p t z j = z j := by simp [hp, hji]
      rwa [this]
  have hd := GlobalTheory.SCV.differentiableOn_fderiv_apply isOpen_ball ha (Pi.single i 1)
  have key := GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun t z => fderiv ℂ a (p t z) (Pi.single i 1)) (U := ball c r) isOpen_ball
    (a := 0) (b := 1) ?_ ?_
  · refine ⟨_, key.1, fun z hz => ?_⟩
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => a (p s z))
        (z i * fderiv ℂ a (p t z) (Pi.single i 1)) t := by
      intro t ht
      have h1 : HasFDerivAt a (fderiv ℂ a (p t z)) (p t z) :=
        (ha.differentiableAt (isOpen_ball.mem_nhds (hmem t ht z hz))).hasFDerivAt
      have h2 : HasDerivAt (fun w : ℂ => z + ((w - 1) * z i) • (Pi.single i 1 : Fin n → ℂ))
          ((z i) • (Pi.single i 1 : Fin n → ℂ)) (t : ℂ) := by
        simpa using ((((hasDerivAt_id (t : ℂ)).sub_const 1).mul_const (z i)).smul_const
          (Pi.single i 1 : Fin n → ℂ)).const_add z
      have h3 := (h1.comp_hasDerivAt (t : ℂ) h2).comp_ofReal
      simpa [hp, Function.comp_def] using h3
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (((key.2 z hz).1).const_mul (z i))
    rw [intervalIntegral.integral_const_mul] at hint
    rw [hint, h0 (p 0 z) (hmem 0 left_mem_uIcc z hz) (by simp [hp])]
    simp [hp]
  · refine hd.continuousOn.comp (f := fun q : ℝ × (Fin n → ℂ) => p q.1 q.2) ?_
      fun q hq => hmem _ hq.1 _ hq.2
    simp only [hp]
    fun_prop
  · intro t ht
    refine hd.comp (f := p t) ?_ fun z hz => hmem t ht z hz
    simp only [hp]
    fun_prop
end GlobalTheory.Published.LogLine
