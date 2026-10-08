-- Prove2me | solution 1 for NetworkControl.CapacityRegion.lemma_stability_conditions_under_admissibility_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:36:14.087018+00:00
-- url     : https://prove2.me/submissions/52fe660f-48aa-48d7-92ae-36fed6039213

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleArrival
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleService
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable

set_option autoImplicit false

open MeasureTheory

namespace P2M7d80

open NetworkControl.CapacityRegion

section Det

variable {Ω : Type*} (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)

lemma qb_succ (t : ℕ) (ω : Ω) :
    QueueBacklog A svc U0 (t + 1) ω = max (QueueBacklog A svc U0 t ω - svc t ω) 0 + A t ω := rfl

lemma qb_zero (ω : Ω) : QueueBacklog A svc U0 0 ω = U0 ω := rfl

lemma qb_nonneg (hU0nn : ∀ ω, 0 ≤ U0 ω) (hAnn : ∀ t ω, 0 ≤ A t ω) :
    ∀ t ω, 0 ≤ QueueBacklog A svc U0 t ω
  | 0, ω => hU0nn ω
  | t + 1, ω => by
    rw [qb_succ]
    have := hAnn t ω
    have := le_max_right (QueueBacklog A svc U0 t ω - svc t ω) 0
    linarith

lemma qb_lower (hU0nn : ∀ ω, 0 ≤ U0 ω) :
    ∀ t ω, ∑ τ ∈ Finset.range t, (A τ ω - svc τ ω) ≤ QueueBacklog A svc U0 t ω
  | 0, ω => by simp [qb_zero, hU0nn ω]
  | t + 1, ω => by
    rw [Finset.sum_range_succ, qb_succ]
    have := qb_lower hU0nn t ω
    have := le_max_left (QueueBacklog A svc U0 t ω - svc t ω) 0
    linarith

lemma qb_upper (hU0nn : ∀ ω, 0 ≤ U0 ω) (hAnn : ∀ t ω, 0 ≤ A t ω) (hsvcnn : ∀ t ω, 0 ≤ svc t ω) :
    ∀ t ω, QueueBacklog A svc U0 t ω ≤ U0 ω + ∑ τ ∈ Finset.range t, A τ ω
  | 0, ω => by simp [qb_zero]
  | t + 1, ω => by
    rw [Finset.sum_range_succ, qb_succ]
    have h1 := qb_upper hU0nn hAnn hsvcnn t ω
    have h2 := qb_nonneg A svc U0 hU0nn hAnn t ω
    have h3 := hsvcnn t ω
    have : max (QueueBacklog A svc U0 t ω - svc t ω) 0 ≤ QueueBacklog A svc U0 t ω :=
      max_le (by linarith) h2
    linarith

lemma qb_le_add (hU0nn : ∀ ω, 0 ≤ U0 ω) :
    ∀ t ω, QueueBacklog A svc U0 t ω ≤ U0 ω + QueueBacklog A svc (fun _ => 0) t ω
  | 0, ω => by simp [qb_zero]
  | t + 1, ω => by
    rw [qb_succ, qb_succ]
    have h1 := qb_le_add hU0nn t ω
    have h2 := hU0nn ω
    have h3 := le_max_left (QueueBacklog A svc (fun _ => 0) t ω - svc t ω) 0
    have h4 := le_max_right (QueueBacklog A svc (fun _ => 0) t ω - svc t ω) 0
    have : max (QueueBacklog A svc U0 t ω - svc t ω) 0 ≤
        U0 ω + max (QueueBacklog A svc (fun _ => 0) t ω - svc t ω) 0 :=
      max_le (by linarith) (by linarith)
    linarith

lemma qb_window (hAnn : ∀ t ω, 0 ≤ A t ω) (hsvcnn : ∀ t ω, 0 ≤ svc t ω) (t : ℕ) (ω : Ω) :
    ∀ n : ℕ, QueueBacklog A svc U0 (t + n) ω ≤
      max (QueueBacklog A svc U0 t ω - ∑ k ∈ Finset.range n, svc (t + k) ω) 0
        + ∑ k ∈ Finset.range n, A (t + k) ω
  | 0 => by simp
  | n + 1 => by
    rw [show t + (n + 1) = (t + n) + 1 from rfl, qb_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have ih := qb_window hAnn hsvcnn t ω n
    set Q := QueueBacklog A svc U0 t ω
    set S := ∑ k ∈ Finset.range n, svc (t + k) ω
    set Asum := ∑ k ∈ Finset.range n, A (t + k) ω
    have hAs : 0 ≤ Asum := Finset.sum_nonneg (fun k _ => hAnn (t + k) ω)
    have hs := hsvcnn (t + n) ω
    have ha := hAnn (t + n) ω
    have key : max (Q - S) 0 - svc (t + n) ω ≤ max (Q - (S + svc (t + n) ω)) 0 := by
      rcases le_total (Q - S) 0 with h | h
      · rw [max_eq_right h]
        have := le_max_right (Q - (S + svc (t + n) ω)) 0
        linarith
      · rw [max_eq_left h]
        have := le_max_left (Q - (S + svc (t + n) ω)) 0
        linarith
    have h0 := le_max_right (Q - (S + svc (t + n) ω)) 0
    have : max (QueueBacklog A svc U0 (t + n) ω - svc (t + n) ω) 0 ≤
        max (Q - (S + svc (t + n) ω)) 0 + Asum :=
      max_le (by linarith) (by linarith)
    linarith

lemma sq_step (q q' S Asum : ℝ) (hq : 0 ≤ q) (hq' : 0 ≤ q') (hS : 0 ≤ S) (hA : 0 ≤ Asum)
    (h : q' ≤ max (q - S) 0 + Asum) :
    q' ^ 2 ≤ q ^ 2 + S ^ 2 + Asum ^ 2 - 2 * q * S + 2 * q * Asum := by
  set m := max (q - S) 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  have hmq : m ≤ q := max_le (by linarith) hq
  have hm2 : m ^ 2 ≤ (q - S) ^ 2 := by
    rcases le_total (q - S) 0 with h' | h'
    · rw [hm, max_eq_right h']; nlinarith [sq_nonneg (q - S)]
    · rw [hm, max_eq_left h']
  have h1 : q' ^ 2 ≤ (m + Asum) ^ 2 := pow_le_pow_left₀ hq' h 2
  nlinarith [mul_le_mul_of_nonneg_right hmq hA]

end Det

section Prob

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma qb_meas (𝓕 : Filtration ℕ m0) (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)
    (hU0 : Measurable[𝓕 0] U0) (hA : ∀ t, Measurable[𝓕 (t + 1)] (A t))
    (hs : ∀ t, Measurable[𝓕 (t + 1)] (svc t)) :
    ∀ t, Measurable[𝓕 t] (QueueBacklog A svc U0 t)
  | 0 => hU0
  | t + 1 => by
    have h1 : Measurable[𝓕 (t + 1)] (QueueBacklog A svc U0 t) :=
      (qb_meas 𝓕 A svc U0 hU0 hA hs t).mono (𝓕.mono (Nat.le_succ t)) le_rfl
    show Measurable[𝓕 (t + 1)] (fun ω => max (QueueBacklog A svc U0 t ω - svc t ω) 0 + A t ω)
    exact ((h1.sub (hs t)).max measurable_const).add (hA t)

lemma integrable_mul_of_sq {f g : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (hg : AEStronglyMeasurable g P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) (hg2 : Integrable (fun ω => g ω ^ 2) P) :
    Integrable (fun ω => f ω * g ω) P := by
  refine Integrable.mono' ((hf2.add hg2).div_const 2) (hf.mul hg) ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  show ‖f ω * g ω‖ ≤ (f ω ^ 2 + g ω ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]

lemma cond_upper {m : MeasurableSpace Ω} (hm : m ≤ m0) (f X : Ω → ℝ) (c : ℝ)
    (hf : StronglyMeasurable[m] f) (hfnn : ∀ ω, 0 ≤ f ω) (hfint : Integrable f P)
    (hX : Integrable X P) (hfX : Integrable (fun ω => f ω * X ω) P)
    (hb : P[X|m] ≤ᵐ[P] fun _ => c) :
    ∫ ω, f ω * X ω ∂P ≤ c * ∫ ω, f ω ∂P := by
  have h2 : P[f * X|m] =ᵐ[P] f * P[X|m] := condExp_mul_of_stronglyMeasurable_left hf hfX hX
  have h1 : ∫ ω, f ω * X ω ∂P = ∫ ω, (f * P[X|m]) ω ∂P := by
    rw [← integral_congr_ae h2, integral_condExp hm]; rfl
  rw [h1]
  calc ∫ ω, (f * P[X|m]) ω ∂P ≤ ∫ ω, f ω * c ∂P := by
        refine integral_mono_ae (integrable_condExp.congr h2) (hfint.mul_const c) ?_
        filter_upwards [hb] with ω hω
        exact mul_le_mul_of_nonneg_left hω (hfnn ω)
    _ = c * ∫ ω, f ω ∂P := by rw [integral_mul_const]; ring

lemma cond_lower {m : MeasurableSpace Ω} (hm : m ≤ m0) (f X : Ω → ℝ) (c : ℝ)
    (hf : StronglyMeasurable[m] f) (hfnn : ∀ ω, 0 ≤ f ω) (hfint : Integrable f P)
    (hX : Integrable X P) (hfX : Integrable (fun ω => f ω * X ω) P)
    (hb : (fun _ => c) ≤ᵐ[P] P[X|m]) :
    c * ∫ ω, f ω ∂P ≤ ∫ ω, f ω * X ω ∂P := by
  have h2 : P[f * X|m] =ᵐ[P] f * P[X|m] := condExp_mul_of_stronglyMeasurable_left hf hfX hX
  have h1 : ∫ ω, f ω * X ω ∂P = ∫ ω, (f * P[X|m]) ω ∂P := by
    rw [← integral_congr_ae h2, integral_condExp hm]; rfl
  rw [h1]
  calc c * ∫ ω, f ω ∂P = ∫ ω, f ω * c ∂P := by rw [integral_mul_const]; ring
    _ ≤ ∫ ω, (f * P[X|m]) ω ∂P := by
        refine integral_mono_ae (hfint.mul_const c) (integrable_condExp.congr h2) ?_
        filter_upwards [hb] with ω hω
        exact mul_le_mul_of_nonneg_left hω (hfnn ω)

lemma intg_mul_fsum {f : Ω → ℝ} (A : ℕ → Ω → ℝ)
    (hfA : ∀ τ, Integrable (fun ω => f ω * A τ ω) P) (s : Finset ℕ) (g : ℕ → ℕ) :
    Integrable (fun ω => f ω * ∑ k ∈ s, A (g k) ω) P := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum (f := fun k ω => f ω * A (g k) ω) _ (fun k _ => hfA (g k))

lemma window_split (A : ℕ → Ω → ℝ) (f : Ω → ℝ) (T : ℕ) (hT : 0 < T) (t0 m : ℕ) (ω : Ω) :
    f ω * ∑ k ∈ Finset.range ((m + 1) * T), A (t0 + k) ω =
      f ω * ∑ k ∈ Finset.range (m * T), A (t0 + k) ω +
      (T : ℝ) * (f ω * ((1 / (T : ℝ)) * ∑ k ∈ Finset.range T, A ((t0 + m * T) + k) ω)) := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [show (m + 1) * T = m * T + T by ring, Finset.sum_range_add]
  simp_rw [← add_assoc]
  field_simp

lemma window_upper (𝓕 : Filtration ℕ m0) (A : ℕ → Ω → ℝ) (c : ℝ) (T : ℕ) (hT : 0 < T)
    (hb : ∀ s : ℕ, (P[(fun ω => (1 / (T : ℝ)) * ∑ k ∈ Finset.range T, A (s + k) ω) | 𝓕 s])
        ≤ᵐ[P] (fun _ => c))
    (hAint : ∀ t, Integrable (A t) P) (f : Ω → ℝ) (t0 : ℕ) (hf : StronglyMeasurable[𝓕 t0] f)
    (hfnn : ∀ ω, 0 ≤ f ω) (hfint : Integrable f P)
    (hfA : ∀ τ, Integrable (fun ω => f ω * A τ ω) P) :
    ∀ m : ℕ, ∫ ω, f ω * ∑ k ∈ Finset.range (m * T), A (t0 + k) ω ∂P ≤
      ((m * T : ℕ) : ℝ) * c * ∫ ω, f ω ∂P
  | 0 => by simp
  | m + 1 => by
    have ih := window_upper 𝓕 A c T hT hb hAint f t0 hf hfnn hfint hfA m
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    simp_rw [window_split A f T hT t0 m]
    have hX : Integrable (fun ω => (1 / (T : ℝ)) *
        ∑ k ∈ Finset.range T, A ((t0 + m * T) + k) ω) P :=
      (integrable_finsetSum (f := fun k => A ((t0 + m * T) + k)) _
        (fun k _ => hAint _)).const_mul _
    have hfX : Integrable (fun ω => f ω * ((1 / (T : ℝ)) *
        ∑ k ∈ Finset.range T, A ((t0 + m * T) + k) ω)) P := by
      refine ((intg_mul_fsum A hfA (Finset.range T) (fun k => (t0 + m * T) + k)).const_mul
        (1 / (T : ℝ))).congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      ring
    have hblock := cond_upper (𝓕.le (t0 + m * T)) f _ c
      (hf.mono (𝓕.mono (Nat.le_add_right _ _))) hfnn hfint hX hfX (hb (t0 + m * T))
    rw [integral_add (intg_mul_fsum A hfA _ _) (hfX.const_mul _), integral_const_mul]
    have := mul_le_mul_of_nonneg_left hblock hTpos.le
    push_cast at ih ⊢
    nlinarith

lemma window_lower (𝓕 : Filtration ℕ m0) (A : ℕ → Ω → ℝ) (c : ℝ) (T : ℕ) (hT : 0 < T)
    (hb : ∀ s : ℕ, (fun _ => c) ≤ᵐ[P]
        (P[(fun ω => (1 / (T : ℝ)) * ∑ k ∈ Finset.range T, A (s + k) ω) | 𝓕 s]))
    (hAint : ∀ t, Integrable (A t) P) (f : Ω → ℝ) (t0 : ℕ) (hf : StronglyMeasurable[𝓕 t0] f)
    (hfnn : ∀ ω, 0 ≤ f ω) (hfint : Integrable f P)
    (hfA : ∀ τ, Integrable (fun ω => f ω * A τ ω) P) :
    ∀ m : ℕ, ((m * T : ℕ) : ℝ) * c * ∫ ω, f ω ∂P ≤
      ∫ ω, f ω * ∑ k ∈ Finset.range (m * T), A (t0 + k) ω ∂P
  | 0 => by simp
  | m + 1 => by
    have ih := window_lower 𝓕 A c T hT hb hAint f t0 hf hfnn hfint hfA m
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    simp_rw [window_split A f T hT t0 m]
    have hX : Integrable (fun ω => (1 / (T : ℝ)) *
        ∑ k ∈ Finset.range T, A ((t0 + m * T) + k) ω) P :=
      (integrable_finsetSum (f := fun k => A ((t0 + m * T) + k)) _
        (fun k _ => hAint _)).const_mul _
    have hfX : Integrable (fun ω => f ω * ((1 / (T : ℝ)) *
        ∑ k ∈ Finset.range T, A ((t0 + m * T) + k) ω)) P := by
      refine ((intg_mul_fsum A hfA (Finset.range T) (fun k => (t0 + m * T) + k)).const_mul
        (1 / (T : ℝ))).congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      ring
    have hblock := cond_lower (𝓕.le (t0 + m * T)) f _ c
      (hf.mono (𝓕.mono (Nat.le_add_right _ _))) hfnn hfint hX hfX (hb (t0 + m * T))
    rw [integral_add (intg_mul_fsum A hfA _ _) (hfX.const_mul _), integral_const_mul]
    have := mul_le_mul_of_nonneg_left hblock hTpos.le
    push_cast at ih ⊢
    nlinarith

lemma win_sq (X : ℕ → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) P) (K : ℝ) (hK : ∀ t, ∫ ω, X t ω ^ 2 ∂P ≤ K)
    (t n : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range n, X (t + k) ω) ^ 2) P ∧
      ∫ ω, (∑ k ∈ Finset.range n, X (t + k) ω) ^ 2 ∂P ≤ n * (n * K) := by
  have hg : Integrable (fun ω => (n : ℝ) * ∑ k ∈ Finset.range n, X (t + k) ω ^ 2) P :=
    (integrable_finsetSum (f := fun k ω => X (t + k) ω ^ 2) _ (fun k _ => hX2 _)).const_mul _
  have hbound : ∀ ω, (∑ k ∈ Finset.range n, X (t + k) ω) ^ 2 ≤
      (n : ℝ) * ∑ k ∈ Finset.range n, X (t + k) ω ^ 2 := by
    intro ω
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := fun k => X (t + k) ω)
    simpa using this
  have hmeas : Measurable (fun ω => (∑ k ∈ Finset.range n, X (t + k) ω) ^ 2) :=
    (Finset.measurable_sum (f := fun k => X (t + k)) _ (fun k _ => hXm _)).pow_const 2
  have hint : Integrable (fun ω => (∑ k ∈ Finset.range n, X (t + k) ω) ^ 2) P :=
    hg.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hbound ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, (∑ k ∈ Finset.range n, X (t + k) ω) ^ 2 ∂P
      ≤ ∫ ω, (n : ℝ) * ∑ k ∈ Finset.range n, X (t + k) ω ^ 2 ∂P :=
        integral_mono hint hg hbound
    _ = (n : ℝ) * ∑ k ∈ Finset.range n, ∫ ω, X (t + k) ω ^ 2 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ (fun k _ => hX2 _)]
    _ ≤ (n : ℝ) * (n * K) := by
        gcongr
        calc ∑ k ∈ Finset.range n, ∫ ω, X (t + k) ω ^ 2 ∂P
            ≤ ∑ k ∈ Finset.range n, K := Finset.sum_le_sum (fun k _ => hK _)
          _ = n * K := by simp

end Prob

section Drift

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

lemma drift_int (w w' s a : Ω → ℝ) (iw' : Integrable (fun ω => w' ω ^ 2) P)
    (iw : Integrable (fun ω => w ω ^ 2) P) (is : Integrable (fun ω => s ω ^ 2) P)
    (ia : Integrable (fun ω => a ω ^ 2) P) (iws : Integrable (fun ω => w ω * s ω) P)
    (iwa : Integrable (fun ω => w ω * a ω) P)
    (h : ∀ ω, w' ω ^ 2 ≤ w ω ^ 2 + s ω ^ 2 + a ω ^ 2 - 2 * (w ω * s ω) + 2 * (w ω * a ω)) :
    ∫ ω, w' ω ^ 2 ∂P ≤ ∫ ω, w ω ^ 2 ∂P + ∫ ω, s ω ^ 2 ∂P + ∫ ω, a ω ^ 2 ∂P
      - 2 * ∫ ω, w ω * s ω ∂P + 2 * ∫ ω, w ω * a ω ∂P := by
  have i12 : Integrable (fun ω => w ω ^ 2 + s ω ^ 2) P := iw.add is
  have i123 : Integrable (fun ω => w ω ^ 2 + s ω ^ 2 + a ω ^ 2) P := i12.add ia
  have i1234 : Integrable (fun ω => w ω ^ 2 + s ω ^ 2 + a ω ^ 2 - 2 * (w ω * s ω)) P :=
    i123.sub (iws.const_mul 2)
  have iall : Integrable (fun ω => w ω ^ 2 + s ω ^ 2 + a ω ^ 2 - 2 * (w ω * s ω)
      + 2 * (w ω * a ω)) P := i1234.add (iwa.const_mul 2)
  calc ∫ ω, w' ω ^ 2 ∂P ≤ ∫ ω, (w ω ^ 2 + s ω ^ 2 + a ω ^ 2 - 2 * (w ω * s ω)
        + 2 * (w ω * a ω)) ∂P := integral_mono iw' iall h
    _ = _ := by
      rw [integral_add i1234 (iwa.const_mul 2), integral_sub i123 (iws.const_mul 2),
        integral_add i12 ia, integral_add iw is, integral_const_mul, integral_const_mul]

end Drift

end P2M7d80

open NetworkControl.CapacityRegion MeasureTheory in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ) (lam mu : ℝ)
    (hU0meas : Measurable[𝓕 0] U0) (hU0nn : ∀ ω, 0 ≤ U0 ω) (hU0int : Integrable U0 P)
    (hAadapt : ∀ t : ℕ, Measurable[𝓕 (t + 1)] (A t)) (hAnn : ∀ t ω, 0 ≤ A t ω)
    (hsvcadapt : ∀ t : ℕ, Measurable[𝓕 (t + 1)] (svc t)) (hsvcnn : ∀ t ω, 0 ≤ svc t ω)
    (hA : AdmissibleArrival P 𝓕 A lam)
    (hsvc : AdmissibleService P 𝓕 svc mu) :
    (StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P) → lam ≤ mu) ∧
      (lam < mu → StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P)) := by
  have hAm : ∀ t, Measurable (A t) := fun t => (hAadapt t).mono (𝓕.le (t + 1)) le_rfl
  have hsm : ∀ t, Measurable (svc t) := fun t => (hsvcadapt t).mono (𝓕.le (t + 1)) le_rfl
  have hUmF : ∀ t, Measurable[𝓕 t] (QueueBacklog A svc U0 t) :=
    P2M7d80.qb_meas 𝓕 A svc U0 hU0meas hAadapt hsvcadapt
  have hUm : ∀ t, Measurable (QueueBacklog A svc U0 t) :=
    fun t => (hUmF t).mono (𝓕.le t) le_rfl
  have hUnn := P2M7d80.qb_nonneg A svc U0 hU0nn hAnn
  have hUint : ∀ t, Integrable (QueueBacklog A svc U0 t) P := by
    intro t
    refine Integrable.mono' (hU0int.add (integrable_finsetSum (f := fun τ => A τ)
      (Finset.range t) (fun τ _ => hA.integrable τ))) (hUm t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hUnn t ω)]
    simpa using P2M7d80.qb_upper A svc U0 hU0nn hAnn hsvcnn t ω
  constructor
  · -- (a) necessity
    rintro ⟨M, hM⟩
    by_contra hlt0
    have hlt : mu < lam := not_le.mp hlt0
    have hc : 0 < lam - mu := by linarith
    have he0 : ∀ t, 0 ≤ ∫ ω, QueueBacklog A svc U0 t ω ∂P :=
      fun t => integral_nonneg (hUnn t)
    have hsub : ∀ τ, Integrable (fun ω => A τ ω - svc τ ω) P :=
      fun τ => (hA.integrable τ).sub (hsvc.integrable τ)
    have hes : ∀ t, ∑ τ ∈ Finset.range t, (∫ ω, A τ ω ∂P - ∫ ω, svc τ ω ∂P) ≤
        ∫ ω, QueueBacklog A svc U0 t ω ∂P := by
      intro t
      calc ∑ τ ∈ Finset.range t, (∫ ω, A τ ω ∂P - ∫ ω, svc τ ω ∂P)
          = ∫ ω, ∑ τ ∈ Finset.range t, (A τ ω - svc τ ω) ∂P := by
            rw [integral_finsetSum _ (fun τ _ => hsub τ)]
            refine Finset.sum_congr rfl (fun τ _ => ?_)
            rw [integral_sub (hA.integrable τ) (hsvc.integrable τ)]
        _ ≤ ∫ ω, QueueBacklog A svc U0 t ω ∂P :=
            integral_mono (integrable_finsetSum _ (fun τ _ => hsub τ)) (hUint t)
              (fun ω => P2M7d80.qb_lower A svc U0 hU0nn t ω)
    have hconv : Filter.Tendsto (fun t : ℕ => (1 / (t : ℝ)) *
        ∑ τ ∈ Finset.range t, (∫ ω, A τ ω ∂P - ∫ ω, svc τ ω ∂P))
        Filter.atTop (nhds (lam - mu)) := by
      refine (hA.time_average.sub hsvc.time_average).congr (fun t => ?_)
      simp only [Finset.sum_sub_distrib]
      ring
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hconv.eventually (Ioi_mem_nhds (show (lam - mu) / 2 < lam - mu by linarith)))
    obtain ⟨k, hk⟩ := exists_nat_gt (4 * M / (lam - mu))
    set K : ℕ := max (N + 1) k with hK_def
    have hK1 : 1 ≤ K := le_trans (Nat.le_add_left 1 N) (le_max_left _ _)
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    have hKk : (k : ℝ) ≤ K := by exact_mod_cast le_max_right _ _
    have hlow : ∀ j, (lam - mu) / 2 * K ≤ ∫ ω, QueueBacklog A svc U0 (K + j) ω ∂P := by
      intro j
      have hj : N ≤ K + j :=
        le_trans (le_trans (Nat.le_succ N) (le_max_left _ _)) (Nat.le_add_right _ _)
      have h1 : (lam - mu) / 2 < (1 / ((K + j : ℕ) : ℝ)) *
          ∑ τ ∈ Finset.range (K + j), (∫ ω, A τ ω ∂P - ∫ ω, svc τ ω ∂P) := hN (K + j) hj
      have h3 : (K : ℝ) ≤ ((K + j : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
      have hpos : (0 : ℝ) < ((K + j : ℕ) : ℝ) := lt_of_lt_of_le hKpos h3
      rw [one_div_mul_eq_div, lt_div_iff₀ hpos] at h1
      have h2 := hes (K + j)
      nlinarith [mul_le_mul_of_nonneg_left h3 (le_of_lt (half_pos hc))]
    have hsum : (1 / ((K + K : ℕ) : ℝ)) *
        ∑ τ ∈ Finset.range (K + K), ∫ ω, QueueBacklog A svc U0 τ ω ∂P ≤ M := hM (K + K)
    rw [Finset.sum_range_add] at hsum
    have hA1 : 0 ≤ ∑ τ ∈ Finset.range K, ∫ ω, QueueBacklog A svc U0 τ ω ∂P :=
      Finset.sum_nonneg (fun τ _ => he0 τ)
    have hA2 : (K : ℝ) * ((lam - mu) / 2 * K) ≤
        ∑ j ∈ Finset.range K, ∫ ω, QueueBacklog A svc U0 (K + j) ω ∂P := by
      calc (K : ℝ) * ((lam - mu) / 2 * K) = ∑ j ∈ Finset.range K, (lam - mu) / 2 * (K : ℝ) := by
            simp
        _ ≤ _ := Finset.sum_le_sum (fun j _ => hlow j)
    have hpos2 : (0 : ℝ) < ((K + K : ℕ) : ℝ) := by push_cast; linarith
    rw [one_div_mul_eq_div, div_le_iff₀ hpos2] at hsum
    push_cast at hsum
    have hk' : 4 * M < (lam - mu) * K := by
      have := (div_lt_iff₀ hc).mp hk
      nlinarith [mul_le_mul_of_nonneg_right hKk hc.le]
    nlinarith [mul_lt_mul_of_pos_left hk' hKpos]
  · -- (b) sufficiency
    intro hlt
    obtain ⟨Amax, hAm2⟩ := hA.second_moment_bound
    obtain ⟨smax, hsmax⟩ := hsvc.upper_bound
    have hδ : 0 < (mu - lam) / 4 := by linarith
    obtain ⟨TA, hTA, hbA⟩ := hA.averaging_bound _ hδ
    obtain ⟨TS, hTS, hbS⟩ := hsvc.averaging_bound _ hδ
    set W := QueueBacklog A svc (fun _ : Ω => (0 : ℝ)) with hW_def
    have hWmF : ∀ t, Measurable[𝓕 t] (W t) :=
      P2M7d80.qb_meas 𝓕 A svc _ measurable_const hAadapt hsvcadapt
    have hWsF : ∀ t, StronglyMeasurable[𝓕 t] (W t) := fun t => (hWmF t).stronglyMeasurable
    have hWm : ∀ t, Measurable (W t) := fun t => (hWmF t).mono (𝓕.le t) le_rfl
    have hWnn : ∀ t ω, 0 ≤ W t ω := P2M7d80.qb_nonneg A svc _ (fun _ => le_rfl) hAnn
    have hWle : ∀ t ω, W t ω ≤ ∑ τ ∈ Finset.range t, A τ ω := fun t ω => by
      simpa using P2M7d80.qb_upper A svc (fun _ : Ω => (0 : ℝ)) (fun _ => le_rfl) hAnn hsvcnn t ω
    have hA2int : ∀ t, Integrable (fun ω => A t ω ^ 2) P := fun t => (hAm2 t).1
    have hEA2 : ∀ t, ∫ ω, A t ω ^ 2 ∂P ≤ Amax ^ 2 := by
      intro t
      calc ∫ ω, A t ω ^ 2 ∂P = ∫ ω, (P[fun ω => A t ω ^ 2 | 𝓕 t]) ω ∂P :=
            (integral_condExp (𝓕.le t)).symm
        _ ≤ ∫ ω, Amax ^ 2 ∂P :=
            integral_mono_ae integrable_condExp (integrable_const _) (hAm2 t).2
        _ = Amax ^ 2 := by simp
    have hs2le : ∀ t ω, svc t ω ^ 2 ≤ smax ^ 2 :=
      fun t ω => pow_le_pow_left₀ (hsvcnn t ω) (hsmax t ω) 2
    have hs2int : ∀ t, Integrable (fun ω => svc t ω ^ 2) P := fun t =>
      (integrable_const (smax ^ 2)).mono' ((hsm t).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hs2le t ω)
    have hEs2 : ∀ t, ∫ ω, svc t ω ^ 2 ∂P ≤ smax ^ 2 := fun t => by
      calc ∫ ω, svc t ω ^ 2 ∂P ≤ ∫ ω, smax ^ 2 ∂P :=
            integral_mono (hs2int t) (integrable_const _) (fun ω => hs2le t ω)
        _ = smax ^ 2 := by simp
    have hWint : ∀ t, Integrable (W t) P := by
      intro t
      refine (integrable_finsetSum (f := fun τ => A τ) (Finset.range t)
        (fun τ _ => hA.integrable τ)).mono' (hWm t).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (hWnn t ω)]
      exact hWle t ω
    have hW2int : ∀ t, Integrable (fun ω => W t ω ^ 2) P := by
      intro t
      have h := (P2M7d80.win_sq A hAm hA2int _ hEA2 0 t).1
      refine h.mono' ((hWm t).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simp only [zero_add]
      exact pow_le_pow_left₀ (hWnn t ω) (hWle t ω) 2
    have hWA : ∀ t τ, Integrable (fun ω => W t ω * A τ ω) P := fun t τ =>
      P2M7d80.integrable_mul_of_sq (hWm t).aestronglyMeasurable (hAm τ).aestronglyMeasurable
        (hW2int t) (hA2int τ)
    have hWS : ∀ t τ, Integrable (fun ω => W t ω * svc τ ω) P := fun t τ =>
      P2M7d80.integrable_mul_of_sq (hWm t).aestronglyMeasurable (hsm τ).aestronglyMeasurable
        (hW2int t) (hs2int τ)
    set n : ℕ := TS * TA with hn_def
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hTS.ne' hTA.ne')
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hupper : ∀ t, ∫ ω, W t ω * ∑ k ∈ Finset.range n, A (t + k) ω ∂P ≤
        (n : ℝ) * (lam + (mu - lam) / 4) * ∫ ω, W t ω ∂P := fun t =>
      P2M7d80.window_upper 𝓕 A _ TA hTA hbA hA.integrable (W t) t (hWsF t) (hWnn t)
        (hWint t) (hWA t) TS
    have hlower : ∀ t, (n : ℝ) * (mu - (mu - lam) / 4) * ∫ ω, W t ω ∂P ≤
        ∫ ω, W t ω * ∑ k ∈ Finset.range n, svc (t + k) ω ∂P := by
      intro t
      have := P2M7d80.window_lower 𝓕 svc _ TS hTS hbS hsvc.integrable (W t) t (hWsF t) (hWnn t)
        (hWint t) (hWS t) TA
      rw [Nat.mul_comm TA TS] at this
      exact this
    set B : ℝ := (n : ℝ) * ((n : ℝ) * smax ^ 2) + (n : ℝ) * ((n : ℝ) * Amax ^ 2) with hB_def
    set κ : ℝ := (n : ℝ) * (mu - lam) with hκ_def
    have hκ : 0 < κ := mul_pos hnpos (by linarith)
    have hB0 : 0 ≤ B := by positivity
    have hdrift : ∀ t, ∫ ω, W (t + n) ω ^ 2 ∂P ≤
        ∫ ω, W t ω ^ 2 ∂P + B - κ * ∫ ω, W t ω ∂P := by
      intro t
      have hSS := P2M7d80.win_sq svc hsm hs2int _ hEs2 t n
      have hSA := P2M7d80.win_sq A hAm hA2int _ hEA2 t n
      have hmS : Measurable (fun ω => ∑ k ∈ Finset.range n, svc (t + k) ω) :=
        Finset.measurable_sum (f := fun k => svc (t + k)) _ (fun k _ => hsm _)
      have hmA : Measurable (fun ω => ∑ k ∈ Finset.range n, A (t + k) ω) :=
        Finset.measurable_sum (f := fun k => A (t + k)) _ (fun k _ => hAm _)
      have hd := P2M7d80.drift_int (W t) (W (t + n))
        (fun ω => ∑ k ∈ Finset.range n, svc (t + k) ω)
        (fun ω => ∑ k ∈ Finset.range n, A (t + k) ω) (hW2int _) (hW2int t) hSS.1 hSA.1
        (P2M7d80.integrable_mul_of_sq (hWm t).aestronglyMeasurable hmS.aestronglyMeasurable
          (hW2int t) hSS.1)
        (P2M7d80.integrable_mul_of_sq (hWm t).aestronglyMeasurable hmA.aestronglyMeasurable
          (hW2int t) hSA.1)
        (fun ω => by
          have := P2M7d80.sq_step (W t ω) (W (t + n) ω)
            (∑ k ∈ Finset.range n, svc (t + k) ω) (∑ k ∈ Finset.range n, A (t + k) ω)
            (hWnn _ _) (hWnn _ _) (Finset.sum_nonneg (fun k _ => hsvcnn _ _))
            (Finset.sum_nonneg (fun k _ => hAnn _ _))
            (P2M7d80.qb_window A svc _ hAnn hsvcnn t ω n)
          linarith)
      have h1 := hSS.2
      have h2 := hSA.2
      have h3 := hupper t
      have h4 := hlower t
      rw [hB_def, hκ_def]
      linarith
    set D : ℕ → ℝ := fun t => ∫ ω, W t ω ^ 2 ∂P with hD_def
    set E : ℕ → ℝ := fun t => ∫ ω, W t ω ∂P with hE_def
    set C : ℝ := ∑ k ∈ Finset.range n, D k with hC_def
    have hD0 : ∀ t, 0 ≤ D t := fun t => integral_nonneg (fun ω => sq_nonneg _)
    have hC0 : 0 ≤ C := Finset.sum_nonneg (fun k _ => hD0 k)
    have hsumE : ∀ N : ℕ, κ * ∑ t ∈ Finset.range N, E t ≤ C + N * B := by
      intro N
      have h1 : ∑ t ∈ Finset.range N, D (t + n) ≤
          ∑ t ∈ Finset.range N, (D t + B - κ * E t) :=
        Finset.sum_le_sum (fun t _ => hdrift t)
      have h2 : ∑ t ∈ Finset.range N, (D t + B - κ * E t) =
          ∑ t ∈ Finset.range N, D t + N * B - κ * ∑ t ∈ Finset.range N, E t := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      have tele : ∑ t ∈ Finset.range N, D t + ∑ k ∈ Finset.range n, D (N + k) =
          C + ∑ t ∈ Finset.range N, D (t + n) := by
        rw [← Finset.sum_range_add, hC_def, add_comm N n, Finset.sum_range_add]
        congr 1
        exact Finset.sum_congr rfl (fun t _ => by rw [add_comm])
      have h3 : 0 ≤ ∑ k ∈ Finset.range n, D (N + k) := Finset.sum_nonneg (fun k _ => hD0 _)
      linarith
    have hU0i : 0 ≤ ∫ ω, U0 ω ∂P := integral_nonneg hU0nn
    refine ⟨∫ ω, U0 ω ∂P + (C + B) / κ, fun N => ?_⟩
    show (1 / (N : ℝ)) * ∑ τ ∈ Finset.range N, ∫ ω, QueueBacklog A svc U0 τ ω ∂P ≤ _
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      rw [Finset.sum_range_zero, mul_zero]
      exact add_nonneg hU0i (div_nonneg (by linarith) hκ.le)
    · have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      have hUE : ∀ t, ∫ ω, QueueBacklog A svc U0 t ω ∂P ≤ ∫ ω, U0 ω ∂P + E t := by
        intro t
        rw [hE_def, ← integral_add hU0int (hWint t)]
        exact integral_mono (hUint t) (hU0int.add (hWint t))
          (fun ω => P2M7d80.qb_le_add A svc U0 hU0nn t ω)
      have hS1 : ∑ τ ∈ Finset.range N, ∫ ω, QueueBacklog A svc U0 τ ω ∂P ≤
          N * ∫ ω, U0 ω ∂P + ∑ τ ∈ Finset.range N, E τ := by
        calc _ ≤ ∑ τ ∈ Finset.range N, (∫ ω, U0 ω ∂P + E τ) := Finset.sum_le_sum (fun τ _ => hUE τ)
          _ = _ := by rw [Finset.sum_add_distrib]; simp
      have hS2 : ∑ τ ∈ Finset.range N, E τ ≤ (C + B) / κ * N := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
        have := hsumE N
        nlinarith
      rw [one_div_mul_eq_div, div_le_iff₀ (by linarith)]
      nlinarith
