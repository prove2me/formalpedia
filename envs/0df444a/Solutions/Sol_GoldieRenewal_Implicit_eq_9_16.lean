-- Prove2me | solution 1 for GoldieRenewal.Implicit.eq_9_16
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:36:38.434985+00:00
-- url     : https://prove2.me/submissions/33c90c47-bbd3-4803-9430-628bacd979ea

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
open MeasureTheory ProbabilityTheory


namespace GoldieRenewal.Implicit

lemma e916_tail_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A X : Ω → ℝ) (hA : Measurable A) (hX : Measurable X) (hind : IndepFun A X P) (t : ℝ) :
    Measurable (fun a : ℝ => P.real {ω | t < a * X ω}) ∧
      P.real {ω | t < A ω * X ω} = ∫ a, P.real {ω | t < a * X ω} ∂(P.map A) := by
  set S : Set (ℝ × ℝ) := {p | t < p.1 * p.2} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  have hsec : ∀ a : ℝ, (P.map X) (Prod.mk a ⁻¹' S) = P {ω | t < a * X ω} := by
    intro a
    rw [Measure.map_apply hX (measurable_prodMk_left hSm)]
    rfl
  have hmeas : Measurable (fun a : ℝ => P {ω | t < a * X ω}) := by
    have := measurable_measure_prodMk_left (ν := P.map X) hSm
    simpa [hsec] using this
  refine ⟨hmeas.ennreal_toReal, ?_⟩
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hX.aemeasurable).1 hind
  have h1 : P {ω | t < A ω * X ω} = (P.map (fun ω => (A ω, X ω))) S := by
    rw [Measure.map_apply (hA.prodMk hX) hSm]; rfl
  rw [measureReal_def, h1, hmap, Measure.prod_apply hSm]
  simp_rw [hsec]
  rw [← integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall (fun a => measure_lt_top _ _))]
  rfl

theorem eq_9_16_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M M' R : Ω → ℝ) (hM : Measurable M) (hM' : Measurable M') (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hident : IdentDistrib M' M P P)
    (hind : iIndepFun (fun i : Fin 3 => (![R, M, M'] : Fin 3 → Ω → ℝ) i) P)
    (hM_nonpos : ∀ᵐ ω ∂P, M ω ≤ 0)
    (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ) :
    TailCondPlus P (fun ω => M ω * M' ω) R κ := by
  have hκ := hC.pos
  have hmeasf : ∀ i, Measurable ((![R, M, M'] : Fin 3 → Ω → ℝ) i) := by
    intro i; fin_cases i <;> simpa
  -- independence
  have hMR : IndepFun M R P := by
    have := hind.indepFun (i := 1) (j := 0) (by decide)
    simpa using this
  have hM'MR : IndepFun M' (fun ω => M ω * R ω) P := by
    have h := hind.indepFun_prodMk hmeasf 0 1 2 (by decide) (by decide)
    have h2 := h.symm.comp (φ := id) (ψ := fun p : ℝ × ℝ => p.2 * p.1) measurable_id (by fun_prop)
    simpa [Function.comp_def] using h2
  set lam := P.map M with hlam
  have hlamM' : P.map M' = lam := hident.map_eq
  -- λ-a.e. nonpositive
  have hae : ∀ᵐ m ∂lam, m ≤ 0 :=
    (ae_map_iff hM.aemeasurable measurableSet_Iic).2 hM_nonpos
  -- φ
  set φ := tailDiffMinus P M R κ with hφ
  have hφm : Measurable φ := by
    have h1 : Antitone (fun s : ℝ => P.real {ω | R ω < -s}) := by
      intro a b hab
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith
    have h2 : Antitone (fun s : ℝ => P.real {ω | M ω * R ω < -s}) := by
      intro a b hab
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith
    have : φ = fun s => (P.real {ω | R ω < -s} - P.real {ω | M ω * R ω < -s}) * s ^ (κ - 1) := rfl
    rw [this]
    exact (h1.measurable.sub h2.measurable).mul (by fun_prop)
  set Cφ := ∫ s in Set.Ioi 0, ‖φ s‖ with hCφ
  -- the kernel
  set K : ℝ × ℝ → ℝ := fun p => if p.2 < 0 then (-p.2) ^ (κ - 1) * φ (p.1 / (-p.2)) else 0 with hK
  have hKm : Measurable K := by
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_const) _ measurable_const
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => (-p.2) ^ (κ - 1)).mul
      (hφm.comp (by fun_prop))
  -- slice integrals
  have hslice : ∀ m : ℝ, m < 0 →
      IntegrableOn (fun t => K (t, m)) (Set.Ioi 0) ∧
        ∫ t in Set.Ioi 0, ‖K (t, m)‖ = (-m) ^ κ * Cφ := by
    intro m hm
    have hb : 0 < (-m)⁻¹ := inv_pos.2 (by linarith)
    have heq : (fun t => K (t, m)) = fun t => (-m) ^ (κ - 1) * φ ((-m)⁻¹ * t) := by
      ext t; simp only [hK, if_pos hm]; rw [div_eq_inv_mul]
    have hint : IntegrableOn (fun t => φ ((-m)⁻¹ * t)) (Set.Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff _ _ hb, mul_zero]; exact h29
    refine ⟨?_, ?_⟩
    · rw [heq]; exact hint.const_mul _
    · have heq' : ∀ t, K (t, m) = (-m) ^ (κ - 1) * φ ((-m)⁻¹ * t) := fun t => congrFun heq t
      simp_rw [heq', norm_mul]
      rw [integral_const_mul]
      have := integral_comp_mul_left_Ioi (fun s => ‖φ s‖) 0 hb
      simp only [mul_zero] at this
      rw [this, smul_eq_mul, inv_inv, hCφ, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← mul_assoc]
      congr 1
      rw [← Real.rpow_add_one (by linarith)]; ring_nf
  have hslice0 : ∀ m : ℝ, ¬ m < 0 → ∀ t, K (t, m) = 0 := by
    intro m hm t; simp only [hK, if_neg hm]
  -- integrability on the product
  have hmom : Integrable (fun m : ℝ => |m| ^ κ) lam :=
    ⟨(by fun_prop : Measurable fun m : ℝ => |m| ^ κ).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall (fun x => by positivity))).2
        (by rw [hC.moment_eq_one]; simp)⟩
  have : IsProbabilityMeasure lam := ⟨hC.probability⟩
  have hKint : Integrable K ((volume.restrict (Set.Ioi (0:ℝ))).prod lam) := by
    rw [integrable_prod_iff' hKm.aestronglyMeasurable]
    constructor
    · filter_upwards with m
      by_cases hm : m < 0
      · exact (hslice m hm).1
      · simp_rw [hslice0 m hm]; exact integrable_zero _ _ _
    · have hsm := (hKm.norm.aestronglyMeasurable
          (μ := (volume.restrict (Set.Ioi (0:ℝ))).prod lam)).prod_swap.integral_prod_right'
      refine (hmom.mul_const Cφ).mono' hsm ?_
      filter_upwards with m
      have hC0 : 0 ≤ Cφ := setIntegral_nonneg measurableSet_Ioi (fun _ _ => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      by_cases hm : m < 0
      · rw [(hslice m hm).2, abs_of_neg hm]
      · simp_rw [hslice0 m hm, norm_zero, integral_zero]; positivity
  have hDint : IntegrableOn (fun t => ∫ m, K (t, m) ∂lam) (Set.Ioi 0) :=
    hKint.integral_prod_left
  -- identification
  refine (h28.add hDint).congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht : 0 < t := ht
  obtain ⟨hg1m, hg1⟩ := e916_tail_prod P M R hM hR hMR t
  obtain ⟨hg2m, hg2⟩ := e916_tail_prod P M' (fun ω => M ω * R ω) hM' (hM.mul hR) hM'MR t
  rw [hlamM'] at hg2
  have hset : {ω | t < M ω * M' ω * R ω} = {ω | t < M' ω * (M ω * R ω)} := by
    ext ω; simp only [Set.mem_setOf_eq]; ring_nf
  have hg1i : Integrable (fun a : ℝ => P.real {ω | t < a * R ω}) lam :=
    Integrable.of_bound hg1m.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one))
  have hg2i : Integrable (fun a : ℝ => P.real {ω | t < a * (M ω * R ω)}) lam :=
    Integrable.of_bound hg2m.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one))
  have hpt : ∀ m : ℝ, m ≤ 0 → t ^ (κ - 1) *
      (P.real {ω | t < m * R ω} - P.real {ω | t < m * (M ω * R ω)}) = K (t, m) := by
    intro m hm
    rcases hm.lt_or_eq with hm | hm
    · simp only [hK, if_pos hm, hφ, tailDiffMinus]
      have e1 : {ω | t < m * R ω} = {ω | R ω < -(t / -m)} := by
        ext ω; simp only [Set.mem_setOf_eq]
        rw [div_neg, neg_neg, lt_div_iff_of_neg hm, mul_comm]
      have e2 : {ω | t < m * (M ω * R ω)} = {ω | M ω * R ω < -(t / -m)} := by
        ext ω; simp only [Set.mem_setOf_eq]
        rw [div_neg, neg_neg, lt_div_iff_of_neg hm, mul_comm]
      rw [e1, e2]
      have : (-m) ^ (κ - 1) * (t / -m) ^ (κ - 1) = t ^ (κ - 1) := by
        rw [← Real.mul_rpow (by linarith) (div_nonneg ht.le (by linarith))]
        congr 1; rw [mul_div_assoc']; exact mul_div_cancel_left₀ t (by linarith : (-m) ≠ 0)
      rw [← this]; ring
    · subst hm
      simp only [hK, lt_irrefl, if_false, zero_mul]
      have : {ω : Ω | t < 0} = ∅ := by ext; simp; linarith
      rw [this]; simp
  simp only [Pi.add_apply]
  symm
  rw [← integral_congr_ae (hae.mono (fun m hm => hpt m hm)), integral_const_mul,
    integral_sub hg1i hg2i, ← hg1, ← hg2, ← hset]
  simp only [tailDiffPlus]
  ring

end GoldieRenewal.Implicit

open GoldieRenewal.Implicit


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M M' R : Ω → ℝ) (hM : Measurable M) (hM' : Measurable M') (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hident : IdentDistrib M' M P P)
    (hind : iIndepFun (fun i : Fin 3 => (![R, M, M'] : Fin 3 → Ω → ℝ) i) P)
    (hM_nonpos : ∀ᵐ ω ∂P, M ω ≤ 0)
    (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ) :
    TailCondPlus P (fun ω => M ω * M' ω) R κ := by
  exact eq_9_16_core P M M' R hM hM' hR κ hC hident hind hM_nonpos h28 h29
