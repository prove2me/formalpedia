-- Prove2me | solution 1 for KoanaKPaths.Main.one_sketching_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:00:37.058728+00:00
-- url     : https://prove2.me/submissions/0b96e485-c9e3-4a4d-9288-e8dd1d984d53

import Theorems.Thm_KoanaKPaths_Main_fixed_matrix_sketching_moments

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KoanaKPaths.Main.SignMoments

lemma uniform_lintegral {α : Type} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂(PMF.uniformOfFintype α).toMeasure =
      ENNReal.ofReal (uniformMean f) := by
  rw [lintegral_fintype]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]
  unfold uniformMean
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos (α := α)),
    ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
  simp only [ENNReal.ofReal_natCast, div_eq_mul_inv, Finset.sum_mul]

lemma frob_nonneg {d t : ℕ} (X : Fin d → Fin t → ℝ) : 0 ≤ realFrobSq X := by
  apply Finset.sum_nonneg
  intro u _
  exact Finset.sum_nonneg (fun b _ => sq_nonneg _)

lemma measurable_frob {d t : ℕ} : Measurable (realFrobSq (d := d) (t := t)) := by
  unfold realFrobSq
  fun_prop

lemma measurable_signMul {ℓ d t : ℕ} :
    Measurable (fun p : (Fin d → Fin t → ℝ) × (Fin ℓ → Fin d → Bool) =>
      signMul p.2 p.1) := by
  have hs : Measurable (fun b : Bool => (sgn b : ℝ)) := measurable_of_countable _
  unfold signMul
  fun_prop

lemma independent_uniform_lintegral {Ω A : Type*} {S : Type} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace S] [Fintype S] [Nonempty S]
    [MeasurableSingletonClass S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → A) (R : Ω → S)
    (hX : Measurable X) (hR : Measurable R)
    (hRlaw : P.map R = (PMF.uniformOfFintype S).toMeasure) (hind : IndepFun X R P)
    (F : A × S → ℝ) (hF : Measurable F) (hn : ∀ p, 0 ≤ F p) :
    ∫⁻ ω, ENNReal.ofReal (F (X ω, R ω)) ∂P =
      ∫⁻ x, ENNReal.ofReal (uniformMean (fun r : S => F (x, r))) ∂P.map X := by
  have hEF : Measurable (fun p => ENNReal.ofReal (F p)) := ENNReal.measurable_ofReal.comp hF
  rw [← lintegral_map hEF (hX.prodMk hR),
    IndepFun.map_prod_eq_prod_map_map hX.aemeasurable hR.aemeasurable hind, hRlaw,
    lintegral_prod _ hEF.aemeasurable]
  congr 1
  funext x
  exact uniform_lintegral (fun r : S => F (x,r)) (fun r => hn _)

 theorem one_step (d t ℓ : ℕ) (hd : 0 < d) (ht : 0 < t) (hℓ : 0 < ℓ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Fin d → Fin t → ℝ) (R : Ω → Fin ℓ → Fin d → Bool)
    (hX : Measurable X) (hR : Measurable R)
    (hRlaw : P.map R = (PMF.uniformOfFintype (Fin ℓ → Fin d → Bool)).toMeasure)
    (hind : IndepFun X R P) :
    ∫⁻ ω, ENNReal.ofReal (realFrobSq (signMul (R ω) (X ω))) ∂P =
        (ℓ : ENNReal) * ∫⁻ ω, ENNReal.ofReal (realFrobSq (X ω)) ∂P ∧
      ∫⁻ ω, ENNReal.ofReal (realFrobSq (signMul (R ω) (X ω)) ^ 2) ∂P ≤
        ENNReal.ofReal ((ℓ : ℝ) ^ 2 * (1 + 2 / (ℓ : ℝ))) *
          ∫⁻ ω, ENNReal.ofReal (realFrobSq (X ω) ^ 2) ∂P := by
  have hC : ((ℓ : ℝ)^2 + 2*ℓ) = (ℓ : ℝ)^2 * (1 + 2/(ℓ : ℝ)) := by
    have hl : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
    field_simp
    <;> ring
  have hfm : Measurable (fun x : Fin d → Fin t → ℝ => ENNReal.ofReal (realFrobSq x)) :=
    ENNReal.measurable_ofReal.comp measurable_frob
  have hfm2 : Measurable (fun x : Fin d → Fin t → ℝ => ENNReal.ofReal (realFrobSq x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_frob.pow_const 2)
  constructor
  · rw [independent_uniform_lintegral P X R hX hR hRlaw hind
      (fun p => realFrobSq (signMul p.2 p.1))
      (measurable_frob.comp measurable_signMul) (fun _ => frob_nonneg _)]
    simp_rw [(KoanaKPaths.Main.fixed_matrix_sketching_moments ℓ d t _).1,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ℓ), ENNReal.ofReal_natCast]
    rw [lintegral_const_mul _ hfm,
      lintegral_map hfm hX]
  · rw [independent_uniform_lintegral P X R hX hR hRlaw hind
      (fun p => realFrobSq (signMul p.2 p.1)^2)
      ((measurable_frob.comp measurable_signMul).pow_const 2) (fun _ => sq_nonneg _)]
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (((ℓ : ℝ)^2+2*ℓ) * realFrobSq x ^ 2) ∂P.map X :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (KoanaKPaths.Main.fixed_matrix_sketching_moments ℓ d t x).2)
      _ = _ := by
        simp_rw [hC, ENNReal.ofReal_mul (by positivity : 0 ≤ (ℓ : ℝ)^2*(1+2/(ℓ : ℝ)))]
        rw [lintegral_const_mul _ hfm2,
          lintegral_map hfm2 hX]

end KoanaKPaths.Main.SignMoments

open KoanaKPaths.Main

theorem solution (d t ℓ : ℕ) (hd : 0 < d) (ht : 0 < t) (hℓ : 0 < ℓ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Fin d → Fin t → ℝ) (R : Ω → Fin ℓ → Fin d → Bool)
    (hX : Measurable X) (hR : Measurable R)
    (hRlaw : P.map R = (PMF.uniformOfFintype (Fin ℓ → Fin d → Bool)).toMeasure)
    (hind : IndepFun X R P) :
    ∫⁻ ω, ENNReal.ofReal (realFrobSq (signMul (R ω) (X ω))) ∂P =
        (ℓ : ENNReal) * ∫⁻ ω, ENNReal.ofReal (realFrobSq (X ω)) ∂P ∧
      ∫⁻ ω, ENNReal.ofReal (realFrobSq (signMul (R ω) (X ω)) ^ 2) ∂P ≤
        ENNReal.ofReal ((ℓ : ℝ) ^ 2 * (1 + 2 / (ℓ : ℝ))) *
          ∫⁻ ω, ENNReal.ofReal (realFrobSq (X ω) ^ 2) ∂P := by
  exact KoanaKPaths.Main.SignMoments.one_step d t ℓ hd ht hℓ P X R hX hR hRlaw hind
