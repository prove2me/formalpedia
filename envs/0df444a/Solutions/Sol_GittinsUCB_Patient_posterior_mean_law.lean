-- Prove2me | solution 1 for GittinsUCB.Patient.posterior_mean_law
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:54:03.559103+00:00
-- url     : https://prove2.me/submissions/5487bed4-ac76-4938-a860-d632384ebe46

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

namespace GittinsPMLAux

/-- Closed form of the posterior-mean recursion. -/
lemma postMean_closed (μ0 s : ℝ) (hs : 0 < s) (t : ℕ) (ω : Ω) :
    postMean μ0 1 s t ω = postVar 1 s t * (μ0 + (∑ i ∈ Finset.range t, R i ω) / s) := by
  induction t with
  | zero => simp [postMean, postVar]
  | succ n ih =>
    have hv : 0 < 1 / (1 : ℝ) + (n : ℝ) / s := by positivity
    have hv' : 0 < 1 / (1 : ℝ) + ((n + 1 : ℕ) : ℝ) / s := by positivity
    simp only [postMean, ih, Finset.sum_range_succ]
    simp only [postVar] at hv hv' ⊢
    field_simp
    push_cast
    ring

/-- The sum of the first `L` noises is `N(0, L σ²)`. -/
lemma law_sum (s : ℝ≥0) (L : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)).map
      (fun w : ℕ → ℝ => ∑ i ∈ Finset.range L, w i) = gaussianReal 0 ((L : ℝ≥0) * s) := by
  induction L with
  | zero =>
    simp [gaussianReal_zero_var]
  | succ n ih =>
    have hind : iIndepFun (fun (i : ℕ) (w : ℕ → ℝ) => w i)
        (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)) :=
      iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
    have h2 := hind.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i)
      (Finset.notMem_range_self (n := n))
    have hX : (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)).map (fun w : ℕ → ℝ => w n) =
        gaussianReal 0 s := Measure.infinitePi_map_eval _ n
    have hS : (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)).map
        (∑ i ∈ Finset.range n, fun (w : ℕ → ℝ) => w i) = gaussianReal 0 ((n : ℝ≥0) * s) := by
      rw [← ih]; congr 1; funext w; simp
    have := gaussianReal_add_gaussianReal_of_indepFun h2 hS hX
    have e : (∑ i ∈ Finset.range n, fun (w : ℕ → ℝ) => w i) + (fun w : ℕ → ℝ => w n) =
        fun w : ℕ → ℝ => ∑ i ∈ Finset.range (n + 1), w i := by
      funext w; simp [Finset.sum_range_succ]
    rw [e] at this
    rw [this]
    congr 1
    · simp
    · push_cast; ring

end GittinsPMLAux

open GittinsPMLAux in
theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2)
    (L : ℕ) (μ0 : ℝ) :
    (model μ0 1 σW2).map (postMean μ0 1 (σW2 : ℝ) L) =
      gaussianReal μ0 (1 - postVar 1 (σW2 : ℝ) L).toNNReal := by
  set s : ℝ := (σW2 : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast hW
  set k : ℝ := (L : ℝ) / s with hk
  have hk0 : 0 ≤ k := by positivity
  set v : ℝ := postVar 1 s L with hv
  have hvk : v = 1 / (1 + k) := by rw [hv, hk]; unfold postVar; simp
  have hv0 : 0 < v := by rw [hvk]; positivity
  set a : ℝ := v * k with ha
  set b : ℝ := v / s with hb
  set S : (ℕ → ℝ) → ℝ := fun w => ∑ i ∈ Finset.range L, w i with hSdef
  have hSm : Measurable S := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  -- pointwise closed form
  have hpt : postMean μ0 1 s L = fun ω : Ω => (a * ω.1 + b * S ω.2) + v * μ0 := by
    funext ω
    rw [postMean_closed μ0 s hs0 L ω]
    have hR : ∑ i ∈ Finset.range L, R i ω = (L : ℝ) * ω.1 + S ω.2 := by
      simp [R, hSdef, Finset.sum_add_distrib]
    rw [hR, ha, hb, hk]
    field_simp
    ring
  -- laws of the two independent pieces
  set P := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σW2) with hP
  have hmodel : model μ0 1 σW2 = (gaussianReal μ0 1).prod P := rfl
  have hind : IndepFun (fun ω : Ω => a * ω.1) (fun ω : Ω => b * S ω.2) (model μ0 1 σW2) := by
    rw [hmodel]
    exact indepFun_prod (X := fun x : ℝ => a * x) (Y := fun w => b * S w)
      (measurable_const_mul a) ((measurable_const_mul b).comp hSm)
  have hX : (model μ0 1 σW2).map (fun ω : Ω => a * ω.1) =
      (gaussianReal μ0 1).map (fun x => a * x) := by
    rw [hmodel, show (fun ω : Ω => a * ω.1) = (fun x => a * x) ∘ Prod.fst from rfl,
      ← Measure.map_map (measurable_const_mul a) measurable_fst,
      Measure.map_fst_prod]
    simp
  rw [gaussianReal_map_const_mul] at hX
  have hY : (model μ0 1 σW2).map (fun ω : Ω => b * S ω.2) =
      (gaussianReal 0 ((L : ℝ≥0) * σW2)).map (fun x => b * x) := by
    rw [hmodel, ← law_sum σW2 L, Measure.map_map (measurable_const_mul b) hSm,
      show (fun ω : Ω => b * S ω.2) = ((fun x => b * x) ∘ S) ∘ Prod.snd from rfl,
      ← Measure.map_map ((measurable_const_mul b).comp hSm) measurable_snd,
      Measure.map_snd_prod]
    simp [hP]
  rw [gaussianReal_map_const_mul] at hY
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hX hY
  have hmeas_sum : Measurable ((fun ω : Ω => a * ω.1) + fun ω : Ω => b * S ω.2) :=
    ((measurable_const_mul a).comp measurable_fst).add
      (((measurable_const_mul b).comp hSm).comp measurable_snd)
  rw [hpt]
  have e : (fun ω : Ω => (a * ω.1 + b * S ω.2) + v * μ0) =
      (fun x => x + v * μ0) ∘ ((fun ω : Ω => a * ω.1) + fun ω : Ω => b * S ω.2) := by
    funext ω; simp
  rw [e, ← Measure.map_map (measurable_add_const _) hmeas_sum, hsum,
    gaussianReal_map_add_const]
  congr 1
  · rw [ha, hvk]; field_simp; ring
  · apply NNReal.eq
    rw [Real.coe_toNNReal _ (by rw [hvk]; rw [sub_nonneg, div_le_one (by positivity)]; linarith)]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_natCast]
    rw [ha, hb, hvk]
    have hk' : (L : ℝ) = k * s := by rw [hk]; field_simp
    rw [hk']
    field_simp
    ring
