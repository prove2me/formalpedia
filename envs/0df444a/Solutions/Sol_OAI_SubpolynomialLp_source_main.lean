-- Prove2me | solution 1 for OAI.SubpolynomialLp.source_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:35:15.740099+00:00
-- url     : https://prove2.me/submissions/13e397c4-30e4-4c92-a78c-be5dd4734a32

import Mathlib
import Definitions.Def_SubpolynomialLp

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

universe u uE uI uΩ uV uι uJ uA uH uX uε uF

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace SubpolynomialLp

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace SubpolynomialLp

lemma independent_of_affine_sum {E : Type uE} {I : Type uI} [Fintype E] (z : I → E → ℝ)
    (hz : AffineIndependent ℝ z) (hs : ∀ i, ∑ e, z i e = 1) :
    LinearIndependent ℝ z := by
  classical
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hsum := congrArg (fun v : E → ℝ => ∑ e, v e) hw
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.sum_const_zero] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, hs, mul_one] at hsum
  exact hz.eq_zero_of_sum_eq_zero hsum hw i hi

lemma hyperplane_convex_representation {E : Type uE} [Fintype E] {K : Set (E → ℝ)}
    (hK : ∀ z ∈ K, ∑ e, z e = 1) {v : E → ℝ} (hv : v ∈ convexHull ℝ K) :
    ∃ k ≤ Fintype.card E, ∃ (z : Fin k → E → ℝ) (w : Fin k → ℝ),
      (∀ i, z i ∈ K) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = v := by
  classical
  obtain ⟨I, hI, z, w, hz, hi, hw, hws, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hv
  let e := (Fintype.equivFin I).symm
  have hlin := independent_of_affine_sum z hi (fun i => hK _ (hz ⟨i,rfl⟩))
  have hc : Fintype.card I ≤ Fintype.card E := by
    simpa using hlin.fintype_card_le_finrank
  refine ⟨Fintype.card I, hc, z ∘ e, w ∘ e, ?_, ?_, ?_, ?_⟩
  · intro i; exact hz ⟨e i, rfl⟩
  · intro i; exact (hw (e i)).le
  · exact (e.sum_comp w).trans hws
  · exact (e.sum_comp (fun i => w i • z i)).trans hsum

lemma compact_convexHull_hyperplane {E : Type uE} [Fintype E] {K : Set (E → ℝ)}
    (hKc : IsCompact K) (hK : ∀ z ∈ K, ∑ e, z e = 1) :
    IsCompact (convexHull ℝ K) := by
  classical
  let A (k : ℕ) : Set ((Fin k → E → ℝ) × (Fin k → ℝ)) :=
    (Set.pi Set.univ (fun _ => K)) ×ˢ {weights | (∀ i, 0 ≤ weights i) ∧ ∑ i, weights i = 1}
  let f (k : ℕ) (a : (Fin k → E → ℝ) × (Fin k → ℝ)) := ∑ i, a.2 i • a.1 i
  have hAc (k : ℕ) : IsCompact (A k) := by
    have hs : IsCompact {weights : Fin k → ℝ |
        (∀ i, 0 ≤ weights i) ∧ ∑ i, weights i = 1} := by
      exact isCompact_stdSimplex ℝ (Fin k)
    simpa [A, Set.pi] using (isCompact_pi_infinite (fun _ : Fin k => hKc)).prod
      hs
  have hf (k : ℕ) : Continuous (f k) := by unfold f; fun_prop
  have he : convexHull ℝ K = ⋃ k ∈ Finset.range (Fintype.card E+1), (f k) '' (A k) := by
    ext v
    constructor
    · intro hv
      obtain ⟨k,hk,z,w,hz,hw,hws,hv⟩ := hyperplane_convex_representation hK hv
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      exact ⟨(z,w), ⟨by simpa using hz, hw,hws⟩, hv⟩
    · intro hv
      obtain ⟨k,hk,a,ha,rfl⟩ := Set.mem_iUnion.mp hv |>.imp (fun k => Set.mem_iUnion.mp)
      exact (convex_convexHull ℝ K).sum_mem (fun i _ => ha.2.1 i) ha.2.2
        (fun i _ => subset_convexHull ℝ K (ha.1 i (Set.mem_univ i)))
  rw [he]
  exact Finset.isCompact_biUnion _ (fun k _ => (hAc k).image (hf k))

lemma normalized_integral_mem {E : Type uE} {Ω : Type uΩ} [Fintype E] [MeasurableSpace Ω]
    (μ : Measure Ω) {K : Set (E → ℝ)} (hKc : IsCompact K)
    (hK : ∀ z ∈ K, ∑ e, z e = 1) (q : Ω → E → ℝ) (hqi : Integrable q μ)
    (hq : ∀ᵐ t ∂μ, q t = 0 ∨ (0 < ∑ e, q t e ∧ (∑ e, q t e)⁻¹ • q t ∈ K))
    (hS : 0 < ∫ t, ∑ e, q t e ∂μ) :
    (∫ t, ∑ e, q t e ∂μ)⁻¹ • (∫ t, q t ∂μ) ∈ convexHull ℝ K := by
  classical
  let S := ∫ t, ∑ e, q t e ∂μ
  have hsi : Integrable (fun t => ∑ e, q t e) μ :=
    integrable_finsetSum _ (fun e _ => (integrable_pi_iff.mp hqi) e)
  by_contra hn
  obtain ⟨f,a,hfa,haf⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ K)
    (compact_convexHull_hyperplane hKc hK).isClosed hn
  have hle : ∀ᵐ t ∂μ, f (q t) ≤ a * ∑ e, q t e := by
    filter_upwards [hq] with t ht
    rcases ht with ht | ⟨ht,hkt⟩
    · simp [ht]
    · have hh := (hfa _ (subset_convexHull ℝ K hkt)).le
      rw [map_smul, smul_eq_mul] at hh
      simpa only [mul_comm] using (inv_mul_le_iff₀ ht).mp hh
  have hi := integral_mono_ae (f.integrable_comp hqi) (hsi.const_mul a) hle
  rw [f.integral_comp_comm hqi, integral_const_mul] at hi
  rw [map_smul, smul_eq_mul] at haf
  have : S⁻¹ * f (∫ t, q t ∂μ) ≤ a := (inv_mul_le_iff₀ hS).mpr (by simpa only [mul_comm] using hi)
  exact (not_lt_of_ge this) haf

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Matrix

namespace SubpolynomialLp

lemma entropy_le_log_card {ι : Type uι} [Fintype ι] (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i) (hsum : ∑ i, μ i = 1) :
    ∑ i, μ i * Real.log (1 / μ i) ≤ Real.log (Fintype.card ι : ℝ) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := μ) (p := fun i => 1 / μ i)
    (fun i _ => (hμ i).le) hsum (fun i _ => show 0 < 1 / μ i from one_div_pos.mpr (hμ i))
  have hn : ∀ i, μ i ≠ 0 := fun i => (hμ i).ne'
  simpa [smul_eq_mul, hn] using h

lemma log_ratio_lower {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  let f : ℝ → ℝ := fun t => Real.log t - 2 * (t - 1) / (t + 1)
  have hd (t : ℝ) (ht : 1 ≤ t) :
      HasDerivAt f ((t - 1) ^ 2 / (t * (t + 1) ^ 2)) t := by
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t + 1 ≠ 0 := by linarith
    convert (Real.hasDerivAt_log ht0).sub
      ((((hasDerivAt_id t).sub_const 1).const_mul 2).div
        ((hasDerivAt_id t).add_const 1) ht1) using 1
    all_goals first | rfl | (simp only [id_eq]; field_simp; ring)
  have hm : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by simpa using (le_of_lt (show 1 < t from by
        simpa only [interior_Ici, Set.mem_Ioi] using ht)))).hasDerivWithinAt)
    intro t ht
    have ht' : 1 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    positivity
  have hh := hm (Set.mem_Ici.mpr le_rfl) hx hx
  dsimp [f] at hh
  norm_num at hh
  linarith

/-- The logarithmic-mean estimate in a division-free form, valid also at a=b. -/
lemma log_mean_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 ≤ (a - b) * (Real.log a - Real.log b) * ((a + b) / 2) := by
  wlog hab : b ≤ a generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    nlinarith
  have hx : 1 ≤ a / b := (le_div_iff₀ hb).mpr (by simpa using hab)
  have hh := log_ratio_lower hx
  rw [Real.log_div ha.ne' hb.ne'] at hh
  have he : 2 * (a / b - 1) / (a / b + 1) = 2 * (a - b) / (a + b) := by
    field_simp
  rw [he] at hh
  have habp : 0 < a + b := by positivity
  have hh' := (div_le_iff₀ habp).mp hh
  have := mul_le_mul_of_nonneg_left hh' (sub_nonneg.mpr hab)
  nlinarith


section ElectricalEnergy
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]

def electricalEnergy (src dst : E → V) (c : E → ℝ) (h : V → ℝ) : ℝ :=
  ∑ e, c e * (h (src e) - h (dst e)) *
    (Real.log (h (src e)) - Real.log (h (dst e)))

lemma sub_mul_log_sub_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (Real.log a - Real.log b) := by
  rcases le_total a b with hab | hab
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab)
      (sub_nonpos.mpr (Real.log_le_log ha hab))
  · exact mul_nonneg (sub_nonneg.mpr hab)
      (sub_nonneg.mpr (Real.log_le_log hb hab))

omit [Fintype V] in
lemma electricalEnergy_nonneg (src dst : E → V) (c : E → ℝ) (h : V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hh : ∀ i, 0 < h i) :
    0 ≤ electricalEnergy src dst c h := by
  apply Finset.sum_nonneg
  intro e _
  rw [mul_assoc]
  exact mul_nonneg (hc e) (sub_mul_log_sub_nonneg (hh _) (hh _))

omit [Fintype V] in
/-- The weighted Cauchy--Schwarz step, before mass normalization. -/
lemma electrical_cauchy_schwarz (src dst : E → V) (c w : E → ℝ) (h : V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hh : ∀ i, 0 < h i) :
    (∑ e, w e * Real.sqrt (c e) * |h (src e) - h (dst e)|) ^ 2 ≤
      electricalEnergy src dst c h *
        ∑ e, (w e) ^ 2 * ((h (src e) + h (dst e)) / 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro e _
    rw [mul_assoc]
    exact mul_nonneg (hc e) (sub_mul_log_sub_nonneg (hh _) (hh _))
  · intro e _
    exact mul_nonneg (sq_nonneg (w e))
      (div_nonneg (add_nonneg (hh _).le (hh _).le) (by norm_num))
  · intro e _
    have he := mul_le_mul_of_nonneg_left (log_mean_sq_le (hh (src e)) (hh (dst e)))
      (mul_nonneg (sq_nonneg (w e)) (hc e))
    calc
      (w e * Real.sqrt (c e) * |h (src e) - h (dst e)|) ^ 2 =
          ((w e) ^ 2 * c e) * (h (src e) - h (dst e)) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt (hc e), sq_abs]
      _ ≤ ((w e) ^ 2 * c e) *
          ((h (src e) - h (dst e)) *
            (Real.log (h (src e)) - Real.log (h (dst e))) *
              ((h (src e) + h (dst e)) / 2)) := he
      _ = _ := by ring

variable [DecidableEq V]

def vertexWeight (src dst : E → V) (w : E → ℝ) (i : V) : ℝ :=
  (∑ e, if src e = i then (w e) ^ 2 else 0) +
  (∑ e, if dst e = i then (w e) ^ 2 else 0)

def vertexMass (src dst : E → V) (w : E → ℝ) (i : V) : ℝ :=
  vertexWeight src dst w i / (2 * ∑ e, (w e) ^ 2)

lemma vertexWeight_pairing (src dst : E → V) (w : E → ℝ) (h : V → ℝ) :
    ∑ i, vertexWeight src dst w i * h i =
      ∑ e, (w e) ^ 2 * (h (src e) + h (dst e)) := by
  simp only [vertexWeight, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  calc
    _ = (∑ e, (w e) ^ 2 * h (src e)) + ∑ e, (w e) ^ 2 * h (dst e) := by
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        simp [ite_mul]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        simp [ite_mul]
    _ = _ := by simp [mul_add, Finset.sum_add_distrib]

lemma vertexMass_pairing (src dst : E → V) (w : E → ℝ) (h : V → ℝ) :
    ∑ i, vertexMass src dst w i * h i =
      (∑ e, (w e) ^ 2 * (h (src e) + h (dst e))) / (2 * ∑ e, (w e) ^ 2) := by
  simp only [vertexMass, div_mul_eq_mul_div, ← Finset.sum_div, vertexWeight_pairing]

lemma vertexMass_sum (src dst : E → V) (w : E → ℝ)
    (hw : 0 < ∑ e, (w e) ^ 2) :
    ∑ i, vertexMass src dst w i = 1 := by
  have h := vertexMass_pairing src dst w (fun _ => 1)
  simp only [mul_one, one_add_one_eq_two, ← Finset.sum_mul] at h
  rw [h, mul_comm (∑ e, (w e) ^ 2) 2]
  exact div_self (mul_ne_zero (by norm_num) hw.ne')

/-- The precise normalized energy inequality used in the heat-entropy proof. -/
lemma heat_cauchy_schwarz (src dst : E → V) (c w : E → ℝ) (h : V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hh : ∀ i, 0 < h i)
    (hw : 0 < ∑ e, (w e) ^ 2)
    (hmass : ∑ i, vertexMass src dst w i * h i = 1) :
    (∑ e, w e * Real.sqrt (c e) * |h (src e) - h (dst e)|) ^ 2 ≤
      electricalEnergy src dst c h * (∑ e, (w e) ^ 2) := by
  have hm := vertexMass_pairing src dst w h
  rw [hmass] at hm
  have hm' := (eq_div_iff (show 2 * ∑ e, (w e) ^ 2 ≠ 0 by positivity)).mp hm
  have hsum : ∑ e, (w e) ^ 2 * ((h (src e) + h (dst e)) / 2) =
      ∑ e, (w e) ^ 2 := by
    simp only [← mul_div_assoc, ← Finset.sum_div]
    rw [← hm']
    ring
  simpa only [hsum] using electrical_cauchy_schwarz src dst c w h hc hh

def graphLaplacian (src dst : E → V) (c : E → ℝ) (h : V → ℝ) (i : V) : ℝ :=
  (∑ e, if src e = i then c e * (h (src e) - h (dst e)) else 0) -
  (∑ e, if dst e = i then c e * (h (src e) - h (dst e)) else 0)

lemma graphLaplacian_pairing (src dst : E → V) (c : E → ℝ) (h g : V → ℝ) :
    ∑ i, graphLaplacian src dst c h i * g i =
      ∑ e, c e * (h (src e) - h (dst e)) * (g (src e) - g (dst e)) := by
  calc
    _ = (∑ e, c e * (h (src e) - h (dst e)) * g (src e)) -
        ∑ e, c e * (h (src e) - h (dst e)) * g (dst e) := by
      simp only [graphLaplacian, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      congr 1 <;> rw [Finset.sum_comm] <;>
        apply Finset.sum_congr rfl <;> intro e _ <;> simp [ite_mul]
    _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]

lemma graphLaplacian_sum (src dst : E → V) (c : E → ℝ) (h : V → ℝ) :
    ∑ i, graphLaplacian src dst c h i = 0 := by
  simpa using graphLaplacian_pairing src dst c h (fun _ => 1)

def heatEntropy (μ : V → ℝ) (h : V → ℝ) : ℝ :=
  ∑ i, μ i * (h i * Real.log (h i))

/-- Entropy dissipation, from the actual weighted graph heat equation. -/
lemma heatEntropy_hasDerivAt (src dst : E → V) (c : E → ℝ) (μ : V → ℝ)
    (h : ℝ → V → ℝ) (s : ℝ) (hμ : ∀ i, 0 < μ i) (hp : ∀ i, 0 < h s i)
    (hd : ∀ i, HasDerivAt (fun t => h t i)
      (-graphLaplacian src dst c (h s) i / μ i) s) :
    HasDerivAt (fun t => heatEntropy μ (h t))
      (-electricalEnergy src dst c (h s)) s := by
  have hh (i : V) := ((hd i).mul ((hd i).log (hp i).ne')).const_mul (μ i)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hh i)
  have he : (∑ i, μ i *
      ((-graphLaplacian src dst c (h s) i / μ i) * Real.log (h s i) +
      h s i * ((-graphLaplacian src dst c (h s) i / μ i) / h s i))) =
      -electricalEnergy src dst c (h s) := by
    calc
      _ = ∑ i, -graphLaplacian src dst c (h s) i * (Real.log (h s i) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(hμ i).ne', (hp i).ne']
        ring
      _ = -∑ i, graphLaplacian src dst c (h s) i * (Real.log (h s i) + 1) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
      _ = _ := by
        rw [graphLaplacian_pairing]
        simp only [add_sub_add_right_eq_sub, electricalEnergy]
  rw [he] at hs
  exact hs

omit [DecidableEq V] in
lemma heatEntropy_continuous (μ : V → ℝ) : Continuous (heatEntropy μ) := by
  unfold heatEntropy
  fun_prop

/-- The entropy identity for the weighted graph heat flow, including the singular
initial point mass. Positivity is only required at strictly positive times. -/
lemma heatEntropy_integral (src dst : E → V) (c : E → ℝ) (μ : V → ℝ)
    (h : ℝ → V → ℝ) (v : V) (hc : ∀ e, 0 ≤ c e) (hμ : ∀ i, 0 < μ i)
    (hcont : Continuous h) (hp : ∀ s : ℝ, 0 < s → ∀ i, 0 < h s i)
    (hd : ∀ s : ℝ, 0 < s → ∀ i, HasDerivAt (fun t => h t i)
      (-graphLaplacian src dst c (h s) i / μ i) s)
    (hzero : h 0 = Pi.single v (1 / μ v))
    (htop : Tendsto h atTop (𝓝 (fun _ => 1))) :
    IntegrableOn (fun s => electricalEnergy src dst c (h s)) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), electricalEnergy src dst c (h s)) = Real.log (1 / μ v) := by
  have hecont : Continuous (fun s => -heatEntropy μ (h s)) :=
    ((heatEntropy_continuous μ).comp hcont).neg
  have hederiv (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      HasDerivAt (fun t => -heatEntropy μ (h t))
        (electricalEnergy src dst c (h s)) s := by
    convert (heatEntropy_hasDerivAt src dst c μ h s hμ
      (hp s hs) (hd s hs)).neg using 1 <;> first | rfl | simp only [neg_neg]
  have henonneg (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      0 ≤ electricalEnergy src dst c (h s) :=
    electricalEnergy_nonneg src dst c (h s) hc (hp s hs)
  have hetop : Tendsto (fun s => -heatEntropy μ (h s)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (((heatEntropy_continuous μ).tendsto (fun _ => 1)).comp htop).neg
    simpa [heatEntropy] using hh
  have hezero : heatEntropy μ (h 0) = Real.log (1 / μ v) := by
    rw [hzero, heatEntropy]
    simp only [Pi.single_apply]
    rw [Finset.sum_eq_single v]
    · simp [(hμ v).ne']
    · intro i _ hiv
      simp [hiv]
    · simp
  constructor
  · exact integrableOn_Ioi_deriv_of_nonneg hecont.continuousWithinAt hederiv henonneg hetop
  · have hi := integral_Ioi_of_hasDerivAt_of_nonneg hecont.continuousWithinAt
      hederiv henonneg hetop
    simpa [hezero] using hi

variable [DecidableEq E]

def incidence (src dst : E → V) : Matrix E V ℝ :=
  fun e i => (if src e = i then 1 else 0) - (if dst e = i then 1 else 0)

def laplacianMatrix (src dst : E → V) (c : E → ℝ) : Matrix V V ℝ :=
  (incidence src dst).transpose * Matrix.diagonal c * incidence src dst

omit [Fintype E] [DecidableEq E] in
lemma incidence_mulVec (src dst : E → V) (h : V → ℝ) (e : E) :
    (incidence src dst *ᵥ h) e = h (src e) - h (dst e) := by
  simp [Matrix.mulVec, dotProduct, incidence, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma laplacianMatrix_mulVec (src dst : E → V) (c : E → ℝ) (h : V → ℝ) :
    laplacianMatrix src dst c *ᵥ h = graphLaplacian src dst c h := by
  classical
  unfold laplacianMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext i
  change (∑ e, incidence src dst e i * (Matrix.diagonal c *ᵥ (incidence src dst *ᵥ h)) e) = _
  simp only [Matrix.mulVec_diagonal, incidence_mulVec]
  simp only [incidence, sub_mul, Finset.sum_sub_distrib, graphLaplacian]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _ <;> split_ifs <;> simp_all

omit [Fintype V] in
lemma laplacianMatrix_symmetric (src dst : E → V) (c : E → ℝ) :
    (laplacianMatrix src dst c).IsSymm := by
  unfold Matrix.IsSymm laplacianMatrix
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma laplacianMatrix_posSemidef (src dst : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) : (laplacianMatrix src dst c).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (laplacianMatrix_symmetric src dst c), ?_⟩
  intro h
  rw [laplacianMatrix_mulVec]
  have hp := graphLaplacian_pairing src dst c h h
  change 0 ≤ ∑ i, h i * graphLaplacian src dst c h i
  simp only [mul_comm (h _)]
  rw [hp]
  apply Finset.sum_nonneg
  intro e _
  simpa only [sq, mul_assoc] using mul_nonneg (hc e) (sq_nonneg (h (src e) - h (dst e)))

omit [Fintype V] in
lemma laplacianMatrix_apply (src dst : E → V) (c : E → ℝ) (i j : V) :
    laplacianMatrix src dst c i j =
      ∑ e, c e * incidence src dst e i * incidence src dst e j := by
  classical
  unfold laplacianMatrix
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro e _
  ring


omit [Fintype V] in
lemma laplacianMatrix_offdiag_neg (src dst : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) {i j : V} (hij : i ≠ j)
    (hconn : ∃ e, (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    laplacianMatrix src dst c i j < 0 := by
  rw [laplacianMatrix_apply]
  have hnon (e : E) : c e * incidence src dst e i * incidence src dst e j ≤ 0 := by
    have := (hc e).le
    dsimp [incidence]
    split_ifs <;> simp_all
  obtain ⟨e, he⟩ := hconn
  have hneg : c e * incidence src dst e i * incidence src dst e j < 0 := by
    rcases he with ⟨hi, hj⟩ | ⟨hj, hi⟩ <;>
      simp [incidence, hi, hj, hij, hij.symm, (hc e)]
  have hs := Finset.sum_lt_sum (fun e _ => hnon e) ⟨e, Finset.mem_univ e, hneg⟩
  simpa using hs

omit [DecidableEq E] in
lemma graphLaplacian_kernel_constant (src dst : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 < c e)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (h : V → ℝ) (hzero : graphLaplacian src dst c h = 0) (i j : V) : h i = h j := by
  have he : ∑ e, c e * (h (src e) - h (dst e)) ^ 2 = 0 := by
    have hh := graphLaplacian_pairing src dst c h h
    rw [hzero] at hh
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sq, mul_assoc] using hh.symm
  have hn (e : E) : 0 ≤ c e * (h (src e) - h (dst e)) ^ 2 :=
    mul_nonneg (hc e).le (sq_nonneg _)
  have hz (e : E) : h (src e) = h (dst e) := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hn e)).mp he e (Finset.mem_univ e)
    have hs := (mul_eq_zero.mp hz).resolve_left (hc e).ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  by_cases hij : i = j
  · simp [hij]
  · obtain ⟨e, he⟩ := hconn i j hij
    rcases he with ⟨hi, hj⟩ | ⟨hj, hi⟩
    · simpa [hi, hj] using hz e
    · simpa [hi, hj] using (hz e).symm

end ElectricalEnergy

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator

namespace SubpolynomialLp

open scoped Matrix.Norms.Operator
open Matrix NormedSpace
section PositiveExponential
variable {V : Type uV} [Fintype V] [DecidableEq V]
lemma matrix_pow_nonneg (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∀ k : ℕ, ∀ i j, 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k hk =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (hk i l) (hA l j))

omit [Fintype V] [DecidableEq V] in
lemma matrix_tsum_apply (f : ℕ → Matrix V V ℝ) (hf : Summable f) (i j : V) :
    (∑' k, f k) i j = ∑' k, f k i j :=
  ((Pi.hasSum.mp (Pi.hasSum.mp hf.hasSum i)) j).tsum_eq.symm


lemma matrix_exp_pos (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (i j : V) (hij : 0 < A i j) : 0 < exp A i j := by
  have hs := expSeries_summable' (𝕂 := ℝ) A
  have hsi := (Pi.summable.mp hs) i
  have hsij := (Pi.summable.mp hsi) j
  have he : exp A = ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • A ^ k :=
    congrFun (exp_eq_tsum ℝ) A
  rw [he]
  rw [matrix_tsum_apply _ hs i j]
  apply hsij.tsum_pos
    (fun k => mul_nonneg (by positivity) (matrix_pow_nonneg A hA k i j)) 1
  simpa using hij

lemma matrix_exp_scalar (t : ℝ) :
    exp (t • (1 : Matrix V V ℝ)) = Real.exp t • (1 : Matrix V V ℝ) := by
  convert (algebraMap_exp_comm (𝔸 := Matrix V V ℝ) t).symm using 1
  all_goals simp only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]
  all_goals rfl

lemma matrix_exp_add_scalar (A : Matrix V V ℝ) (r : ℝ) :
    exp (A + r • 1) = Real.exp r • exp A := by
  rw [Matrix.exp_add_of_commute A (r • 1) ((Commute.one_right A).smul_right r),
    matrix_exp_scalar, Matrix.mul_smul, Matrix.mul_one]

lemma matrix_exp_pos_of_offdiag (A : Matrix V V ℝ)
    (hA : ∀ i j, i ≠ j → 0 < A i j) (i j : V) : 0 < exp A i j := by
  let r : ℝ := 1 + ∑ i, |A i i|
  have hd (i : V) : 0 < A i i + r := by
    have hb := Finset.single_le_sum (f := fun k => |A k k|)
      (fun k _ => abs_nonneg (A k k)) (Finset.mem_univ i)
    have := neg_abs_le (A i i)
    dsimp [r]
    linarith
  have hp (i j : V) : 0 < (A + r • 1) i j := by
    by_cases hij : i = j
    · subst j
      simpa using hd i
    · simpa [Matrix.one_apply, hij] using hA i j hij
  have hp' := matrix_exp_pos (A + r • 1) (fun i j => (hp i j).le) i j (hp i j)
  rw [matrix_exp_add_scalar] at hp'
  exact (mul_pos_iff_of_pos_left (Real.exp_pos r)).mp hp'

end PositiveExponential

section MatrixSpectral
variable {V : Type uV} [Fintype V] [DecidableEq V]

lemma matrix_exp_conj_unitary (U : Matrix.unitaryGroup V ℝ) (A : Matrix V V ℝ) :
    exp ((U : Matrix V V ℝ) * A * star (U : Matrix V V ℝ)) =
      (U : Matrix V V ℝ) * exp A * star (U : Matrix V V ℝ) := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
  have hc : Continuous φ := φ.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp φ.toAlgEquiv.toAlgHom hc A).symm

lemma matrix_exp_spectral (S : Matrix V V ℝ) (hS : S.IsHermitian) (t : ℝ) :
    exp (t • S) = (hS.eigenvectorUnitary : Matrix V V ℝ) *
      Matrix.diagonal (fun k => Real.exp (t * hS.eigenvalues k)) *
        star (hS.eigenvectorUnitary : Matrix V V ℝ) := by
  conv_lhs => rw [hS.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, matrix_exp_conj_unitary,
    ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 2
  ext i
  simp [Pi.exp_def, Real.exp_eq_exp_ℝ]


def spectralKernelProjection (S : Matrix V V ℝ) (hS : S.IsHermitian) : Matrix V V ℝ :=
  Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hS.eigenvectorUnitary
    (Matrix.diagonal (fun k => if hS.eigenvalues k = 0 then 1 else 0))

lemma matrix_exp_neg_tendsto (S : Matrix V V ℝ) (hS : S.PosSemidef) :
    Tendsto (fun t : ℝ => exp (-t • S)) atTop (𝓝 (spectralKernelProjection S hS.1)) := by
  have he (k : V) : Tendsto (fun t : ℝ => Real.exp (-t * hS.1.eigenvalues k))
      atTop (𝓝 (if hS.1.eigenvalues k = 0 then 1 else 0)) := by
    by_cases hk : hS.1.eigenvalues k = 0
    · simp only [hk, mul_zero, Real.exp_zero, ite_true]
      exact tendsto_const_nhds
    · simp only [hk, ite_false]
      have hp := lt_of_le_of_ne (hS.eigenvalues_nonneg k) (Ne.symm hk)
      simpa only [id_eq, neg_mul, Function.comp_def] using Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hp))
  have hd : Tendsto (fun t : ℝ => Matrix.diagonal (fun k => Real.exp (-t * hS.1.eigenvalues k)))
      atTop (𝓝 (Matrix.diagonal (fun k => if hS.1.eigenvalues k = 0 then 1 else 0))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using he i
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact tendsto_const_nhds
  simpa only [matrix_exp_spectral S hS.1, spectralKernelProjection, Unitary.conjStarAlgAut_apply]
    using (hd.const_mul (hS.1.eigenvectorUnitary : Matrix V V ℝ)).mul_const
      (star (hS.1.eigenvectorUnitary : Matrix V V ℝ))

lemma mul_spectralKernelProjection (S : Matrix V V ℝ) (hS : S.IsHermitian) :
    S * spectralKernelProjection S hS = 0 := by
  unfold spectralKernelProjection
  conv_lhs => lhs; rw [hS.spectral_theorem]
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  have hz : (fun k => (RCLike.ofReal ∘ hS.eigenvalues) k *
      (if hS.eigenvalues k = 0 then 1 else 0)) = (0 : V → ℝ) := by
    funext k
    by_cases hk : hS.eigenvalues k = 0 <;> simp [hk]
  rw [hz]
  simp

end MatrixSpectral

section WeightedHeat
variable {V : Type uV} [Fintype V] [DecidableEq V]

def weightedGenerator (L : Matrix V V ℝ) (d : V → ℝ) :=
  diagonal (fun i => d i * d i) * L

def symmetricGenerator (L : Matrix V V ℝ) (d : V → ℝ) :=
  diagonal d * L * diagonal d

def weightedHeatKernel (L : Matrix V V ℝ) (d : V → ℝ) (t : ℝ) : Matrix V V ℝ :=
  diagonal d * exp (-t • symmetricGenerator L d) * diagonal d

lemma weightedHeatKernel_generator (L : Matrix V V ℝ) (d : V → ℝ) (t : ℝ) :
    weightedHeatKernel L d t =
      exp (-t • weightedGenerator L d) * diagonal (fun i => d i * d i) := by
  have hs : SemiconjBy (diagonal d) (symmetricGenerator L d) (weightedGenerator L d) := by
    dsimp [SemiconjBy, symmetricGenerator, weightedGenerator]
    rw [← diagonal_mul_diagonal]
    simp only [Matrix.mul_assoc]
  have he := (hs.smul_right (-t)).exp_right
  change diagonal d * exp (-t • symmetricGenerator L d) =
    exp (-t • weightedGenerator L d) * diagonal d at he
  unfold weightedHeatKernel
  rw [he, Matrix.mul_assoc, diagonal_mul_diagonal]

lemma weightedHeatKernel_zero (L : Matrix V V ℝ) (d : V → ℝ) :
    weightedHeatKernel L d 0 = diagonal (fun i => d i * d i) := by
  simp [weightedHeatKernel, diagonal_mul_diagonal]

lemma weightedHeatKernel_hasDerivAt (L : Matrix V V ℝ) (d : V → ℝ) (t : ℝ) :
    HasDerivAt (weightedHeatKernel L d)
      (-weightedGenerator L d * weightedHeatKernel L d t) t := by
  have hh := (hasDerivAt_exp_smul_const' (-weightedGenerator L d) t).mul_const
    (diagonal (fun i => d i * d i))
  convert hh using 1
  all_goals first
    | rfl
    | (simp only [weightedHeatKernel_generator, smul_neg, neg_smul, Matrix.mul_assoc]; rfl)
    | (funext s; simp only [weightedHeatKernel_generator, smul_neg, neg_smul]; rfl)

lemma weightedHeatKernel_continuous (L : Matrix V V ℝ) (d : V → ℝ) :
    Continuous (weightedHeatKernel L d) :=
  continuous_iff_continuousAt.mpr (fun t => (weightedHeatKernel_hasDerivAt L d t).continuousAt)

lemma symmetricGenerator_symmetric (L : Matrix V V ℝ) (hL : L.IsSymm) (d : V → ℝ) :
    (symmetricGenerator L d).IsSymm := by
  unfold symmetricGenerator Matrix.IsSymm
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, hL.eq, Matrix.mul_assoc]

lemma weightedHeatKernel_symmetric (L : Matrix V V ℝ) (hL : L.IsSymm) (d : V → ℝ) (t : ℝ) :
    (weightedHeatKernel L d t).IsSymm := by
  unfold weightedHeatKernel Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    ← Matrix.exp_transpose, Matrix.transpose_smul, (symmetricGenerator_symmetric L hL d).eq]
  simp only [Matrix.mul_assoc]

lemma weightedHeatKernel_semigroup (L : Matrix V V ℝ) (d μ : V → ℝ)
    (hdμ : ∀ i, d i * μ i * d i = 1) (s t : ℝ) :
    weightedHeatKernel L d (s+t) =
      weightedHeatKernel L d s * diagonal μ * weightedHeatKernel L d t := by
  have he : diagonal d * diagonal μ * diagonal d = (1 : Matrix V V ℝ) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    ext i j
    simp only [diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have hexp : exp (-(s+t) • symmetricGenerator L d) =
      exp (-s • symmetricGenerator L d) * exp (-t • symmetricGenerator L d) := by
    rw [neg_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl (symmetricGenerator L d)).smul_left (-s)).smul_right (-t))
  unfold weightedHeatKernel
  rw [hexp]
  calc
    _ = diagonal d * exp (-s • symmetricGenerator L d) *
        (diagonal d * diagonal μ * diagonal d) * exp (-t • symmetricGenerator L d) * diagonal d := by
      rw [he]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma symmetricGenerator_posSemidef (L : Matrix V V ℝ) (hL : L.PosSemidef) (d : V → ℝ) :
    (symmetricGenerator L d).PosSemidef := by
  simpa only [symmetricGenerator, Matrix.diagonal_conjTranspose, star_trivial] using
    hL.conjTranspose_mul_mul_same (diagonal d)

lemma weightedHeatKernel_entry_hasDerivAt (L : Matrix V V ℝ) (d : V → ℝ)
    (t : ℝ) (i v : V) :
    HasDerivAt (fun s => weightedHeatKernel L d s i v)
      (-(d i * d i) * (L *ᵥ fun j => weightedHeatKernel L d t j v) i) t := by
  have hh := hasDerivAt_pi.mp (hasDerivAt_pi.mp (weightedHeatKernel_hasDerivAt L d t) i) v
  convert hh using 1 <;> first
    | rfl
    | (simp only [weightedGenerator, neg_mul, Matrix.mul_assoc]
       rw [Matrix.neg_apply, Matrix.diagonal_mul]
       rfl)


lemma weightedHeatKernel_pos (L : Matrix V V ℝ) (d : V → ℝ)
    (hd : ∀ i, 0 < d i) (hL : ∀ i j, i ≠ j → L i j < 0)
    (t : ℝ) (ht : 0 < t) (i j : V) : 0 < weightedHeatKernel L d t i j := by
  rw [weightedHeatKernel_generator, Matrix.mul_diagonal]
  apply mul_pos _ (mul_pos (hd j) (hd j))
  apply matrix_exp_pos_of_offdiag
  intro a b hab
  change 0 < -t * (weightedGenerator L d a b)
  rw [weightedGenerator, Matrix.diagonal_mul]
  exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr ht)
    (mul_neg_of_pos_of_neg (mul_pos (hd a) (hd a)) (hL a b hab))

lemma weightedHeatKernel_tendsto (L : Matrix V V ℝ) (hL : L.PosSemidef) (d : V → ℝ) :
    Tendsto (weightedHeatKernel L d) atTop
      (𝓝 (diagonal d * spectralKernelProjection (symmetricGenerator L d)
        (symmetricGenerator_posSemidef L hL d).1 * diagonal d)) := by
  exact ((matrix_exp_neg_tendsto _ (symmetricGenerator_posSemidef L hL d)).const_mul
    (diagonal d)).mul_const (diagonal d)

lemma weightedHeatKernel_limit_ker (L : Matrix V V ℝ) (hL : L.IsHermitian) (d : V → ℝ)
    (hd : ∀ i, d i ≠ 0) :
    L * (diagonal d * spectralKernelProjection (symmetricGenerator L d)
      (Matrix.isHermitian_iff_isSymm.mpr (symmetricGenerator_symmetric L
        (Matrix.isHermitian_iff_isSymm.mp hL) d)) * diagonal d) = 0 := by
  let hS : (symmetricGenerator L d).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (symmetricGenerator_symmetric L
      (Matrix.isHermitian_iff_isSymm.mp hL) d)
  let Z := spectralKernelProjection (symmetricGenerator L d) hS
  change L * (diagonal d * Z * diagonal d) = 0
  have hz : diagonal d * (L * (diagonal d * Z * diagonal d)) = 0 := by
    calc
      _ = symmetricGenerator L d * Z * diagonal d := by
        simp only [symmetricGenerator, Matrix.mul_assoc]
      _ = 0 := by rw [mul_spectralKernelProjection, Matrix.zero_mul]
  ext i j
  have hh := congrFun₂ hz i j
  rw [Matrix.diagonal_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (hd i)

end WeightedHeat

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator

namespace SubpolynomialLp

section ProjectionIntegral
variable {V : Type uV} [Fintype V] [DecidableEq V]

lemma exponential_sum_integral {I : Type uI} [Fintype I] (a b : I → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, a k = 0 → b k = 0) :
    IntegrableOn (fun t : ℝ => ∑ k, b k * Real.exp (-t * a k)) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), ∑ k, b k * Real.exp (-t * a k)) = ∑ k, b k / a k := by
  have hi (k : I) : IntegrableOn (fun t : ℝ => b k * Real.exp (-t * a k)) (Set.Ioi 0) := by
    by_cases hz : a k = 0
    · simp [hb k hz]
    · have hp : 0 < a k := lt_of_le_of_ne (ha k) (Ne.symm hz)
      have hh := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hp) 0).const_mul (b k)
      have he : (fun t : ℝ => b k * Real.exp (-t * a k)) =
          (fun t : ℝ => b k * Real.exp (-a k * t)) := by
        funext t; congr 2; ring
      rw [he]
      exact hh
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hz : a k = 0
  · simp [hz, hb k hz]
  · have hp : 0 < a k := lt_of_le_of_ne (ha k) (Ne.symm hz)
    rw [integral_const_mul]
    have hh := integral_exp_mul_Ioi (neg_neg_of_pos hp) 0
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hh
    have hexp : (fun t : ℝ => Real.exp (-t * a k)) =
        (fun t : ℝ => Real.exp (-a k * t)) := by funext t; congr 1; ring
    rw [hexp, hh]
    simp [div_eq_mul_inv]

section GramProjection
variable {E : Type uE} [Fintype E]

omit [DecidableEq V] in
theorem gramHermitian (A : Matrix E V ℝ) : (A.conjTranspose * A).IsHermitian :=
  (Matrix.posSemidef_conjTranspose_mul_self A).1

def gramEigenMatrix (A : Matrix E V ℝ) : Matrix E V ℝ :=
  A * ((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ)

def gramProjection (A : Matrix E V ℝ) : Matrix E E ℝ :=
  gramEigenMatrix A * diagonal (fun k => ((gramHermitian A).eigenvalues k)⁻¹) *
    (gramEigenMatrix A).transpose

lemma gramEigenMatrix_zero (A : Matrix E V ℝ) (k : V)
    (hk : (gramHermitian A).eigenvalues k = 0) (e : E) : gramEigenMatrix A e k = 0 := by
  have hh := (gramHermitian A).mulVec_eigenvectorBasis k
  rw [hk, zero_smul] at hh
  have hz := (Matrix.conjTranspose_mul_self_mulVec_eq_zero A _).mp hh
  have hh' := congrFun hz e
  simpa only [gramEigenMatrix, Matrix.mul_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Matrix.mulVec, dotProduct, Pi.zero_apply] using hh'

lemma gram_heat_apply (A : Matrix E V ℝ) (t : ℝ) (e f : E) :
    (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f =
      ∑ k, (gramEigenMatrix A e k * gramEigenMatrix A f k) *
        Real.exp (-t * (gramHermitian A).eigenvalues k) := by
  rw [matrix_exp_spectral _ (gramHermitian A)]
  have he : A * ((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ) *
      diagonal (fun k => Real.exp (-t * (gramHermitian A).eigenvalues k)) *
      (star ((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ) * A.transpose) =
      gramEigenMatrix A * diagonal (fun k => Real.exp (-t * (gramHermitian A).eigenvalues k)) *
        (gramEigenMatrix A).transpose := by
    simp only [gramEigenMatrix, Matrix.transpose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (_ * _ * _) _ A.transpose, he]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma gramProjection_heat_integral (A : Matrix E V ℝ) (e f : E) :
    IntegrableOn (fun t : ℝ => (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f)
      (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f) =
      gramProjection A e f := by
  have hh := exponential_sum_integral ((gramHermitian A).eigenvalues)
    (fun k => gramEigenMatrix A e k * gramEigenMatrix A f k)
    (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg
    (fun k hk => by rw [gramEigenMatrix_zero A k hk e, zero_mul])
  simp_rw [gram_heat_apply]
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold gramProjection
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma gramEigenMatrix_gram (A : Matrix E V ℝ) :
    (gramEigenMatrix A).transpose * gramEigenMatrix A =
      diagonal (gramHermitian A).eigenvalues := by
  let U : Matrix V V ℝ := (gramHermitian A).eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self (gramHermitian A).eigenvectorUnitary
  have hs : A.transpose * A = U * diagonal (gramHermitian A).eigenvalues * U.transpose := by
    calc
      _ = A.conjTranspose * A := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      _ = _ := (gramHermitian A).spectral_theorem
      _ = U * diagonal (gramHermitian A).eigenvalues * U.transpose := by
        change U * diagonal (RCLike.ofReal ∘ (gramHermitian A).eigenvalues) * star U = _
        have he : (RCLike.ofReal ∘ (gramHermitian A).eigenvalues : V → ℝ) =
            (gramHermitian A).eigenvalues := rfl
        rw [he]
        congr 1
  change (A * U).transpose * (A * U) = _
  rw [Matrix.transpose_mul]
  calc
    _ = U.transpose * (A.transpose * A) * U := by simp only [Matrix.mul_assoc]
    _ = (U.transpose * U) * diagonal (gramHermitian A).eigenvalues * (U.transpose * U) := by
      rw [hs]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]

lemma gramProjection_mul_eigenMatrix (A : Matrix E V ℝ) :
    gramProjection A * gramEigenMatrix A = gramEigenMatrix A := by
  unfold gramProjection
  rw [Matrix.mul_assoc, gramEigenMatrix_gram, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  ext e k
  rw [Matrix.mul_diagonal]
  by_cases hk : (gramHermitian A).eigenvalues k = 0
  · rw [gramEigenMatrix_zero A k hk e, zero_mul]
  · rw [inv_mul_cancel₀ hk, mul_one]

lemma gramProjection_mul_self (A : Matrix E V ℝ) :
    gramProjection A * A = A := by
  let U : Matrix V V ℝ := (gramHermitian A).eigenvectorUnitary
  have hU : U * U.transpose = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Unitary.coe_star] using Unitary.coe_mul_star_self (gramHermitian A).eigenvectorUnitary
  have he : gramEigenMatrix A * U.transpose = A := by
    change (A * U) * U.transpose = A
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  calc
    _ = gramProjection A * (gramEigenMatrix A * U.transpose) := by rw [he]
    _ = gramEigenMatrix A * U.transpose := by rw [← Matrix.mul_assoc, gramProjection_mul_eigenMatrix]
    _ = A := he

lemma gramProjection_idempotent (A : Matrix E V ℝ) :
    gramProjection A * gramProjection A = gramProjection A := by
  conv_lhs => rhs; unfold gramProjection
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, gramProjection_mul_eigenMatrix]
  rfl

lemma gramProjection_symmetric (A : Matrix E V ℝ) : (gramProjection A).IsSymm := by
  show (gramProjection A).transpose = gramProjection A
  simp only [gramProjection, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

lemma mul_gramProjection_of_fix (P : Matrix E E ℝ) (A : Matrix E V ℝ)
    (hPA : P * A = A) : P * gramProjection A = gramProjection A := by
  simp only [gramProjection, gramEigenMatrix, ← Matrix.mul_assoc, hPA]

lemma gramProjection_eq_of_mutual_fix (A B : Matrix E V ℝ)
    (hAB : gramProjection A * B = B) (hBA : gramProjection B * A = A) :
    gramProjection A = gramProjection B := by
  have hab := mul_gramProjection_of_fix _ B hAB
  have hba := mul_gramProjection_of_fix _ A hBA
  have ht := congrArg Matrix.transpose hab
  rw [Matrix.transpose_mul, (gramProjection_symmetric A).eq,
    (gramProjection_symmetric B).eq] at ht
  exact hba.symm.trans ht

lemma gramProjection_right_diagonal (A : Matrix E V ℝ) (d : V → ℝ)
    (hd : ∀ i, d i ≠ 0) : gramProjection (A * diagonal d) = gramProjection A := by
  have he : (A * diagonal d) * diagonal (fun i => (d i)⁻¹) = A := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have hh : (fun i => d i * (d i)⁻¹) = (fun _ : V => (1 : ℝ)) := by
      funext i; exact mul_inv_cancel₀ (hd i)
    rw [hh, Matrix.diagonal_one, Matrix.mul_one]
  apply gramProjection_eq_of_mutual_fix
  · calc
      _ = gramProjection (A * diagonal d) * ((A * diagonal d) * diagonal (fun i => (d i)⁻¹)) := by rw [he]
      _ = (A * diagonal d) * diagonal (fun i => (d i)⁻¹) := by
        rw [← Matrix.mul_assoc, gramProjection_mul_self]
      _ = A := he
  · rw [← Matrix.mul_assoc, gramProjection_mul_self]

end GramProjection
end ProjectionIntegral

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator

namespace SubpolynomialLp

section GraphHeat
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

lemma graphHeat_entry_hasDerivAt (src dst : E → V) (μ d : V → ℝ)
    (ce : E → ℝ) (hμ : ∀ i, 0 < μ i) (hrel : ∀ i, μ i * (d i * d i) = 1)
    (t : ℝ) (i v : V) :
    HasDerivAt (fun s => weightedHeatKernel (laplacianMatrix src dst ce) d s i v)
      (-graphLaplacian src dst ce
        (fun j => weightedHeatKernel (laplacianMatrix src dst ce) d t j v) i / μ i) t := by
  have hh := weightedHeatKernel_entry_hasDerivAt (laplacianMatrix src dst ce) d t i v
  rw [laplacianMatrix_mulVec] at hh
  convert hh using 1
  have he : d i * d i = 1 / μ i := by
    apply (eq_div_iff (hμ i).ne').mpr
    simpa only [mul_comm] using hrel i
  rw [he]
  ring

lemma graphHeat_mass (src dst : E → V) (ce : E → ℝ) (μ d : V → ℝ)
    (hμ : ∀ i, 0 < μ i) (hrel : ∀ i, μ i * (d i * d i) = 1) (t : ℝ) (v : V) :
    ∑ i, μ i * weightedHeatKernel (laplacianMatrix src dst ce) d t i v = 1 := by
  let K := weightedHeatKernel (laplacianMatrix src dst ce) d
  let f : ℝ → ℝ := fun s => ∑ i, μ i * K s i v
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    have hh := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (graphHeat_entry_hasDerivAt src dst μ d ce hμ hrel s i v).const_mul (μ i))
    have he : (∑ i, μ i * (-graphLaplacian src dst ce (fun j => K s j v) i / μ i)) = 0 := by
      calc
        _ = -∑ i, graphLaplacian src dst ce (fun j => K s j v) i := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          field_simp [(hμ i).ne']
        _ = 0 := by rw [graphLaplacian_sum, neg_zero]
    exact he ▸ hh
  have heq := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
    (fun s => (hf s).deriv) t 0
  change f t = 1
  rw [heq]
  simp only [f, K, weightedHeatKernel_zero, Matrix.diagonal_apply, mul_ite, mul_zero]
  simpa using hrel v

lemma graphHeat_tendsto (src dst : E → V) (ce : E → ℝ) (μ d : V → ℝ)
    (hc : ∀ e, 0 < ce e) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    (hrel : ∀ i, μ i * (d i * d i) = 1) (hsum : ∑ i, μ i = 1)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    Tendsto (weightedHeatKernel (laplacianMatrix src dst ce) d) atTop
      (𝓝 (fun _ _ => (1 : ℝ))) := by
  let L := laplacianMatrix src dst ce
  have hL : L.PosSemidef := laplacianMatrix_posSemidef src dst ce (fun e => (hc e).le)
  let T := diagonal d * spectralKernelProjection (symmetricGenerator L d)
    (symmetricGenerator_posSemidef L hL d).1 * diagonal d
  have ht : Tendsto (weightedHeatKernel L d) atTop (𝓝 T) := weightedHeatKernel_tendsto L hL d
  have hz : L * T = 0 := weightedHeatKernel_limit_ker L hL.1 d (fun i => (hd i).ne')
  have hconst (v i j : V) : T i v = T j v := by
    apply graphLaplacian_kernel_constant src dst ce hc hconn (fun k => T k v)
    funext k
    rw [← laplacianMatrix_mulVec]
    exact congrFun₂ hz k v
  have hmass (v : V) : ∑ i, μ i * T i v = 1 := by
    have hh := tendsto_finsetSum Finset.univ (fun i _ =>
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht i)) v).const_mul (μ i))
    have he : (fun t : ℝ => ∑ i, μ i * weightedHeatKernel L d t i v) = (fun _ => 1) := by
      funext t
      exact graphHeat_mass src dst ce μ d hμ hrel t v
    rw [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have he : T = (fun _ _ => (1 : ℝ)) := by
    ext i v
    have hh := hmass v
    simp_rw [hconst v _ i] at hh
    rw [← Finset.sum_mul, hsum, one_mul] at hh
    exact hh
  simpa only [he] using ht

lemma graphHeat_entropy_integral (src dst : E → V) (ce : E → ℝ) (μ d : V → ℝ)
    (hc : ∀ e, 0 < ce e) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    (hrel : ∀ i, μ i * (d i * d i) = 1) (hsum : ∑ i, μ i = 1)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) (v : V) :
    IntegrableOn (fun t => electricalEnergy src dst ce
      (fun i => weightedHeatKernel (laplacianMatrix src dst ce) d t i v)) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), electricalEnergy src dst ce
      (fun i => weightedHeatKernel (laplacianMatrix src dst ce) d t i v)) = Real.log (1 / μ v) := by
  apply heatEntropy_integral src dst ce μ _ v (fun e => (hc e).le) hμ
  · apply continuous_pi
    intro i
    exact (continuous_apply v).comp ((continuous_apply i).comp
      (weightedHeatKernel_continuous (laplacianMatrix src dst ce) d))
  · intro t ht i
    exact weightedHeatKernel_pos _ d hd (fun i j hij =>
      laplacianMatrix_offdiag_neg src dst ce hc hij (hconn i j hij)) t ht i v
  · intro t _ i
    exact graphHeat_entry_hasDerivAt src dst μ d ce hμ hrel t i v
  · funext i
    simp only [weightedHeatKernel_zero, Matrix.diagonal_apply, Pi.single_apply]
    by_cases hiv : i = v
    · subst i
      simp only [ite_true]
      apply (eq_div_iff (hμ v).ne').mpr
      simpa only [mul_comm] using hrel v
    · simp [hiv]
  · apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
      (graphHeat_tendsto src dst ce μ d hc hμ hd hrel hsum hconn) i) v

end GraphHeat

section LocalizationIntegral
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]

lemma sum_abs_outer_le (μ : V → ℝ) (w : E → ℝ) (z : E → V → ℝ)
    (hμ : ∀ v, 0 ≤ μ v) (hw : ∀ e, 0 ≤ w e) :
    (∑ e, ∑ f, w e * w f * |∑ v, μ v * z e v * z f v|) ≤
      ∑ v, μ v * (∑ e, w e * |z e v|)^2 := by
  calc
    _ ≤ ∑ e, ∑ f, ∑ v, μ v * (w e * |z e v|) * (w f * |z f v|) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      calc
        _ ≤ w e * w f * ∑ v, |μ v * z e v * z f v| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg (hw e) (hw f))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          rw [abs_mul, abs_mul, abs_of_nonneg (hμ v)]
          ring
    _ = _ := by
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      simp only [sq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      ring

lemma localization_integral_bound (Q : E → E → ℝ) (F : ℝ → E → E → ℝ)
    (I : ℝ → V → ℝ) (μ : V → ℝ) (w : E → ℝ) (S : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hrep : ∀ e f, Q e f = 2 * ∫ t in Set.Ioi (0 : ℝ), F t e f)
    (hiF : ∀ e f, IntegrableOn (fun t => F t e f) (Set.Ioi 0))
    (hiI : ∀ v, IntegrableOn (fun t => I t v) (Set.Ioi 0))
    (hint : ∀ v, (∫ t in Set.Ioi (0 : ℝ), I t v) = Real.log (1 / μ v))
    (hb : ∀ t : ℝ, 0 < t →
      (∑ e, ∑ f, w e * w f * |F t e f|) ≤ S * ∑ v, μ v * I t v) :
    (∑ e, ∑ f, w e * w f * |Q e f|) ≤
      2 * S * ∑ v, μ v * Real.log (1 / μ v) := by
  have hiF' (e f : E) : IntegrableOn (fun t => w e * w f * |F t e f|) (Set.Ioi 0) :=
    (hiF e f).abs.const_mul _
  have hsumF : IntegrableOn (fun t => ∑ e, ∑ f, w e * w f * |F t e f|) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun e _ => integrable_finsetSum _ (fun f _ => hiF' e f))
  have hsumI : IntegrableOn (fun t => ∑ v, μ v * I t v) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun v _ => (hiI v).const_mul _)
  calc
    _ ≤ 2 * (∑ e, ∑ f, w e * w f * ∫ t in Set.Ioi (0 : ℝ), |F t e f|) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      rw [hrep, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hh := mul_le_mul_of_nonneg_left
        (abs_integral_le_integral_abs (f := fun t => F t e f) (μ := volume.restrict (Set.Ioi 0)))
        (mul_nonneg (hw e) (hw f))
      nlinarith
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), ∑ e, ∑ f, w e * w f * |F t e f| := by
      congr 1
      rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun f _ => hiF' e f))]
      apply Finset.sum_congr rfl
      intro e _
      rw [integral_finsetSum _ (fun f _ => hiF' e f)]
      simp only [integral_const_mul]
    _ ≤ 2 * ∫ t in Set.Ioi (0 : ℝ), S * ∑ v, μ v * I t v := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply integral_mono_ae hsumF (hsumI.const_mul S)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t ht
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun v _ => (hiI v).const_mul _)]
      simp only [integral_const_mul, hint, mul_assoc]

end LocalizationIntegral

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator

namespace SubpolynomialLp

section GraphProjection
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

def conductorMatrix (src dst : E → V) (c : E → ℝ) : Matrix E V ℝ :=
  diagonal (fun e => Real.sqrt (c e)) * incidence src dst

omit [Fintype V] in
lemma conductorMatrix_gram (src dst : E → V) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    (conductorMatrix src dst c).transpose * conductorMatrix src dst c = laplacianMatrix src dst c := by
  have he : diagonal (fun e => Real.sqrt (c e)) * diagonal (fun e => Real.sqrt (c e)) = diagonal c := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext e
    exact Real.mul_self_sqrt (hc e)
  unfold conductorMatrix laplacianMatrix
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc
    _ = (incidence src dst).transpose *
        (diagonal (fun e => Real.sqrt (c e)) * diagonal (fun e => Real.sqrt (c e))) * incidence src dst := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [he]

lemma conductorMatrix_mul_apply (src dst : E → V) (c : E → ℝ) (K : Matrix V V ℝ) (e : E) (v : V) :
    (conductorMatrix src dst c * K) e v = Real.sqrt (c e) * (K (src e) v - K (dst e) v) := by
  rw [conductorMatrix, Matrix.mul_assoc, Matrix.diagonal_mul]
  congr 1
  exact incidence_mulVec src dst (fun i => K i v) e

omit [DecidableEq E] in
lemma gram_heat_weighted (R : Matrix E V ℝ) (d : V → ℝ) (t : ℝ) :
    (R * diagonal d) * exp (-t • ((R * diagonal d).conjTranspose * (R * diagonal d))) *
      (R * diagonal d).transpose =
    R * weightedHeatKernel (R.transpose * R) d t * R.transpose := by
  have he : (R * diagonal d).conjTranspose * (R * diagonal d) =
      symmetricGenerator (R.transpose * R) d := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.diagonal_transpose]
    simp only [symmetricGenerator, Matrix.mul_assoc]
  rw [he]
  simp only [weightedHeatKernel, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

omit [DecidableEq E] in
lemma gram_heat_twice (R : Matrix E V ℝ) (d μ : V → ℝ)
    (hrel : ∀ i, d i * μ i * d i = 1) (t : ℝ) (e f : E) :
    ((R * diagonal d) * exp (-(2*t) • ((R * diagonal d).conjTranspose * (R * diagonal d))) *
      (R * diagonal d).transpose) e f =
      ∑ v, μ v * (R * weightedHeatKernel (R.transpose * R) d t) e v *
        (R * weightedHeatKernel (R.transpose * R) d t) f v := by
  rw [gram_heat_weighted, two_mul, weightedHeatKernel_semigroup _ _ _ hrel]
  have hL : (R.transpose * R).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
  have he : R * (weightedHeatKernel (R.transpose * R) d t * diagonal μ *
      weightedHeatKernel (R.transpose * R) d t) * R.transpose =
      (R * weightedHeatKernel (R.transpose * R) d t) * diagonal μ *
        (R * weightedHeatKernel (R.transpose * R) d t).transpose := by
    rw [Matrix.transpose_mul, (weightedHeatKernel_symmetric _ hL d t).eq]
    simp only [Matrix.mul_assoc]
  rw [he, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro v _
  ring

omit [Fintype V] [DecidableEq E] in
lemma vertexWeight_pos (src dst : E → V) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (i : V) (hi : ∃ e, src e = i ∨ dst e = i) : 0 < vertexWeight src dst w i := by
  have hn (p : E → Prop) [DecidablePred p] : 0 ≤ ∑ e, if p e then (w e)^2 else 0 := by
    apply Finset.sum_nonneg
    intro e _
    split_ifs <;> positivity
  have hp (p : E → Prop) [DecidablePred p] (e : E) (he : p e) :
      0 < ∑ e, if p e then (w e)^2 else 0 := by
    apply Finset.sum_pos' (fun e _ => by split_ifs <;> positivity)
    exact ⟨e, Finset.mem_univ e, by simpa only [ite_eq_left he] using sq_pos_of_pos (hw e)⟩
  obtain ⟨e, he | he⟩ := hi
  · exact add_pos_of_pos_of_nonneg (hp _ e he) (hn _)
  · exact add_pos_of_nonneg_of_pos (hn _) (hp _ e he)

lemma graph_localization_positive (src dst : E → V) (c w : E → ℝ)
    (hc : ∀ e, 0 < c e) (hw : ∀ e, 0 < w e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (hW : 0 < ∑ e, (w e)^2) :
    (∑ e, ∑ f, w e * w f * |gramProjection (conductorMatrix src dst c) e f|) ≤
      2 * Real.log (Fintype.card V : ℝ) * ∑ e, (w e)^2 := by
  let R := conductorMatrix src dst c
  let μ := vertexMass src dst w
  let d : V → ℝ := fun i => (Real.sqrt (μ i))⁻¹
  let A := R * diagonal d
  let L := laplacianMatrix src dst c
  let K := weightedHeatKernel L d
  let F : ℝ → E → E → ℝ := fun t e f =>
    (A * exp (-(2*t) • (A.conjTranspose * A)) * A.transpose) e f
  let I : ℝ → V → ℝ := fun t v => electricalEnergy src dst c (fun i => K t i v)
  have hμ (i : V) : 0 < μ i :=
    div_pos (vertexWeight_pos src dst w hw i (hinc i)) (by positivity)
  have hd (i : V) : 0 < d i := inv_pos.mpr (Real.sqrt_pos.mpr (hμ i))
  have hrel (i : V) : μ i * (d i * d i) = 1 := by
    dsimp only [d]
    rw [← mul_inv, Real.mul_self_sqrt (hμ i).le, mul_inv_cancel₀ (hμ i).ne']
  have hrel' (i : V) : d i * μ i * d i = 1 := by nlinarith [hrel i]
  have hsum : ∑ i, μ i = 1 := vertexMass_sum src dst w hW
  have hR : R.transpose * R = L := conductorMatrix_gram src dst c (fun e => (hc e).le)
  have hrep (e f : E) : gramProjection R e f = 2 * ∫ t in Set.Ioi (0 : ℝ), F t e f := by
    have hh := integral_comp_mul_left_Ioi' (fun t : ℝ =>
      (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f) 0 (by norm_num : (0 : ℝ) < 2)
    have he := (gramProjection_heat_integral A e f).2
    rw [mul_zero] at hh
    rw [he] at hh
    have hQ : gramProjection A = gramProjection R :=
      gramProjection_right_diagonal R d (fun i => (hd i).ne')
    rw [hQ] at hh
    exact hh.symm
  have hiF (e f : E) : IntegrableOn (fun t => F t e f) (Set.Ioi 0) := by
    have hh := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ =>
      (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f) 0 (by norm_num : (0 : ℝ) < 2)).2
    apply hh
    simpa only [mul_zero] using (gramProjection_heat_integral A e f).1
  have hI (v : V) : IntegrableOn (fun t => I t v) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), I t v) = Real.log (1 / μ v) :=
    graphHeat_entropy_integral src dst c μ d hc hμ hd hrel hsum hconn v
  have hb (t : ℝ) (ht : 0 < t) :
      (∑ e, ∑ f, w e * w f * |F t e f|) ≤ (∑ e, (w e)^2) * ∑ v, μ v * I t v := by
    have heF (e f : E) : F t e f = ∑ v, μ v * (R * K t) e v * (R * K t) f v := by
      have hh := gram_heat_twice R d μ hrel' t e f
      rw [hR] at hh
      exact hh
    have henergy (v : V) : (∑ e, w e * |(R * K t) e v|)^2 ≤ I t v * ∑ e, (w e)^2 := by
      have hpos (i : V) : 0 < K t i v := weightedHeatKernel_pos L d hd
        (fun i j hij => laplacianMatrix_offdiag_neg src dst c hc hij (hconn i j hij)) t ht i v
      have hh := heat_cauchy_schwarz src dst c w (fun i => K t i v) (fun e => (hc e).le)
        hpos hW (graphHeat_mass src dst c μ d hμ hrel t v)
      exact le_of_eq_of_le (by
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [conductorMatrix_mul_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        ring) hh
    simp_rw [heF]
    calc
      _ ≤ ∑ v, μ v * (∑ e, w e * |(R * K t) e v|)^2 :=
        sum_abs_outer_le μ w (R * K t) (fun v => (hμ v).le) (fun e => (hw e).le)
      _ ≤ ∑ v, μ v * (I t v * ∑ e, (w e)^2) :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (henergy v) (hμ v).le)
      _ = _ := by simp only [← mul_assoc, ← Finset.sum_mul]; ring
  have hh := localization_integral_bound (gramProjection R) F I μ w (∑ e, (w e)^2)
    (fun e => (hw e).le) hrep hiF (fun v => (hI v).1) (fun v => (hI v).2) hb
  have he := mul_le_mul_of_nonneg_left (entropy_le_log_card μ hμ hsum)
    (show 0 ≤ 2 * ∑ e, (w e)^2 by positivity)
  exact hh.trans (by convert he using 1; ring)

lemma graph_localization_nonneg (src dst : E → V) (c w : E → ℝ)
    (hc : ∀ e, 0 < c e) (hw : ∀ e, 0 ≤ w e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    (∑ e, ∑ f, w e * w f * |gramProjection (conductorMatrix src dst c) e f|) ≤
      2 * Real.log (Fintype.card V : ℝ) * ∑ e, (w e)^2 := by
  cases isEmpty_or_nonempty E with
  | inl hE => simp
  | inr hE =>
    let wn : ℕ → E → ℝ := fun n e => w e + 1 / ((n : ℝ) + 1)
    have hp (n : ℕ) (e : E) : 0 < wn n e := by
      dsimp [wn]
      exact add_pos_of_nonneg_of_pos (hw e) (by positivity)
    have ht : Tendsto wn atTop (𝓝 w) := by
      apply tendsto_pi_nhds.mpr
      intro e
      simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (w e)
    let f : (E → ℝ) → ℝ := fun x => ∑ e, ∑ f, x e * x f *
      |gramProjection (conductorMatrix src dst c) e f|
    let g : (E → ℝ) → ℝ := fun x => 2 * Real.log (Fintype.card V : ℝ) * ∑ e, (x e)^2
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hg : Continuous g := by dsimp [g]; fun_prop
    apply le_of_tendsto_of_tendsto' ((hf.tendsto w).comp ht) ((hg.tendsto w).comp ht)
    intro n
    apply graph_localization_positive src dst c (wn n) hc (hp n) hinc hconn
    exact Finset.sum_pos (fun e _ => sq_pos_of_pos (hp n e)) Finset.univ_nonempty

lemma orthogonal_sum_sq (U : Matrix E E ℝ) (hU : U.transpose * U = 1) (x : E → ℝ) :
    ∑ i, (U *ᵥ x) i ^ 2 = ∑ i, (x i)^2 := by
  have hh : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hU, Matrix.vecMul_one]
  simpa only [dotProduct, sq] using hh

lemma symmetric_quadratic_bound_sq (B : Matrix E E ℝ) (hB : B.IsSymm) (H : ℝ)
    (hb : ∀ x : E → ℝ, |x ⬝ᵥ (B *ᵥ x)| ≤ H * ∑ i, (x i)^2) (x : E → ℝ) :
    (∑ i, (B *ᵥ x) i ^ 2) ≤ H^2 * ∑ i, (x i)^2 := by
  let hS : B.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hB
  let U : Matrix E E ℝ := hS.eigenvectorUnitary
  let lam : E → ℝ := hS.eigenvalues
  have hU : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hU' : U * U.transpose = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hs : B = U * diagonal lam * U.transpose := by
    convert hS.spectral_theorem using 1
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hBU : B * U = U * diagonal lam := by
    rw [hs, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hnorm (k : E) : ∑ i, (U i k)^2 = 1 := by
    have hh := congrFun₂ hU k k
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq] using hh
  have hval (k : E) : |lam k| ≤ H := by
    have he : B *ᵥ (fun i => U i k) = fun i => U i k * lam k := by
      funext i
      change (B * U) i k = U i k * lam k
      rw [hBU, Matrix.mul_diagonal]
    have hh := hb (fun i => U i k)
    have hd : (fun i => U i k) ⬝ᵥ (fun i => U i k * lam k) = lam k := by
      simp only [dotProduct, ← mul_assoc, ← sq, ← Finset.sum_mul, hnorm, one_mul]
    rw [he, hd, hnorm, mul_one] at hh
    exact hh
  let y := U.transpose *ᵥ x
  have hy : ∑ i, (y i)^2 = ∑ i, (x i)^2 := by
    apply orthogonal_sum_sq
    simpa only [Matrix.transpose_transpose] using hU'
  have he : B *ᵥ x = U *ᵥ (diagonal lam *ᵥ y) := by
    rw [hs]
    simp only [Matrix.mulVec_mulVec, y, Matrix.mul_assoc]
  rw [he, orthogonal_sum_sq U hU]
  calc
    _ = ∑ i, (lam i)^2 * (y i)^2 := by simp only [Matrix.mulVec_diagonal, mul_pow]
    _ ≤ ∑ i, H^2 * (y i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (lam i)) (hval i) 2
    _ = _ := by rw [← Finset.mul_sum, hy]


lemma graph_localization_quadratic (src dst : E → V) (c x : E → ℝ)
    (hc : ∀ e, 0 < c e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    abs (∑ e, ∑ f, x e * x f * |gramProjection (conductorMatrix src dst c) e f|) ≤
      2 * Real.log (Fintype.card V : ℝ) * ∑ e, (x e)^2 := by
  calc
    _ ≤ ∑ e, abs (∑ f, x e * x f * |gramProjection (conductorMatrix src dst c) e f|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, ∑ f, abs (x e * x f * |gramProjection (conductorMatrix src dst c) e f|) :=
      Finset.sum_le_sum (fun e _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ e, ∑ f, |x e| * |x f| * |gramProjection (conductorMatrix src dst c) e f| := by
      simp only [abs_mul, abs_abs]
    _ ≤ _ := by
      simpa only [sq_abs] using graph_localization_nonneg src dst c (fun e => |x e|) hc
        (fun e => abs_nonneg _) hinc hconn

/-- The squared ℓ₂ form of electrical localization, for the complete graph
used by the main upper-bound construction. -/
lemma electrical_localization_complete (src dst : E → V) (c x : E → ℝ)
    (hc : ∀ e, 0 < c e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    (∑ e, (∑ f, |gramProjection (conductorMatrix src dst c) e f| * x f)^2) ≤
      (2 * Real.log (Fintype.card V : ℝ))^2 * ∑ e, (x e)^2 := by
  let B : Matrix E E ℝ := fun e f => |gramProjection (conductorMatrix src dst c) e f|
  have hsym : B.IsSymm := by
    ext e f
    exact congrArg abs (congrFun₂ (gramProjection_symmetric _) e f)
  apply symmetric_quadratic_bound_sq B hsym
  intro y
  have hh := graph_localization_quadratic src dst c y hc hinc hconn
  convert hh using 1
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, B]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

end GraphProjection

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator

namespace SubpolynomialLp

def powerDefect (p a b : ℝ) : ℝ :=
  |a+b|^p + |a-b|^p - 2*|a|^p - 2*|b|^p

lemma sq_rpow_half (p a : ℝ) : (a^2)^(p/2) = |a|^p := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  ring

lemma strictly_superadditive_rpow {p a b : ℝ} (hp : 1 < p) (ha : 0 < a) (hb : 0 < b) :
    a^p + b^p < (a+b)^p := by
  have hsum : 0 < a+b := add_pos ha hb
  have hta : 0 < a/(a+b) := div_pos ha hsum
  have htb : 0 < b/(a+b) := div_pos hb hsum
  have ht : a/(a+b) + b/(a+b) = 1 := by field_simp
  have h1 := (strictConvexOn_rpow hp).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) hta htb ht
  have h2 := (strictConvexOn_rpow hp).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) htb hta (by linarith)
  have he1 : b/(a+b) * (a+b) = b := by field_simp
  have he2 : a/(a+b) * (a+b) = a := by field_simp
  simp only [smul_eq_mul, Real.zero_rpow (by linarith : p ≠ 0), mul_zero,
    zero_add] at h1 h2
  rw [he1] at h1
  rw [he2] at h2
  nlinarith [show (a/(a+b) + b/(a+b)) * (a+b)^p = (a+b)^p by rw [ht, one_mul]]

lemma strictly_subadditive_rpow {p a b : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : 0 < b) :
    (a+b)^p < a^p + b^p := by
  have hsum : 0 < a+b := add_pos ha hb
  have hta : 0 < a/(a+b) := div_pos ha hsum
  have htb : 0 < b/(a+b) := div_pos hb hsum
  have ht : a/(a+b) + b/(a+b) = 1 := by field_simp
  have h1 := (Real.strictConcaveOn_rpow hp hp1).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) hta htb ht
  have h2 := (Real.strictConcaveOn_rpow hp hp1).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) htb hta (by linarith)
  have he1 : b/(a+b) * (a+b) = b := by field_simp
  have he2 : a/(a+b) * (a+b) = a := by field_simp
  simp only [smul_eq_mul, Real.zero_rpow hp.ne', mul_zero, zero_add] at h1 h2
  rw [he1] at h1
  rw [he2] at h2
  nlinarith [show (a/(a+b) + b/(a+b)) * (a+b)^p = (a+b)^p by rw [ht, one_mul]]

lemma powerDefect_pos {p a b : ℝ} (hp : 2 < p) (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < powerDefect p a b := by
  have hc := (convexOn_rpow (show 1 ≤ p/2 by linarith)).2
    (show (a+b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a+b)) (show (a-b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a-b))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have he : (1/2:ℝ) * (a+b)^2 + (1/2:ℝ) * (a-b)^2 = a^2+b^2 := by ring
  simp only [smul_eq_mul, he] at hc
  have hs := strictly_superadditive_rpow (show 1 < p/2 by linarith)
    (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb)
  simp only [sq_rpow_half] at hc hs
  unfold powerDefect
  linarith

lemma powerDefect_neg {p a b : ℝ} (hp : 0 < p) (hp2 : p < 2) (ha : a ≠ 0) (hb : b ≠ 0) :
    powerDefect p a b < 0 := by
  have hc := (Real.concaveOn_rpow (show 0 ≤ p/2 by linarith) (show p/2 ≤ 1 by linarith)).2
    (show (a+b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a+b)) (show (a-b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a-b))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have he : (1/2:ℝ) * (a+b)^2 + (1/2:ℝ) * (a-b)^2 = a^2+b^2 := by ring
  simp only [smul_eq_mul, he] at hc
  have hs := strictly_subadditive_rpow (show 0 < p/2 by linarith) (show p/2 < 1 by linarith)
    (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb)
  simp only [sq_rpow_half] at hc hs
  unfold powerDefect
  linarith

lemma powerDefect_eq_zero_iff {p a b : ℝ} (hp : 0 < p) (hp2 : p ≠ 2) :
    powerDefect p a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro hh
    by_contra hab
    push Not at hab
    rcases lt_or_gt_of_ne hp2 with hlt | hgt
    · linarith [powerDefect_neg hp hlt hab.1 hab.2]
    · linarith [powerDefect_pos hgt hab.1 hab.2]
  · rintro (rfl | rfl) <;> simp [powerDefect, Real.zero_rpow hp.ne'] <;> ring

def lpPower {I : Type uI} [Fintype I] (p : ℝ) (x : I → ℝ) : ℝ := ∑ i, |x i|^p

lemma lpPower_disjointness {I : Type uI} [Fintype I] (p : ℝ) (hp : 0 < p) (hp2 : p ≠ 2)
    (u v : I → ℝ) :
    lpPower p (u+v) + lpPower p (u-v) = 2*lpPower p u + 2*lpPower p v ↔
      ∀ i, u i = 0 ∨ v i = 0 := by
  have he : lpPower p (u+v) + lpPower p (u-v) - 2*lpPower p u - 2*lpPower p v =
      ∑ i, powerDefect p (u i) (v i) := by
    simp only [lpPower, powerDefect, Pi.add_apply, Pi.sub_apply, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hz (i : I) : powerDefect p (u i) (v i) = 0 ↔ u i = 0 ∨ v i = 0 :=
    powerDefect_eq_zero_iff hp hp2
  rw [← sub_eq_zero, ← sub_sub, he]
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · rw [Finset.sum_eq_zero_iff_of_nonpos]
    · simp only [Finset.mem_univ, true_implies, hz]
    · intro i _
      by_cases hi : u i = 0 ∨ v i = 0
      · exact (hz i).2 hi |>.le
      · push Not at hi
        exact (powerDefect_neg hp hlt hi.1 hi.2).le
  · rw [Finset.sum_eq_zero_iff_of_nonneg]
    · simp only [Finset.mem_univ, true_implies, hz]
    · intro i _
      by_cases hi : u i = 0 ∨ v i = 0
      · exact (hz i).2 hi |>.ge
      · push Not at hi
        exact (powerDefect_pos hgt hi.1 hi.2).le

lemma abs_midpoint_rpow_strict {p a b : ℝ} (hp : 1 < p) (hab : a ≠ b) :
    |(a+b)/2|^p < (|a|^p+|b|^p)/2 := by
  by_cases he : |a| = |b|
  · have hn : a = -b := (abs_eq_abs.mp he).resolve_left hab
    have hb : b ≠ 0 := by intro h; apply hab; simpa [h] using hn
    rw [hn]
    simp only [neg_add_cancel, zero_div, abs_zero, Real.zero_rpow (by linarith : p ≠ 0), abs_neg]
    positivity
  · have hh := (strictConvexOn_rpow hp).2 (abs_nonneg a) (abs_nonneg b) he
      (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    have hm : |(a+b)/2| ≤ (1/2:ℝ)*|a|+(1/2:ℝ)*|b| := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_add_le a b]
    have hr := Real.rpow_le_rpow (abs_nonneg ((a+b)/2)) hm (show 0 ≤ p by linarith)
    exact hr.trans_lt (by linarith [hh])

lemma abs_midpoint_rpow_le {p a b : ℝ} (hp : 1 < p) :
    |(a+b)/2|^p ≤ (|a|^p+|b|^p)/2 := by
  by_cases hab : a = b
  · subst b
    have he : (a+a)/2 = a := by ring
    rw [he]; linarith
  · exact (abs_midpoint_rpow_strict hp hab).le

lemma lpPower_midpoint_eq_iff {I : Type uI} [Fintype I] (p : ℝ) (hp : 1 < p)
    (u v : I → ℝ) :
    lpPower p (fun i => (u i+v i)/2) = (lpPower p u+lpPower p v)/2 ↔ u = v := by
  constructor
  · intro he
    have hs : ∑ i, ((|u i|^p+|v i|^p)/2 - |(u i+v i)/2|^p) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
      change (lpPower p u + lpPower p v)/2 - lpPower p (fun i => (u i+v i)/2) = 0
      linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      sub_nonneg.mpr (abs_midpoint_rpow_le hp))).mp hs
    funext i
    by_contra hh
    have hs := hi i (Finset.mem_univ i)
    linarith [abs_midpoint_rpow_strict hp hh]
  · rintro rfl
    have he (i : I) : (u i+u i)/2 = u i := by ring
    simp only [he]
    ring

lemma lpPower_nonneg {I : Type uI} [Fintype I] (p : ℝ) (x : I → ℝ) : 0 ≤ lpPower p x :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)

lemma lpPower_neg {I : Type uI} [Fintype I] (p : ℝ) (x : I → ℝ) : lpPower p (-x) = lpPower p x := by
  simp only [lpPower, Pi.neg_apply, abs_neg]

lemma lpPower_smul {I : Type uI} [Fintype I] (p a : ℝ) (x : I → ℝ) :
    lpPower p (a • x) = |a|^p * lpPower p x := by
  simp only [lpPower, Pi.smul_apply, smul_eq_mul, abs_mul,
    Real.mul_rpow (abs_nonneg a) (abs_nonneg _), Finset.mul_sum]

lemma lpPower_midpoint {I : Type uI} [Fintype I] (p : ℝ) (x y : I → ℝ) :
    lpPower p (fun i => (x i+y i)/2) = lpPower p (x+y)/(2:ℝ)^p := by
  simp only [lpPower, abs_div, abs_of_pos (show (0:ℝ)<2 by norm_num),
    Real.div_rpow (abs_nonneg _) (show (0:ℝ)≤2 by norm_num), Finset.sum_div, Pi.add_apply]

lemma antipodes_of_lpPower {I : Type uI} [Fintype I] (p : ℝ) (hp : 1 < p)
    (u v : I → ℝ) (h1 : lpPower p v = lpPower p u)
    (h2 : lpPower p (u-v) = (2:ℝ)^p * lpPower p u) : v = -u := by
  have he : lpPower p (fun i => (u i + (-v) i)/2) = (lpPower p u + lpPower p (-v))/2 := by
    rw [lpPower_midpoint, lpPower_neg, h1, ← sub_eq_add_neg, h2]
    field_simp
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) p]
  have hh := (lpPower_midpoint_eq_iff p hp u (-v)).mp he
  simpa using congrArg Neg.neg hh |>.symm

lemma disjoint_rows_columns_card {I : Type uI} {J : Type uJ} {E : Type uE} [Fintype I] [Fintype J] [Fintype E]
    (r : I → E → ℝ) (c : J → E → ℝ)
    (hr : ∀ i i', i ≠ i' → ∀ e, r i e = 0 ∨ r i' e = 0)
    (hc : ∀ j j', j ≠ j' → ∀ e, c j e = 0 ∨ c j' e = 0)
    (hrc : ∀ i j, ∃ e, r i e ≠ 0 ∧ c j e ≠ 0) :
    Fintype.card I * Fintype.card J ≤ Fintype.card E := by
  classical
  choose f hf using hrc
  have hinj : Function.Injective (fun ij : I × J => f ij.1 ij.2) := by
    intro ij ij' he
    change f ij.1 ij.2 = f ij'.1 ij'.2 at he
    apply Prod.ext
    · by_contra hh
      rcases hr _ _ hh (f ij.1 ij.2) with h | h
      · exact (hf _ _).1 h
      · rw [he] at h
        exact (hf _ _).1 h
    · by_contra hh
      rcases hc _ _ hh (f ij.1 ij.2) with h | h
      · exact (hf _ _).2 h
      · rw [he] at h
        exact (hf _ _).2 h
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective _ hinj

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator

namespace SubpolynomialLp

section Grid
variable {I : Type uI} [Fintype I] [DecidableEq I]

def rowVector (i : I) : I × I → ℝ := fun ab => if ab.1 = i then 1 else 0
def colVector (j : I) : I × I → ℝ := fun ab => if ab.2 = j then 1 else 0
abbrev GridIndex (I : Type uI) := Option ((I ⊕ I) × Bool)
def gridVector : GridIndex I → I × I → ℝ
  | none => 0
  | some (Sum.inl i, false) => rowVector i
  | some (Sum.inl i, true) => -rowVector i
  | some (Sum.inr j, false) => colVector j
  | some (Sum.inr j, true) => -colVector j

omit [Fintype I] in
lemma row_disjoint (i i' : I) (hne : i ≠ i') (ab : I × I) :
    rowVector i ab = 0 ∨ rowVector i' ab = 0 := by
  by_cases h : ab.1 = i
  · right
    simp [rowVector, h, hne]
  · left; simp [rowVector, h]

omit [Fintype I] in
lemma col_disjoint (j j' : I) (hne : j ≠ j') (ab : I × I) :
    colVector j ab = 0 ∨ colVector j' ab = 0 := by
  by_cases h : ab.2 = j
  · right
    simp [colVector, h, hne]
  · left; simp [colVector, h]

omit [Fintype I] in
lemma row_col_not_disjoint (i j : I) :
    ¬ (∀ ab, rowVector i ab = 0 ∨ colVector j ab = 0) := by
  intro h
  simpa [rowVector, colVector] using h (i,j)

lemma grid_dimension_obstruction {E : Type uE} [Fintype E] (p : ℝ)
    (hp : 1 < p) (hp2 : p ≠ 2) (f : GridIndex I → E → ℝ)
    (hf0 : f none = 0)
    (hf : ∀ i j, lpPower p (f i-f j) = lpPower p (gridVector i-gridVector j)) :
    (Fintype.card I)^2 ≤ Fintype.card E := by
  let r : I → E → ℝ := fun i => f (some (Sum.inl i, false))
  let c : I → E → ℝ := fun j => f (some (Sum.inr j, false))
  have hn (i : GridIndex I) : lpPower p (f i) = lpPower p (gridVector i) := by
    simpa only [hf0, gridVector, sub_zero] using hf i none
  have hneg (i : I ⊕ I) : gridVector (some (i,true)) = -gridVector (some (i,false)) := by
    cases i <;> rfl
  have hant (i : I ⊕ I) : f (some (i,true)) = -f (some (i,false)) := by
    apply antipodes_of_lpPower p hp
    · rw [hn, hn, hneg, lpPower_neg]
    · have hh := hf (some (i,false)) (some (i,true))
      have he : gridVector (some (i,false)) - gridVector (some (i,true)) =
          (2:ℝ) • gridVector (some (i,false)) := by
        rw [hneg]
        module
      rw [he, lpPower_smul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      rw [hn]
      exact hh
  have hd (i j : I ⊕ I) :
      (∀ a, f (some (i,false)) a = 0 ∨ f (some (j,false)) a = 0) ↔
      (∀ a, gridVector (some (i,false)) a = 0 ∨ gridVector (some (j,false)) a = 0) := by
    rw [← lpPower_disjointness p (by linarith) hp2, ← lpPower_disjointness p (by linarith) hp2]
    have he : gridVector (some (j,true)) = -gridVector (some (j,false)) := by
      cases j <;> rfl
    have hs : lpPower p (f (some (i,false)) + f (some (j,false))) =
        lpPower p (gridVector (some (i,false)) + gridVector (some (j,false))) := by
      have hh := hf (some (i,false)) (some (j,true))
      simpa only [hant, he, sub_neg_eq_add] using hh
    rw [hs, hf, hn, hn]
  apply le_trans _ (disjoint_rows_columns_card r c ?_ ?_ ?_)
  · simp [sq]
  · intro i i' hh
    exact (hd (Sum.inl i) (Sum.inl i')).mpr (row_disjoint i i' hh)
  · intro j j' hh
    exact (hd (Sum.inr j) (Sum.inr j')).mpr (col_disjoint j j' hh)
  · intro i j
    have hh : ¬ (∀ a, r i a = 0 ∨ c j a = 0) := by
      intro ha
      exact row_col_not_disjoint i j ((hd (Sum.inl i) (Sum.inr j)).mp ha)
    push Not at hh
    exact hh

end Grid

section FiniteLp
variable {I : Type uI} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma finite_memLp (p : ℝ) (x : I → ℝ) : MemLp x (ENNReal.ofReal p) Measure.count := by
  exact ⟨(measurable_of_finite x).aestronglyMeasurable,
    eLpNorm_count_lt_top_of_lt (f := x) (fun i => enorm_lt_top)⟩

def finiteToLp (p : ℝ) (x : I → ℝ) : Lp ℝ (ENNReal.ofReal p) (Measure.count : Measure I) :=
  (finite_memLp p x).toLp x

lemma finiteToLp_sub (p : ℝ) (x y : I → ℝ) :
    finiteToLp p (x-y) = finiteToLp p x - finiteToLp p y := by
  exact (finite_memLp p x).toLp_sub (finite_memLp p y)

lemma finiteToLp_injective (p : ℝ) : Function.Injective (finiteToLp (I := I) p) := by
  intro x y hh
  have h := (finite_memLp p x).coeFn_toLp.symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ (ENNReal.ofReal p) Measure.count =>
        (f : I → ℝ)) hh)).trans (finite_memLp p y).coeFn_toLp)
  exact funext ((Measure.ae_count_iff).mp h)

lemma finiteToLp_norm (p : ℝ) (hp : 0 < p) (x : I → ℝ) :
    ‖finiteToLp p x‖ = (∑ i, |x i|^p)^(1/p) := by
  rw [finiteToLp, Lp.norm_toLp, toReal_eLpNorm (finite_memLp p x).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
      (finite_memLp p x).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, integral_count]
  simp only [Real.norm_eq_abs, one_div]

lemma finiteToLp_infinite [Nonempty I] (p : ℝ) :
    Infinite (Lp ℝ (ENNReal.ofReal p) (Measure.count : Measure I)) := by
  apply Infinite.of_injective (fun a : ℝ => finiteToLp p (fun _ : I => a))
  intro a b he
  have hh := finiteToLp_injective p he
  exact congrFun hh (Classical.arbitrary I)

lemma finite_extend_card {A : Type uA} [Infinite A] (t : Finset A) (n : ℕ) (h : t.card ≤ n) :
    ∃ s : Finset A, t ⊆ s ∧ s.card = n := by
  classical
  obtain ⟨u, hu⟩ := Finset.exists_card_eq (α := A) n
  have hn : n ≤ (t ∪ u).card := hu.symm.trans_le (Finset.card_le_card Finset.subset_union_right)
  obtain ⟨s, hts, _, hs⟩ := Finset.exists_subsuperset_card_eq Finset.subset_union_left h hn
  exact ⟨s, hts, hs⟩


end FiniteLp

lemma GoodDimension.finite_family {p D : ℝ} {n d : ℕ} (h : GoodDimension.{u} p n D d)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [Infinite (Lp ℝ (ENNReal.ofReal p) μ)] {J : Type uJ} [Fintype J]
    (x : J → Lp ℝ (ENNReal.ofReal p) μ) (hJ : Fintype.card J ≤ n) :
    ∃ (y : J → Fin d → ℝ) (s : ℝ), 0 < s ∧
      ∀ i j, s * ‖x i-x j‖ ≤ coordinateDistance p (y i) (y j) ∧
        coordinateDistance p (y i) (y j) ≤ D*s*‖x i-x j‖ := by
  classical
  let t := Finset.univ.image x
  have ht : t.card ≤ n := (Finset.card_image_le).trans (by simpa using hJ)
  obtain ⟨S, hS, hc⟩ := finite_extend_card t n ht
  let e : S ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hc)
  let z : Fin n → Lp ℝ (ENNReal.ofReal p) μ := fun i => (e.symm i).val
  have hz : Function.Injective z := Subtype.val_injective.comp e.symm.injective
  obtain ⟨y, s, hs, hy⟩ := h Ω inferInstance μ z hz
  let j : J → S := fun i => ⟨x i, hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  refine ⟨fun i => y (e (j i)), s, hs, ?_⟩
  intro a b
  simpa only [z, Equiv.symm_apply_apply, j] using hy (e (j a)) (e (j b))

lemma coordinateDistance_rpow (p : ℝ) (hp : 0 < p) {d : ℕ} (x y : Fin d → ℝ) :
    coordinateDistance p x y ^ p = lpPower p (x-y) := by
  unfold coordinateDistance
  rw [one_div, Real.rpow_inv_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne']
  rfl

lemma finiteToLp_norm_rpow (p : ℝ) (hp : 0 < p) {I : Type uI} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (x : I → ℝ) :
    ‖finiteToLp p x‖^p = lpPower p x := by
  rw [finiteToLp_norm p hp, one_div, Real.rpow_inv_rpow]
  · rfl
  · exact lpPower_nonneg p x
  · exact hp.ne'

lemma exact_lower_of_goodDimension (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2)
    (n d : ℕ) (hn : 9 ≤ n) (hd : GoodDimension.{u} p n 1 d) :
    ((n-1)/4)^2 ≤ d := by
  classical
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let k := (n-1)/4
  have hk : 0 < k := by dsimp [k]; omega
  have : NeZero k := ⟨by omega⟩
  let Ω := ULift.{u} (Fin k × Fin k)
  let : MeasurableSpace Ω := ⊤
  have : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  let X : GridIndex (Fin k) → Ω → ℝ := fun i a => gridVector i a.down
  let x : GridIndex (Fin k) → Lp ℝ (ENNReal.ofReal p) (Measure.count : Measure Ω) :=
    fun i => finiteToLp p (X i)
  have := finiteToLp_infinite (I := Ω) p
  have hJ : Fintype.card (GridIndex (Fin k)) ≤ n := by
    simp only [GridIndex, Fintype.card_option, Fintype.card_prod, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_bool]
    dsimp [k]
    omega
  obtain ⟨y,s,hs,hy⟩ := hd.finite_family Measure.count x hJ
  have hxy (i j) : lpPower p (y i-y j) = s^p * lpPower p (gridVector i-gridVector j) := by
    have he : coordinateDistance p (y i) (y j) = s * ‖x i-x j‖ :=
      (hy i j).2.trans_eq (by ring) |>.antisymm (hy i j).1
    have hpow := congrArg (fun a : ℝ => a^p) he
    rw [coordinateDistance_rpow p (by linarith), Real.mul_rpow hs.le (norm_nonneg _)] at hpow
    have hnrm : ‖x i-x j‖^p = lpPower p (gridVector i-gridVector j) := by
      change ‖finiteToLp p (X i)-finiteToLp p (X j)‖^p = _
      rw [← finiteToLp_sub, finiteToLp_norm_rpow p (by linarith)]
      simp only [lpPower, Pi.sub_apply, X]
      exact (Equiv.ulift : Ω ≃ Fin k × Fin k).sum_comp (fun a => |gridVector i a - gridVector j a|^p)
    rwa [hnrm] at hpow
  let f : GridIndex (Fin k) → Fin d → ℝ := fun i => s⁻¹ • (y i-y none)
  have hf0 : f none = 0 := by simp [f]
  have hf (i j) : lpPower p (f i-f j) = lpPower p (gridVector i-gridVector j) := by
    have he : f i-f j = s⁻¹ • (y i-y j) := by dsimp [f]; module
    rw [he, lpPower_smul, abs_inv, abs_of_pos hs, Real.inv_rpow hs.le, hxy,
      inv_mul_cancel_left₀ (Real.rpow_pos_of_pos hs p).ne']
  have hh := grid_dimension_obstruction p hp hp2 f hf0 hf
  simpa only [Fintype.card_fin] using hh

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator

namespace SubpolynomialLp

def PairIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
instance (n : ℕ) : Fintype (PairIndex n) := inferInstanceAs (Fintype {ij : Fin n × Fin n // ij.1 < ij.2})

lemma pairIndex_card (n : ℕ) : Fintype.card (PairIndex n) = n.choose 2 := by
  classical
  change Fintype.card {ij : Fin n × Fin n // ij.1 < ij.2} = _
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
  simp

def pairPower (p : ℝ) {n : ℕ} (z : Fin n → ℝ) : PairIndex n → ℝ :=
  fun e => |z e.val.1 - z e.val.2| ^ p

lemma pairPower_nonneg (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (e : PairIndex n) :
    0 ≤ pairPower p z e := Real.rpow_nonneg (abs_nonneg _) _

lemma pairPower_continuous (p : ℝ) (hp : 0 < p) (n : ℕ) : Continuous (pairPower (n := n) p) := by
  apply continuous_pi
  intro e
  unfold pairPower
  exact ((continuous_apply e.val.1).sub (continuous_apply e.val.2)).abs.rpow_const
    (fun _ => Or.inr hp.le)

lemma pairPower_pair_le_sum (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    |z i-z j|^p ≤ ∑ e, pairPower p z e := by
  classical
  rcases lt_or_gt_of_ne hij with h | h
  · exact Finset.single_le_sum (fun e _ => pairPower_nonneg p z e) (Finset.mem_univ ⟨(i,j),h⟩)
  · rw [abs_sub_comm]
    exact Finset.single_le_sum (fun e _ => pairPower_nonneg p z e) (Finset.mem_univ ⟨(j,i),h⟩)

lemma pairPower_sum_bound (p : ℝ) (hp : 0 < p) {n : ℕ} (z : Fin n → ℝ)
    (i₀ : Fin n) (hz : z i₀ = 0) (hs : ∑ e, pairPower p z e = 1) :
    ∀ i, |z i| ≤ 1 := by
  intro i
  by_cases hi : i = i₀
  · simp [hi,hz]
  have h := pairPower_pair_le_sum p z i i₀ hi
  rw [hs, hz, sub_zero] at h
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) zero_le_one hp).mp
  simpa using h

def normalizedLabels (p : ℝ) {n : ℕ} (i₀ : Fin n) : Set (Fin n → ℝ) :=
  {z | z i₀ = 0 ∧ ∑ e, pairPower p z e = 1}

def normalizedPowers (p : ℝ) {n : ℕ} (i₀ : Fin n) : Set (PairIndex n → ℝ) :=
  pairPower p '' normalizedLabels p i₀

lemma normalizedLabels_compact (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) :
    IsCompact (normalizedLabels p i₀) := by
  have hc : IsClosed (normalizedLabels p i₀) :=
    (isClosed_eq (continuous_apply i₀) continuous_const).inter
      (isClosed_eq (continuous_finsetSum _ (fun e _ =>
        (continuous_apply e).comp (pairPower_continuous p hp n))) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro z hz
  have h := pairPower_sum_bound p hp z i₀ hz.1 hz.2
  exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

lemma normalizedPowers_compact (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) :
    IsCompact (normalizedPowers p i₀) :=
  (normalizedLabels_compact p hp i₀).image (pairPower_continuous p hp n)

lemma normalizedPowers_sum (p : ℝ) {n : ℕ} (i₀ : Fin n) {v : PairIndex n → ℝ}
    (hv : v ∈ normalizedPowers p i₀) : ∑ e, v e = 1 := by
  obtain ⟨z, hz, rfl⟩ := hv
  exact hz.2

lemma pairPower_smul_sub (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (a b : ℝ) :
    pairPower p (fun i => a * (z i-b)) = |a|^p • pairPower p z := by
  ext e
  simp only [pairPower, Pi.smul_apply, smul_eq_mul]
  rw [show a*(z e.val.1-b)-a*(z e.val.2-b) = a*(z e.val.1-z e.val.2) by ring,
    abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

lemma pairPower_normalize (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) (z : Fin n → ℝ)
    (hs : 0 < ∑ e, pairPower p z e) :
    (∑ e, pairPower p z e)⁻¹ • pairPower p z ∈ normalizedPowers p i₀ := by
  let s := ∑ e, pairPower p z e
  let a := (s⁻¹)^(1/p)
  have ha : 0 < a := Real.rpow_pos_of_pos (inv_pos.mpr hs) _
  have hap : |a|^p = s⁻¹ := by
    rw [abs_of_pos ha]
    dsimp [a]
    rw [one_div]
    exact (Real.rpow_inv_rpow (inv_nonneg.mpr hs.le) hp.ne' :
      (s⁻¹^p⁻¹)^p = s⁻¹)
  refine ⟨(fun i => a*(z i-z i₀)), ⟨by simp, ?_⟩, ?_⟩
  · rw [pairPower_smul_sub, hap]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · rw [pairPower_smul_sub, hap]


lemma lp_norm_rpow_integral (p : ℝ) (hp : 0 < p) {Ω : Type uΩ} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ‖f‖^p = ∫ t, |f t|^p ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.memLp f).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top (Lp.memLp f).aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp only [Real.norm_eq_abs]
  exact Real.rpow_inv_rpow (integral_nonneg (fun t => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne'

lemma lpDifference_integrable (p : ℝ) (hp : 0 < p) {Ω : Type uΩ} [MeasurableSpace Ω]
    {μ : Measure Ω} (f g : Lp ℝ (ENNReal.ofReal p) μ) :
    Integrable (fun t => |f t-g t|^p) μ := by
  have h := ((Lp.memLp f).sub (Lp.memLp g)).norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  rw [memLp_one_iff_integrable] at h
  simpa only [Real.norm_eq_abs, Pi.sub_apply, ENNReal.toReal_ofReal hp.le] using h

lemma lpDifference_integral (p : ℝ) (hp : 0 < p) {Ω : Type uΩ} [MeasurableSpace Ω]
    {μ : Measure Ω} (f g : Lp ℝ (ENNReal.ofReal p) μ) :
    (∫ t, |f t-g t|^p ∂μ) = ‖f-g‖^p := by
  rw [lp_norm_rpow_integral p hp]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with t ht
  rw [ht]
  rfl


lemma pad_coordinates {I : Type uI} (p : ℝ) (hp : 0 < p) {k d : ℕ} (hk : k ≤ d)
    (y : I → Fin k → ℝ) : ∃ Y : I → Fin d → ℝ, ∀ i j,
      (∑ a, |Y i a-Y j a|^p) = ∑ a, |y i a-y j a|^p := by
  induction d, hk using Nat.le_induction with
  | base => exact ⟨y, fun _ _ => rfl⟩
  | succ d hd ih =>
    obtain ⟨Y,hY⟩ := ih
    refine ⟨fun i => Fin.snoc (Y i) 0, ?_⟩
    intro i j
    simpa [Fin.sum_univ_castSucc, Real.zero_rpow hp.ne'] using hY i j

/-- Ball's finite-coordinate isometry, obtained by applying Carathéodory's theorem
to the normalized pairwise `p`th powers. -/
lemma exact_discretization_ge_one (p : ℝ) (hp : 1 ≤ p) (n : ℕ) (hn : 2 ≤ n)
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Fin n → Lp ℝ (ENNReal.ofReal p) μ) (hx : Function.Injective x) :
    ∃ y : Fin n → Fin (n.choose 2) → ℝ, ∀ i j,
      coordinateDistance p (y i) (y j) = ‖x i-x j‖ := by
  classical
  have hp0 : 0 < p := by linarith
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let j₀ : Fin n := ⟨1, by omega⟩
  let e₀ : PairIndex n := ⟨(i₀,j₀), by change (0:ℕ) < 1; omega⟩
  let q : Ω → PairIndex n → ℝ := fun t => pairPower p (fun i => x i t)
  have hqi : Integrable q μ := integrable_pi_iff.mpr (fun e =>
    lpDifference_integrable p hp0 (x e.val.1) (x e.val.2))
  have hqe (e : PairIndex n) : (∫ t, q t e ∂μ) = ‖x e.val.1-x e.val.2‖^p :=
    lpDifference_integral p hp0 _ _
  let S := ∫ t, ∑ e, q t e ∂μ
  have hsum : S = ∑ e : PairIndex n, ‖x e.val.1-x e.val.2‖^p := by
    rw [show S = ∫ t, ∑ e, q t e ∂μ from rfl, integral_finsetSum]
    · exact Finset.sum_congr rfl (fun e _ => hqe e)
    · intro e _; exact integrable_pi_iff.mp hqi e
  have hS : 0 < S := by
    rw [hsum]
    apply Finset.sum_pos'
    · intro e _; positivity
    · refine ⟨e₀, Finset.mem_univ _, Real.rpow_pos_of_pos (norm_pos_iff.mpr ?_) p⟩
      apply sub_ne_zero.mpr
      apply hx.ne
      intro he; have := congrArg Fin.val he; change (0:ℕ) = 1 at this; omega
  have hq : ∀ᵐ t ∂μ, q t = 0 ∨ (0 < ∑ e, q t e ∧ (∑ e, q t e)⁻¹ • q t ∈ normalizedPowers p i₀) := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : ∑ e, q t e = 0
    · left
      ext e
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => pairPower_nonneg p _ e)).mp ht e (Finset.mem_univ e)
    · right
      have htpos : 0 < ∑ e, q t e := lt_of_le_of_ne
        (Finset.sum_nonneg (fun e _ => pairPower_nonneg p _ e)) (Ne.symm ht)
      exact ⟨htpos, pairPower_normalize p hp0 i₀ _ htpos⟩
  have hmem := normalized_integral_mem μ (normalizedPowers_compact p hp0 i₀)
    (fun z hz => normalizedPowers_sum p i₀ hz) q hqi hq hS
  obtain ⟨k,hk,v,w,hv,hw,hws,hvw⟩ := hyperplane_convex_representation
    (fun z hz => normalizedPowers_sum p i₀ hz) hmem
  choose z hz hpz using hv
  let y : Fin n → Fin k → ℝ := fun i a => (S*w a)^(1/p)*z a i
  have hyp (e : PairIndex n) : (∑ a, |y e.val.1 a-y e.val.2 a|^p) = ‖x e.val.1-x e.val.2‖^p := by
    have hwe (a : Fin k) : |y e.val.1 a-y e.val.2 a|^p = S*w a*v a e := by
      have hsw : 0 ≤ S*w a := mul_nonneg hS.le (hw a)
      have ha : 0 ≤ (S*w a)^(1/p) := Real.rpow_nonneg hsw _
      dsimp [y]
      rw [← mul_sub, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_of_nonneg ha,
        one_div, Real.rpow_inv_rpow hsw hp0.ne']
      rw [← hpz a]
      rfl
    simp_rw [hwe]
    have he := congrFun hvw e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
    have hei : (∫ t, q t ∂μ) e = ∫ t, q t e ∂μ :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PairIndex n => ℝ) e).integral_comp_comm hqi).symm
    rw [hei] at he
    rw [hqe] at he
    calc
      ∑ a, S*w a*v a e = S*∑ a, w a*v a e := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = S*(S⁻¹*‖x e.val.1-x e.val.2‖^p) := by rw [he]
      _ = _ := by rw [mul_inv_cancel_left₀ hS.ne']
  have hyy (i j : Fin n) : (∑ a, |y i a-y j a|^p) = ‖x i-x j‖^p := by
    rcases lt_trichotomy i j with h | h | h
    · exact hyp ⟨(i,j),h⟩
    · subst j; simp [Real.zero_rpow hp0.ne']
    · simpa only [abs_sub_comm, norm_sub_rev] using hyp ⟨(j,i),h⟩
  rw [pairIndex_card] at hk
  obtain ⟨Y,hY⟩ := pad_coordinates p hp0 hk y
  refine ⟨Y, ?_⟩
  intro i j
  unfold coordinateDistance
  rw [hY, hyy, one_div, Real.rpow_rpow_inv (norm_nonneg _) hp0.ne']

lemma exact_discretization (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n)
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Fin n → Lp ℝ (ENNReal.ofReal p) μ) (hx : Function.Injective x) :
    ∃ y : Fin n → Fin (n.choose 2) → ℝ, ∀ i j,
      coordinateDistance p (y i) (y j) = ‖x i-x j‖ :=
  exact_discretization_ge_one p hp.le n hn μ x hx

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal

namespace SubpolynomialLp

open Metric Module Set
open scoped ENNReal
lemma packing_card_bound {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) (R : ℝ) (hR : 0 ≤ R)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R) (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (1+2*R)^finrank ℝ E := by
  classical
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1/2
  let ρ : ℝ := R+1/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let A := ⋃ c ∈ s, ball c δ
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert h c hc d hd hcd using 1; norm_num [δ]
  have hA : A ⊆ ball (0:E) ρ := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    dsimp [δ,ρ]
    linarith [hs c hc]
  have hi : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^finrank ℝ E)*μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^finrank ℝ E)*μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball c δ from rfl, measure_biUnion_finset hd (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ (show 0 < δ by norm_num [δ]), Finset.sum_const,
          nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0:E) ρ) := measure_mono hA
      _ = _ := μ.addHaar_ball_of_pos 0 hρ
  have hj : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^finrank ℝ E) ≤ ENNReal.ofReal (ρ^finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).mp hi
  have hr : (s.card : ℝ)*δ^finrank ℝ E ≤ ρ^finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal
      (pow_nonneg (by norm_num [δ] : 0 ≤ δ) (finrank ℝ E))] using ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hj
  have hr := (le_div_iff₀ (pow_pos (by norm_num [δ] : 0 < δ) (finrank ℝ E))).mpr hr
  rw [← div_pow] at hr
  have he : ρ/δ = 1+2*R := by dsimp [ρ,δ]; ring
  rwa [he] at hr

lemma packing_family_bound {E : Type uE} {I : Type uI} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype I] (f : I → E) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ i, ‖f i‖ ≤ R) (hsep : ∀ i j, i ≠ j → 1 ≤ ‖f i-f j‖) :
    (Fintype.card I : ℝ) ≤ (1+2*R)^finrank ℝ E := by
  classical
  have hinj : Function.Injective f := by
    intro i j he
    by_contra h
    have := hsep i j h
    simp only [he, sub_self, norm_zero] at this
    linarith
  have hh := packing_card_bound (Finset.univ.image f) R hR
    (by simpa using hf) (by
      intro c hc d hd hcd
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
      exact hsep i j (fun he => hcd (congrArg f he)))
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using hh


lemma coordinateDistance_norm (p : ℝ) (hp : 0 < p) {d : ℕ} (x y : Fin d → ℝ) :
    coordinateDistance p x y =
      ‖WithLp.toLp (ENNReal.ofReal p) x - WithLp.toLp (ENNReal.ofReal p) y‖ := by
  rw [← WithLp.toLp_sub, PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp only [Pi.sub_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le]
  rfl

lemma equilateral_lp (p : ℝ) (hp : 0 < p) (n : ℕ) :
    ∃ x : Fin n → Lp ℝ (ENNReal.ofReal p) (Measure.count : Measure (ULift.{u} (Fin n))),
      Function.Injective x ∧ ∀ i j, i ≠ j → ‖x i-x j‖ = (2:ℝ)^(1/p) := by
  classical
  let f : Fin n → ULift.{u} (Fin n) → ℝ := fun i z => if z.down = i then 1 else 0
  refine ⟨fun i => finiteToLp p (f i), ?_, ?_⟩
  · intro i j he
    have h := congrFun (finiteToLp_injective p he) (ULift.up i)
    by_contra hij
    simp [f, hij] at h
  · intro i j hij
    rw [← finiteToLp_sub, finiteToLp_norm p hp]
    have hterm (z : ULift.{u} (Fin n)) : |(f i-f j) z|^p =
        (if z.down = i then 1 else 0) + (if z.down = j then 1 else 0) := by
      by_cases hi : z.down = i <;> by_cases hj : z.down = j
      · exact (hij (hi.symm.trans hj)).elim
      all_goals simp [f, Pi.sub_apply, hi, hj, hij, Ne.symm hij, Real.zero_rpow hp.ne']
    simp_rw [hterm, Finset.sum_add_distrib]
    have hi : (∑ z : ULift.{u} (Fin n), if z.down = i then (1:ℝ) else 0) = 1 := by
      rw [← (Equiv.ulift.symm).sum_comp]
      simp
    have hj : (∑ z : ULift.{u} (Fin n), if z.down = j then (1:ℝ) else 0) = 1 := by
      rw [← (Equiv.ulift.symm).sum_comp]
      simp
    rw [hi,hj]; norm_num

lemma packing_lower_of_goodDimension (p : ℝ) (hp : 1 < p) (n d : ℕ) (hn : 2 ≤ n)
    (D : ℝ) (hD : 1 ≤ D) (hgood : GoodDimension.{u} p n D d) :
    Real.log (n:ℝ) / Real.log (1+2*D) ≤ d := by
  classical
  have hp0 : 0 < p := by linarith
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨x,hx,hxe⟩ := equilateral_lp.{u} p hp0 n
  obtain ⟨y,s,hs,hys⟩ := hgood _ _ _ x hx
  let Y : Fin n → PiLp (ENNReal.ofReal p) (fun _ : Fin d => ℝ) :=
    fun i => WithLp.toLp _ (y i)
  let r := s*(2:ℝ)^(1/p)
  have hr : 0 < r := mul_pos hs (Real.rpow_pos_of_pos (by norm_num) _)
  let i₀ : Fin n := ⟨0,by omega⟩
  let Z := fun i => r⁻¹ • (Y i-Y i₀)
  have hnorm (i j : Fin n) : ‖Z i-Z j‖ = r⁻¹ * coordinateDistance p (y i) (y j) := by
    simp only [Z, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), coordinateDistance_norm p hp0]
    rfl
  have hZ (i : Fin n) : ‖Z i‖ ≤ D := by
    by_cases hi : i = i₀
    · subst i; simp [Z]; linarith
    have hb := (hys i i₀).2
    rw [hxe i i₀ hi] at hb
    have hz : Z i₀ = 0 := by simp [Z]
    rw [← sub_zero (Z i), ← hz, hnorm]
    apply (inv_mul_le_iff₀ hr).mpr
    simpa only [r, mul_assoc, mul_left_comm, mul_comm] using hb
  have hsep (i j : Fin n) (hij : i ≠ j) : 1 ≤ ‖Z i-Z j‖ := by
    rw [hnorm]
    apply (le_inv_mul_iff₀ hr).mpr
    simpa only [mul_one, r, hxe i j hij] using (hys i j).1
  have hcard := packing_family_bound Z D (by linarith) hZ hsep
  have hdim : finrank ℝ (PiLp (ENNReal.ofReal p) (fun _ : Fin d => ℝ)) = d := by
    rw [(WithLp.linearEquiv (ENNReal.ofReal p) ℝ (Fin d → ℝ)).finrank_eq]
    simp
  simp only [Fintype.card_fin, hdim] at hcard
  have hbase : 1 < 1+2*D := by linarith
  have hnpos : 0 < (n:ℝ) := by positivity
  have hl := Real.log_le_log hnpos hcard
  rw [Real.log_pow] at hl
  exact (div_le_iff₀ (Real.log_pos hbase)).mpr hl


lemma exact_goodDimension (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n) :
    GoodDimension.{u} p n 1 (n.choose 2) := by
  intro Ω mΩ μ x hx
  obtain ⟨y,hy⟩ := exact_discretization p hp n hn μ x hx
  refine ⟨y, 1, zero_lt_one, ?_⟩
  intro i j
  simp [hy]

lemma GoodDimension.mono_distortion {p D D' : ℝ} {n d : ℕ}
    (h : GoodDimension.{u} p n D d) (hDD : D ≤ D') : GoodDimension.{u} p n D' d := by
  intro Ω mΩ μ x hx
  obtain ⟨y,s,hs,hy⟩ := h Ω mΩ μ x hx
  refine ⟨y,s,hs,fun i j => ⟨(hy i j).1, (hy i j).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD hs.le) (by rw [Lp.norm_def]; exact ENNReal.toReal_nonneg)

lemma dimension_good (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 1 ≤ D) :
    GoodDimension.{u} p n D (dimension.{u} p n D) := by
  apply Nat.sInf_mem (s := {d : ℕ | GoodDimension.{u} p n D d})
  exact ⟨n.choose 2, (exact_goodDimension p hp n hn).mono_distortion hD⟩

lemma dimension_le_exact (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 1 ≤ D) :
    dimension.{u} p n D ≤ n.choose 2 := by
  exact Nat.sInf_le ((exact_goodDimension p hp n hn).mono_distortion hD)


lemma exact_dimension_bounds (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (n : ℕ) (hn : 9 ≤ n) :
    GoodDimension.{u} p n 1 (dimension.{u} p n 1) ∧
      ((n-1)/4)^2 ≤ dimension.{u} p n 1 ∧ dimension.{u} p n 1 ≤ n.choose 2 := by
  have hg := dimension_good.{u} p hp n (by omega) 1 le_rfl
  exact ⟨hg, exact_lower_of_goodDimension p hp hp2 n _ hn hg,
    dimension_le_exact p hp n (by omega) 1 le_rfl⟩

lemma quadratic_growth_log_limit (f : ℕ → ℕ)
    (hlo : ∀ᶠ n in atTop, ((n-1)/4)^2 ≤ f n)
    (hhi : ∀ᶠ n in atTop, f n ≤ n^2) :
    Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log (n:ℝ)) atTop (𝓝 2) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => 2 - (2*Real.log 8)/Real.log (n:ℝ)) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.sub (hlog.const_div_atTop (2*Real.log 8))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [hlo, Filter.eventually_ge_atTop 9] with n hlo hn
    have hquad : (n:ℝ)^2 / 64 ≤ f n := by
      have hdiv : n ≤ 8*((n-1)/4) := by omega
      have hdivR : (n:ℝ) ≤ 8*((n-1)/4:ℕ) := by exact_mod_cast hdiv
      have hloR : (((n-1)/4:ℕ):ℝ)^2 ≤ f n := by exact_mod_cast hlo
      have hn0 : (0:ℝ) ≤ n := by positivity
      have hk0 : (0:ℝ) ≤ ((n-1)/4:ℕ) := by positivity
      nlinarith
    have hnpos : (0:ℝ) < n := by positivity
    have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hqpos : 0 < (n:ℝ)^2/64 := by positivity
    have hb := Real.log_le_log hqpos hquad
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hb
    have h64 : Real.log 64 = 2*Real.log 8 := by
      have := Real.log_pow (8:ℝ) 2
      norm_num at this
      exact this
    rw [h64] at hb
    apply (le_div_iff₀ (Real.log_pos hn1)).mpr
    rw [sub_mul, div_mul_cancel₀ _ (Real.log_pos hn1).ne']
    exact_mod_cast hb
  · filter_upwards [hlo, hhi, Filter.eventually_ge_atTop 9] with n hlo hhi hn
    have hfn : 0 < f n := by
      have hk : 0 < (n-1)/4 := by omega
      have := pow_pos hk 2
      omega
    have hfnR : (0:ℝ) < f n := by exact_mod_cast hfn
    have hb := Real.log_le_log hfnR (show (f n:ℝ) ≤ (n:ℝ)^2 by exact_mod_cast hhi)
    rw [Real.log_pow] at hb
    apply (div_le_iff₀ (Real.log_pos (show (1:ℝ) < n by exact_mod_cast (show 1 < n by omega)))).mpr
    exact hb


lemma exact_dimension_log_limit (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) :
    Tendsto (fun n : ℕ => Real.log (dimension.{u} p n 1 : ℝ) / Real.log (n:ℝ))
      atTop (𝓝 2) := by
  apply quadratic_growth_log_limit
  · filter_upwards [Filter.eventually_ge_atTop 9] with n hn
    exact (exact_dimension_bounds p hp hp2 n hn).2.1
  · filter_upwards [Filter.eventually_ge_atTop 9] with n hn
    apply (exact_dimension_bounds p hp hp2 n hn).2.2.trans
    rw [Nat.choose_two_right, pow_two]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left n (Nat.sub_le _ _))

lemma dimension_packing_lower (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n)
    (D : ℝ) (hD : 1 ≤ D) :
    Real.log (n:ℝ) / Real.log (1+2*D) ≤ (dimension.{u} p n D:ℝ) := by
  exact packing_lower_of_goodDimension p hp n _ hn D hD (dimension_good p hp n hn D hD)

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal

namespace SubpolynomialLp

section HilbertMatrix
variable {E : Type uE} {H : Type uH} [Fintype E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def hilbertMul (P : Matrix E E ℝ) (x : E → H) (e : E) : H := ∑ f, P e f • x f

lemma hilbertMul_add (P Q : Matrix E E ℝ) (x : E → H) :
    hilbertMul (P+Q) x = hilbertMul P x+hilbertMul Q x := by
  ext e
  simp [hilbertMul, add_smul, Finset.sum_add_distrib]

lemma hilbertMul_smul (a : ℝ) (P : Matrix E E ℝ) (x : E → H) :
    hilbertMul (a • P) x = a • hilbertMul P x := by
  ext e
  simp [hilbertMul, Finset.smul_sum, smul_smul]

lemma hilbertMul_mul (P Q : Matrix E E ℝ) (x : E → H) :
    hilbertMul (P*Q) x = hilbertMul P (hilbertMul Q x) := by
  ext e
  simp only [hilbertMul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

lemma hilbertMul_inner (P : Matrix E E ℝ) (x y : E → H) :
    (∑ e, inner ℝ (hilbertMul P x e) (y e)) = ∑ e, inner ℝ (x e) (hilbertMul P.transpose y e) := by
  simp only [hilbertMul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma hilbertMul_contraction (P : Matrix E E ℝ) (hs : P.IsSymm) (hi : P*P=P)
    (x : E → H) : (∑ e, ‖hilbertMul P x e‖^2) ≤ ∑ e, ‖x e‖^2 := by
  have hp : ∑ e, inner ℝ (hilbertMul P x e) (hilbertMul P x e) =
      ∑ e, inner ℝ (x e) (hilbertMul P x e) := by
    rw [hilbertMul_inner, hs.eq, ← hilbertMul_mul, hi]
  have hnon : 0 ≤ ∑ e, ‖x e-hilbertMul P x e‖^2 := by positivity
  have he : (∑ e, ‖x e-hilbertMul P x e‖^2) =
      (∑ e, ‖x e‖^2) - (∑ e, ‖hilbertMul P x e‖^2) := by
    simp_rw [norm_sub_sq_real]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hp' : ∑ e, ‖hilbertMul P x e‖^2 = ∑ e, inner ℝ (x e) (hilbertMul P x e) := by
      simpa only [real_inner_self_eq_norm_sq] using hp
    linarith
  rw [he] at hnon
  linarith

end HilbertMatrix


lemma weighted_error_to_uniform {E : Type uE} [Fintype E] [Nonempty E]
    {C : Set (E → ℝ)} (hC : Convex ℝ C) (b ε : ℝ) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ m ∈ C, (∑ e, w e * |m e-b|) ≤ ε) :
    ∃ m ∈ C, ∀ e, |m e-b| < 2*ε := by
  classical
  let B : Set (E → ℝ) := Metric.ball (fun _ => b) (2*ε)
  have hB : Convex ℝ B := convex_ball _ _
  have hBc : (fun _ : E => b) ∈ B := Metric.mem_ball_self (by positivity)
  have hBu : ∀ z, z ∈ B ↔ ∀ e, |z e-b| < 2*ε := by
    intro z
    simp only [B, Metric.mem_ball, dist_pi_lt_iff (show 0 < 2*ε by positivity), Real.dist_eq]
  by_contra hnot
  have hd : Disjoint B C := by
    apply Set.disjoint_left.mpr
    intro m hm hmC
    exact hnot ⟨m,hmC,(hBu m).mp hm⟩
  obtain ⟨f,u,hfB,hfC⟩ := geometric_hahn_banach_open hB Metric.isOpen_ball hC hd
  let a : E → ℝ := fun e => f (Pi.single e 1)
  have hrepr (z : E → ℝ) : f z = ∑ e, a e*z e := by
    have he : z = ∑ e : E, z e • Pi.single e (1:ℝ) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [he, map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_smul, smul_eq_mul]
    dsimp [a]
    ring
  let S := ∑ e, |a e|
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcard : 0 < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw0 : ∀ e : E, 0 < (Fintype.card E : ℝ)⁻¹ := fun _ => inv_pos.mpr hcard
  have hsum0 : (∑ _ : E, (Fintype.card E:ℝ)⁻¹) = 1 := by
    simp [hcard.ne']
  obtain ⟨m₀,hm₀,_⟩ := hw (fun _ => (Fintype.card E:ℝ)⁻¹) hw0 hsum0
  have hS : 0 < S := by
    by_contra h
    have hz : S = 0 := le_antisymm (not_lt.mp h) hS0
    have haz (e : E) : a e = 0 := abs_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun e _ => abs_nonneg (a e))).mp hz e (Finset.mem_univ e))
    have hh := hfB _ hBc
    have hj := hfC _ hm₀
    simp only [hrepr, haz, zero_mul, Finset.sum_const_zero] at hh hj
    linarith
  let w : E → ℝ := fun e => 3/4*(|a e|/S)+1/(4*(Fintype.card E))
  have hwpos : ∀ e, 0 < w e := by intro e; dsimp [w]; positivity
  have hwsum : ∑ e, w e = 1 := by
    simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [div_self hS.ne']
    field_simp [hcard.ne']
    ring
  obtain ⟨m,hm,herr⟩ := hw w hwpos hwsum
  have hal (e : E) : |a e| ≤ (4/3)*S*w e := by
    have he : (4/3)*S*w e = |a e|+S/(3*(Fintype.card E)) := by
      dsimp [w]
      field_simp [hS.ne', hcard.ne']
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  have hferr : f m-f (fun _ => b) ≤ (4/3)*S*ε := by
    rw [hrepr, hrepr, ← Finset.sum_sub_distrib]
    calc
      ∑ e, (a e*m e-a e*b) ≤ ∑ e, |a e| *|m e-b| := by
        apply Finset.sum_le_sum
        intro e _
        calc
          _ = a e*(m e-b) := by ring
          _ ≤ |a e*(m e-b)| := le_abs_self _
          _ = _ := abs_mul _ _
      _ ≤ ∑ e, ((4/3)*S*w e)*|m e-b| :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (hal e) (abs_nonneg _))
      _ = (4/3)*S*∑ e, w e*|m e-b| := by simp only [Finset.mul_sum, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left herr (by positivity)
  let z : E → ℝ := fun e => b+(3/2)*ε*SignType.sign (a e)
  have hzB : z ∈ B := by
    apply (hBu z).mpr
    intro e
    dsimp [z]
    rcases lt_trichotomy (a e) 0 with h | h | h
    · simp [sign_neg h, abs_of_pos hε]; linarith
    · simp [h]; positivity
    · simp [sign_pos h, abs_of_pos hε]; linarith
  have hzf : f z-f (fun _ => b) = (3/2)*ε*S := by
    rw [hrepr, hrepr, ← Finset.sum_sub_distrib]
    calc
      ∑ e, (a e*z e-a e*b) = ∑ e, (3/2)*ε*|a e| := by
        apply Finset.sum_congr rfl
        intro e _
        dsimp [z]
        rcases lt_trichotomy (a e) 0 with h | h | h
        · rw [sign_neg h, abs_of_neg h]; norm_num; ring
        · simp [h]
        · rw [sign_pos h, abs_of_pos h]; norm_num; ring
      _ = _ := by rw [← Finset.mul_sum]
  have hfz := hfB z hzB
  have hfm := hfC m hm
  nlinarith


/-- Convex separation replaces fixed-point reweighting. -/
lemma convex_cost_selection {X : Type uX} {E : Type uE} [AddCommGroup X] [Module ℝ X]
    [Fintype E] [Nonempty E] {A : Set X} (hA : Convex ℝ A)
    (c : E → X → ℝ) (hc : ∀ e, ConvexOn ℝ A (c e))
    (hcn : ∀ e x, x ∈ A → 0 ≤ c e x) (B : ℝ) (hB : 0 < B)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ x ∈ A, (∑ e, w e*c e x) ≤ B) :
    ∃ x ∈ A, ∀ e, c e x < 2*B := by
  classical
  let C : Set (E → ℝ) := {v | ∃ x ∈ A, ∀ e, c e x ≤ v e}
  have hC : Convex ℝ C := by
    intro v hv z hz a b ha hb hab
    obtain ⟨x,hx,hcx⟩ := hv
    obtain ⟨y,hy,hcy⟩ := hz
    refine ⟨a • x+b • y,hA hx hy ha hb hab,fun e => ?_⟩
    exact ((hc e).2 hx hy ha hb hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hcx e) ha) (mul_le_mul_of_nonneg_left (hcy e) hb))
  have hwt : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ m ∈ C, (∑ e, w e*|m e-(0:ℝ)|) ≤ B := by
    intro w hwp hws
    obtain ⟨x,hx,hxc⟩ := hw w hwp hws
    refine ⟨fun e => c e x,⟨x,hx,fun _ => le_rfl⟩,?_⟩
    simpa only [sub_zero, abs_of_nonneg (hcn _ _ hx)] using hxc
  obtain ⟨v,⟨x,hx,hxv⟩,hve⟩ := weighted_error_to_uniform hC 0 B hB hwt
  refine ⟨x,hx,fun e => (hxv e).trans_lt ?_⟩
  exact (le_abs_self (v e)).trans_lt (by simpa using hve e)


lemma simultaneous_convex_cost_selection {X : Type uX} {E : Type uE} {J : Type uJ}
    [AddCommGroup X] [Module ℝ X] [Fintype E] [Nonempty E] [Fintype J]
    {A : Set X} (hA : Convex ℝ A) (r : E → X → ℝ) (q : J → X → ℝ)
    (hrc : ∀ e, ConvexOn ℝ A (r e)) (hqc : ∀ j, ConvexOn ℝ A (q j))
    (hrn : ∀ e x, x ∈ A → 0 ≤ r e x) (hqn : ∀ j x, x ∈ A → 0 ≤ q j x)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ x ∈ A, (∑ e, w e*r e x) ≤ 2 ∧ ∀ j, q j x ≤ 2) :
    ∃ x ∈ A, (∀ e, r e x < 4) ∧ ∀ j, q j x < 4 := by
  classical
  let c : E ⊕ J → X → ℝ := Sum.elim r q
  have hc : ∀ i, ConvexOn ℝ A (c i) := by intro i; cases i with
    | inl e => exact hrc e
    | inr j => exact hqc j
  have hcn : ∀ i x, x ∈ A → 0 ≤ c i x := by intro i; cases i with
    | inl e => exact hrn e
    | inr j => exact hqn j
  have hwt : ∀ w : E ⊕ J → ℝ, (∀ i, 0 < w i) → (∑ i, w i) = 1 →
      ∃ x ∈ A, (∑ i, w i*c i x) ≤ 2 := by
    intro w hwp hws
    let a := ∑ e, w (Sum.inl e)
    have ha : 0 < a := Finset.sum_pos (fun e _ => hwp (Sum.inl e)) Finset.univ_nonempty
    have hvs : ∑ e, w (Sum.inl e)/a = 1 := by rw [← Finset.sum_div, div_self ha.ne']
    obtain ⟨x,hx,hxr,hxq⟩ := hw (fun e => w (Sum.inl e)/a)
      (fun e => div_pos (hwp _) ha) hvs
    have hxr' : ∑ e, w (Sum.inl e)*r e x ≤ 2*a := by
      have he : ∑ e, w (Sum.inl e)/a*r e x = (∑ e, w (Sum.inl e)*r e x)/a := by
        simp only [div_mul_eq_mul_div, Finset.sum_div]
      rw [he] at hxr
      exact (div_le_iff₀ ha).mp hxr
    have hxq' : ∑ j, w (Sum.inr j)*q j x ≤ 2*(∑ j, w (Sum.inr j)) := by
      calc
        _ ≤ ∑ j, w (Sum.inr j)*2 := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hxq j) (hwp _).le)
        _ = _ := by rw [← Finset.sum_mul]; ring
    refine ⟨x,hx,?_⟩
    rw [Fintype.sum_sum_type] at hws ⊢
    dsimp [c]
    change a+(∑ j, w (Sum.inr j))=1 at hws
    linarith
  obtain ⟨x,hx,hxc⟩ := convex_cost_selection hA c hc hcn 2 (by norm_num) hwt
  refine ⟨x,hx,fun e => ?_,fun j => ?_⟩
  · have hh := hxc (Sum.inl e)
    change r e x < 2*2 at hh
    linarith
  · have hh := hxc (Sum.inr j)
    change q j x < 2*2 at hh
    linarith

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal

namespace SubpolynomialLp

section WeightedProjection
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

def weightedProjection (A : Matrix E V ℝ) (σ : E → ℝ) : Matrix E E ℝ :=
  diagonal (fun e => (Real.sqrt (σ e))⁻¹) *
    gramProjection (diagonal (fun e => Real.sqrt (σ e)) * A) *
    diagonal (fun e => Real.sqrt (σ e))

def retractions (A : Matrix E V ℝ) : Set (Matrix E E ℝ) :=
  {P | P*A=A ∧ ∃ B : Matrix V E ℝ, P=A*B}

omit [DecidableEq E] [DecidableEq V] in
lemma retractions_convex (A : Matrix E V ℝ) : Convex ℝ (retractions A) := by
  intro P hP Q hQ a b ha hb hab
  rcases hP with ⟨hPA,B,rfl⟩
  rcases hQ with ⟨hQA,C,rfl⟩
  constructor
  · rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hPA, hQA,
      ← add_smul, hab, one_smul]
  · refine ⟨a • B+b • C, ?_⟩
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]

omit [DecidableEq E] in
lemma gramProjection_factor (A : Matrix E V ℝ) :
    ∃ B : Matrix V E ℝ, gramProjection A = A*B := by
  refine ⟨((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ) *
    diagonal (fun i => ((gramHermitian A).eigenvalues i)⁻¹) *
    (gramEigenMatrix A).transpose, ?_⟩
  simp only [gramProjection, gramEigenMatrix, Matrix.mul_assoc]

lemma sqrt_diagonal_inv (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) :
    diagonal (fun e => (Real.sqrt (σ e))⁻¹) * diagonal (fun e => Real.sqrt (σ e)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (Real.sqrt_pos.2 (hσ _)).ne']
  exact diagonal_one

lemma weightedProjection_mem (A : Matrix E V ℝ) (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) :
    weightedProjection A σ ∈ retractions A := by
  let D := diagonal (fun e => Real.sqrt (σ e))
  let Di := diagonal (fun e => (Real.sqrt (σ e))⁻¹)
  have hDi : Di*D=1 := sqrt_diagonal_inv σ hσ
  have hf := gramProjection_mul_self (D*A)
  constructor
  · change Di*gramProjection (D*A)*D*A=A
    calc
      _ = Di*(gramProjection (D*A)*(D*A)) := by simp only [Matrix.mul_assoc]
      _ = Di*(D*A) := by rw [hf]
      _ = A := by rw [← Matrix.mul_assoc, hDi, Matrix.one_mul]
  · obtain ⟨B,hB⟩ := gramProjection_factor (D*A)
    refine ⟨B*D, ?_⟩
    change Di*gramProjection (D*A)*D=A*(B*D)
    rw [hB]
    calc
      _ = (Di*D)*A*(B*D) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDi, Matrix.one_mul]

lemma hilbertMul_diagonal {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (d : E → ℝ) (x : E → H) (e : E) : hilbertMul (diagonal d) x e = d e • x e := by
  simp [hilbertMul, Matrix.diagonal_apply]

lemma weightedProjection_energy {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Matrix E V ℝ) (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) (x : E → H) :
    (∑ e, σ e * ‖hilbertMul (weightedProjection A σ) x e‖^2) ≤
      ∑ e, σ e * ‖x e‖^2 := by
  let D := diagonal (fun e => Real.sqrt (σ e))
  let Di := diagonal (fun e => (Real.sqrt (σ e))⁻¹)
  let Q := gramProjection (D*A)
  have hDD : D*Di=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (Real.sqrt_pos.2 (hσ _)).ne']
    exact diagonal_one
  have hP : D*weightedProjection A σ=Q*D := by
    change D*(Di*Q*D)=Q*D
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have hen (y : E → H) : (∑ e, ‖hilbertMul D y e‖^2) = ∑ e, σ e*‖y e‖^2 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [hilbertMul_diagonal, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (hσ e)), mul_pow, Real.sq_sqrt (hσ e).le]
  have hc := hilbertMul_contraction Q (gramProjection_symmetric _) (gramProjection_idempotent _)
    (hilbertMul D x)
  rw [← hilbertMul_mul, ← hP, hilbertMul_mul, hen, hen] at hc
  exact hc


def matrixRowNorm (P : Matrix E E ℝ) (e : E) : ℝ := ∑ f, |P e f|

omit [DecidableEq E] in
lemma matrixRowNorm_nonneg (P : Matrix E E ℝ) (e : E) : 0 ≤ matrixRowNorm P e := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [DecidableEq E] [DecidableEq V] in
lemma matrixRowNorm_convex (A : Matrix E V ℝ) (e : E) :
    ConvexOn ℝ (retractions A) (fun P => matrixRowNorm P e) := by
  refine ⟨retractions_convex A, ?_⟩
  intro P hP Q hQ a b ha hb hab
  change (∑ f, |a*P e f+b*Q e f|) ≤ a*(∑ f, |P e f|)+b*(∑ f, |Q e f|)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f _
  simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a*P e f) (b*Q e f)

omit [DecidableEq E] [DecidableEq V] in
lemma projectionEnergy_convex {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Matrix E V ℝ) (lam : E → ℝ) (hlam : ∀ e, 0 ≤ lam e) (x : E → H) :
    ConvexOn ℝ (retractions A) (fun P => ∑ e, lam e * ‖hilbertMul P x e‖^2) := by
  refine ⟨retractions_convex A, ?_⟩
  intro P hP Q hQ a b ha hb hab
  have hn := (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set H))).pow
    (fun _ _ => norm_nonneg _) 2
  simp only [hilbertMul_add, hilbertMul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have hh := hn.2 (Set.mem_univ (hilbertMul P x e)) (Set.mem_univ (hilbertMul Q x e)) ha hb hab
  change ‖a • hilbertMul P x e+b • hilbertMul Q x e‖^2 ≤
    a*‖hilbertMul P x e‖^2+b*‖hilbertMul Q x e‖^2 at hh
  calc
    _ ≤ lam e*(a*‖hilbertMul P x e‖^2+b*‖hilbertMul Q x e‖^2) :=
      mul_le_mul_of_nonneg_left hh (hlam e)
    _ = _ := by ring

def normalizedGradient (src dst : E → V) (δ : E → ℝ) : Matrix E V ℝ :=
  diagonal (fun e => (δ e)⁻¹) * incidence src dst

omit [Fintype V] in
lemma scaled_normalizedGradient (src dst : E → V) (δ σ : E → ℝ)
    (hδ : ∀ e, 0 < δ e) (hσ : ∀ e, 0 < σ e) :
    diagonal (fun e => Real.sqrt (σ e)) * normalizedGradient src dst δ =
      conductorMatrix src dst (fun e => σ e/(δ e)^2) := by
  unfold normalizedGradient conductorMatrix
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 1
  congr 1
  funext e
  rw [Real.sqrt_div (hσ e).le, Real.sqrt_sq (hδ e).le]
  rfl

lemma weightedProjection_rows (src dst : E → V) (δ σ : E → ℝ)
    (hδ : ∀ e, 0 < δ e) (hσ : ∀ e, 0 < σ e) (hsum : ∑ e, σ e = 1)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    (∑ e, σ e * (matrixRowNorm (weightedProjection (normalizedGradient src dst δ) σ) e)^2) ≤
      (2*Real.log (Fintype.card V : ℝ))^2 := by
  let A := normalizedGradient src dst δ
  let Q := gramProjection (conductorMatrix src dst (fun e => σ e/(δ e)^2))
  have hP (e f : E) : weightedProjection A σ e f =
      (Real.sqrt (σ e))⁻¹*Q e f*Real.sqrt (σ f) := by
    simp only [weightedProjection, A, scaled_normalizedGradient src dst δ σ hδ hσ,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Q]
  have hrow (e : E) : Real.sqrt (σ e)*matrixRowNorm (weightedProjection A σ) e =
      ∑ f, |Q e f| *Real.sqrt (σ f) := by
    unfold matrixRowNorm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [hP, abs_mul, abs_mul, abs_inv, abs_of_pos (Real.sqrt_pos.2 (hσ e)),
      abs_of_pos (Real.sqrt_pos.2 (hσ f))]
    field_simp [(Real.sqrt_pos.2 (hσ e)).ne']
  have hh := electrical_localization_complete src dst (fun e => σ e/(δ e)^2)
    (fun e => Real.sqrt (σ e)) (fun e => div_pos (hσ e) (sq_pos_of_pos (hδ e))) hinc hconn
  simp only [Real.sq_sqrt (hσ _).le, hsum, mul_one] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro e _
  rw [← hrow, mul_pow, Real.sq_sqrt (hσ e).le]


/-- A simultaneous retraction substitute for the fixed-point reweighting:
it supplies the exact row bound and all finitely many tensor-energy bounds
needed by the two constructions. -/
lemma controlled_retraction {J : Type uJ} {H : Type uH} [Fintype J] [Nonempty E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (x : J → E → H) (hx : ∀ j e, ‖x j e‖^2 ≤ 1) :
    ∃ P ∈ retractions (normalizedGradient src dst δ),
      (∀ e, matrixRowNorm P e ≤ 4*Real.log (Fintype.card V : ℝ)) ∧
      (∀ j, (∑ e, lam e * ‖hilbertMul P (x j) e‖^2) ≤ 4) := by
  let A := normalizedGradient src dst δ
  let L := 2*Real.log (Fintype.card V : ℝ)
  have hL : 0 < L := by
    have : (1:ℝ) < Fintype.card V := by exact_mod_cast (show 1 < Fintype.card V by omega)
    exact mul_pos (by norm_num) (Real.log_pos this)
  let r (e : E) (P : Matrix E E ℝ) := (matrixRowNorm P e)^2/L^2
  let q (j : J) (P : Matrix E E ℝ) := ∑ e, lam e*‖hilbertMul P (x j) e‖^2
  have hrc (e : E) : ConvexOn ℝ (retractions A) (r e) := by
    have hh := ((matrixRowNorm_convex A e).pow (fun P _ => matrixRowNorm_nonneg P e) 2).smul
      (show 0 ≤ (L^2)⁻¹ by positivity)
    simpa only [r, Pi.pow_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh
  have hqc (j : J) : ConvexOn ℝ (retractions A) (q j) :=
    projectionEnergy_convex A lam (fun e => (hlam e).le) (x j)
  have hrn (e : E) (P : Matrix E E ℝ) (_hP : P ∈ retractions A) : 0 ≤ r e P := by
    dsimp [r]; positivity
  have hqn (j : J) (P : Matrix E E ℝ) (_hP : P ∈ retractions A) : 0 ≤ q j P := by
    exact Finset.sum_nonneg (fun e _ => mul_nonneg (hlam e).le (sq_nonneg _))
  have htest : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ P ∈ retractions A, (∑ e, w e*r e P) ≤ 2 ∧ ∀ j, q j P ≤ 2 := by
    intro w hw hws
    let σ (e : E) := (lam e+w e)/2
    have hσ (e : E) : 0 < σ e := div_pos (add_pos (hlam e) (hw e)) (by norm_num)
    have hσs : ∑ e, σ e=1 := by simp only [σ, ← Finset.sum_div, Finset.sum_add_distrib, hls, hws]; norm_num
    have hlσ (e : E) : lam e ≤ 2*σ e := by dsimp [σ]; linarith [hw e]
    have hwσ (e : E) : w e ≤ 2*σ e := by dsimp [σ]; linarith [hlam e]
    let P := weightedProjection A σ
    refine ⟨P, weightedProjection_mem A σ hσ, ?_, ?_⟩
    · have hh := weightedProjection_rows src dst δ σ hδ hσ hσs hinc hconn
      change (∑ e, σ e*(matrixRowNorm P e)^2) ≤ L^2 at hh
      have hnum : (∑ e, w e*(matrixRowNorm P e)^2) ≤ 2*L^2 := by
        calc
          _ ≤ ∑ e, (2*σ e)*(matrixRowNorm P e)^2 := Finset.sum_le_sum (fun e _ =>
            mul_le_mul_of_nonneg_right (hwσ e) (sq_nonneg _))
          _ = 2*∑ e, σ e*(matrixRowNorm P e)^2 := by simp only [mul_assoc, Finset.mul_sum]
          _ ≤ 2*L^2 := by linarith
      have he : (∑ e, w e*r e P) = (∑ e, w e*(matrixRowNorm P e)^2)/L^2 := by
        simp only [r, mul_div_assoc, Finset.sum_div]
      rw [he]
      exact (div_le_iff₀ (sq_pos_of_pos hL)).2 hnum
    · intro j
      change (∑ e, lam e*‖hilbertMul P (x j) e‖^2) ≤ 2
      calc
        _ ≤ 2*∑ e, σ e*‖hilbertMul P (x j) e‖^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro e _
          nlinarith [mul_le_mul_of_nonneg_right (hlσ e) (sq_nonneg ‖hilbertMul P (x j) e‖)]
        _ ≤ 2*∑ e, σ e*‖x j e‖^2 := by
          exact mul_le_mul_of_nonneg_left (weightedProjection_energy A σ hσ (x j)) (by norm_num)
        _ ≤ 2*∑ e, σ e*1 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hx j e) (hσ e).le)
        _ = 2 := by simp only [mul_one, hσs]
  obtain ⟨P,hP,hr,hq⟩ := simultaneous_convex_cost_selection (retractions_convex A)
    r q hrc hqc hrn hqn htest
  refine ⟨P,hP,fun e => ?_,fun j => (hq j).le⟩
  have hh := (div_lt_iff₀ (sq_pos_of_pos hL)).mp (hr e)
  have hn := matrixRowNorm_nonneg P e
  have hh' : matrixRowNorm P e ≤ 2*L := by nlinarith
  dsimp [L] at hh'
  linarith

end WeightedProjection

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal

namespace SubpolynomialLp

lemma bounded_sample_exists {E : Type uE} {Ω : Type uΩ} [Fintype E] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E → ℝ)
    (hXm : ∀ e, Measurable (fun ω => X ω e)) (M : ℝ) (hM : 0 ≤ M)
    (hX : ∀ ω e, X ω e ∈ Set.Icc 0 M)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1) :
    ∃ ω : Fin d → Ω, ∀ e,
      |(∑ a, X (ω a) e)/(d:ℝ) - ∫ t, X t e ∂μ| < ε := by
  classical
  let ν : Measure (Fin d → Ω) := Measure.pi (fun _ => μ)
  let m : E → ℝ := fun e => ∫ t, X t e ∂μ
  let c : ℝ≥0 := (‖M‖₊/2)^2
  let Z : E → (Fin d → Ω) → ℝ := fun e ω => ∑ a, (X (ω a) e-m e)
  have hc : (c:ℝ) = (M/2)^2 := by simp [c, Real.norm_eq_abs, abs_of_nonneg hM]
  have hsg (e : E) : HasSubgaussianMGF (Z e) (d*c) ν := by
    have hs := hasSubgaussianMGF_of_mem_Icc (hXm e).aemeasurable (ae_of_all μ (fun ω => hX ω e))
    have hs' : HasSubgaussianMGF (fun ω => X ω e-m e) c μ := by
      simpa only [sub_zero] using hs
    have hi : iIndepFun (fun a : Fin d => fun ω : Fin d → Ω => X (ω a) e-m e) ν :=
      iIndepFun_pi (fun _ => ((hXm e).sub_const (m e)).aemeasurable)
    have hh := HasSubgaussianMGF.sum_of_iIndepFun (c := fun _ : Fin d => c) (s := Finset.univ) hi (fun a _ => by
      have ha := measurePreserving_eval (fun _ : Fin d => μ) a
      have hh : HasSubgaussianMGF (fun ω => X ω e-m e) c (Measure.map (Function.eval a) ν) := by
        rw [ha.map_eq]
        exact hs'
      exact hh.of_map ha.aemeasurable)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  let t : ℝ := d*ε
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let q := Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2))
  have htail (e : E) : ν.real {ω | t ≤ |Z e ω|} ≤ 2*q := by
    have hp := (hsg e).measure_ge_le ht
    have hn := (hsg e).neg.measure_ge_le ht
    have he : {ω | t ≤ |Z e ω|} = {ω | t ≤ Z e ω} ∪ {ω | t ≤ -Z e ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_union]
      rw [le_abs]
    rw [he]
    apply (measureReal_union_le _ _).trans
    have hq : Real.exp (-t^2/(2*((d*c:ℝ≥0):ℝ))) = q := by
      simp only [NNReal.coe_mul, NNReal.coe_natCast, hc, q, t, mul_assoc]
    change ν.real {ω | t ≤ Z e ω} + ν.real {ω | t ≤ -Z e ω} ≤ _
    rw [hq] at hp hn
    change ν.real {ω | t ≤ -Z e ω} ≤ q at hn
    linarith
  have hbad : ν.real (⋃ e, {ω | t ≤ |Z e ω|}) < 1 := by
    apply (measureReal_iUnion_fintype_le _).trans_lt
    calc
      ∑ e, ν.real {ω | t ≤ |Z e ω|} ≤ ∑ _ : E, 2*q := Finset.sum_le_sum (fun e _ => htail e)
      _ = (2*Fintype.card E:ℝ)*q := by simp; ring
      _ < 1 := hprob
  have hnotuniv : (⋃ e, {ω | t ≤ |Z e ω|}) ≠ Set.univ := by
    intro he
    rw [he] at hbad
    have : IsProbabilityMeasure ν := inferInstance
    simp at hbad
  have hex : ∃ ω, ω ∉ (⋃ e, {ω | t ≤ |Z e ω|}) := by
    by_contra h
    push Not at h
    exact hnotuniv (Set.eq_univ_of_forall h)
  obtain ⟨ω,hω⟩ := hex
  refine ⟨ω,fun e => ?_⟩
  have hze : |Z e ω| < t := lt_of_not_ge (fun h => hω (Set.mem_iUnion.mpr ⟨e,h⟩))
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have he : (∑ a, X (ω a) e)/(d:ℝ)-m e = Z e ω/(d:ℝ) := by
    simp only [Z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [he, abs_div, abs_of_pos hdR]
  exact (div_lt_iff₀ hdR).mpr (by simpa only [t, mul_comm] using hze)


lemma sample_convexHull {E : Type uE} [Fintype E] {S : Set (E → ℝ)}
    {v : E → ℝ} (hv : v ∈ convexHull ℝ S) (M : ℝ) (hM : 0 ≤ M)
    (hS : ∀ z ∈ S, ∀ e, z e ∈ Set.Icc 0 M)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1) :
    ∃ z : Fin d → E → ℝ, (∀ a, z a ∈ S) ∧
      ∀ e, |(∑ a, z a e)/(d:ℝ)-v e| < ε := by
  classical
  obtain ⟨I, hI, z, w, hz, _, hw, hws, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hv
  let : MeasurableSpace I := ⊤
  let μ : Measure I := Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i)
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, tsum_fintype]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le), hws, ENNReal.ofReal_one]
  have hXm (e : E) : Measurable (fun i => z i e) := measurable_of_countable _
  have hint (e : E) : ∫ i, z i e ∂μ = v e := by
    rw [show μ = Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i) from rfl,
      integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) (hasSum_fintype _).summable, tsum_fintype]
    simp only [ENNReal.toReal_ofReal (hw _).le, smul_eq_mul]
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congr_fun hsum e
  obtain ⟨ω,hω⟩ := bounded_sample_exists μ z hXm M hM
    (fun i => hS _ (hz ⟨i,rfl⟩)) d hd ε hε hprob
  refine ⟨z ∘ ω,fun a => hz ⟨ω a,rfl⟩,fun e => ?_⟩
  simpa only [hint, Function.comp_apply] using hω e

lemma weighted_moments_samples {E : Type uE} [Fintype E] [Nonempty E]
    {S : Set (E → ℝ)} (M : ℝ) (hM : 0 ≤ M) (hS : ∀ z ∈ S, ∀ e, z e ∈ Set.Icc 0 M)
    (b ε : ℝ) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ m ∈ closedConvexHull ℝ S, (∑ e, w e * |m e-b|) ≤ ε)
    (d : ℕ) (hd : 0 < d)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1) :
    ∃ z : Fin d → E → ℝ, (∀ a, z a ∈ S) ∧
      ∀ e, |(∑ a, z a e)/(d:ℝ)-b| < 3*ε := by
  classical
  obtain ⟨m,hm,hme⟩ := weighted_error_to_uniform convex_closedConvexHull b ε hε hw
  rw [closedConvexHull_eq_closure_convexHull] at hm
  have hb : m ∈ Metric.ball (fun _ => b) (2*ε) := by
    simpa only [Metric.mem_ball, dist_pi_lt_iff (show 0 < 2*ε by positivity), Real.dist_eq] using hme
  obtain ⟨v,hvB,hv⟩ := mem_closure_iff.mp hm _ Metric.isOpen_ball hb
  have hve : ∀ e, |v e-b| < 2*ε := by
    simpa only [Metric.mem_ball, dist_pi_lt_iff (show 0 < 2*ε by positivity), Real.dist_eq] using hvB
  obtain ⟨z,hz,hze⟩ := sample_convexHull hv M hM hS d hd ε hε hprob
  refine ⟨z,hz,fun e => ?_⟩
  have htriangle := abs_add_le ((∑ a, z a e)/(d:ℝ)-v e) (v e-b)
  have ha := hze e
  have hb := hve e
  rw [sub_add_sub_cancel] at htriangle
  linarith


section RetractionBounds
open Matrix MeasureTheory
variable {E : Type uE} {V : Type uV} {J : Type uJ} {H : Type uH} [Fintype E] [Fintype V] [Fintype J]
  [DecidableEq E] [DecidableEq V] [Nonempty E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma controlled_retraction_bounds
    (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (x : J → E → H) (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hx : ∀ j e, ‖x j e‖^2 ≤ B j) :
    ∃ P ∈ retractions (normalizedGradient src dst δ),
      (∀ e, matrixRowNorm P e ≤ 4*Real.log (Fintype.card V : ℝ)) ∧
      (∀ j, (∑ e, lam e * ‖hilbertMul P (x j) e‖^2) ≤ 4*B j) := by
  let y : J → E → H := fun j e => (Real.sqrt (B j))⁻¹ • x j e
  have hy (j : J) (e : E) : ‖y j e‖^2 ≤ 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, inv_pow, Real.sq_sqrt (hB j).le, inv_mul_eq_div]
    exact (div_le_one (hB j)).mpr (hx j e)
  obtain ⟨P,hP,hrow,henergy⟩ := controlled_retraction src dst δ lam hδ hlam hls hcard hinc hconn y hy
  refine ⟨P,hP,hrow,fun j => ?_⟩
  have hem (e : E) : hilbertMul P (y j) e = (Real.sqrt (B j))⁻¹ • hilbertMul P (x j) e := by
    simp only [hilbertMul, y, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact smul_comm _ _ _
  have he := henergy j
  simp only [hem, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt (hB j).le] at he
  have halg : (∑ e, lam e*((B j)⁻¹*‖hilbertMul P (x j) e‖^2)) =
      (∑ e, lam e*‖hilbertMul P (x j) e‖^2)/(B j) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [halg] at he
  exact (div_le_iff₀ (hB j)).mp he
end RetractionBounds

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

def fourierCutoff (x : ℝ) : ℝ := ∫ t in Set.Ioc (0:ℝ) 1, 1-Real.cos (t*x)

lemma fourierCutoff_nonneg (x : ℝ) : 0 ≤ fourierCutoff x :=
  integral_nonneg (fun _t => sub_nonneg.mpr (Real.cos_le_one _))

lemma fourierCutoff_le_two (x : ℝ) : fourierCutoff x ≤ 2 := by
  calc
    fourierCutoff x ≤ ∫ _ in Set.Ioc (0:ℝ) 1, (2:ℝ) := by
      apply integral_mono
      · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
      · exact integrable_const _
      · intro t
        have := Real.neg_one_le_cos (t*x)
        linarith
    _ = 2 := by simp

lemma fourierCutoff_eq (x : ℝ) (hx : x ≠ 0) :
    fourierCutoff x = 1-Real.sin x/x := by
  rw [fourierCutoff, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_sub intervalIntegrable_const ((by fun_prop : Continuous (fun t : ℝ => Real.cos (t*x))).intervalIntegrable 0 1),
    intervalIntegral.integral_const, intervalIntegral.integral_comp_mul_right _ hx,
    integral_cos]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma fourierCutoff_ge_half (x : ℝ) (hx : 2 ≤ |x|) : 1/2 ≤ fourierCutoff x := by
  have hxn : x ≠ 0 := by intro h; norm_num [h] at hx
  have ha : 0 < |x| := by linarith
  rw [fourierCutoff_eq x hxn]
  have h : Real.sin x/x ≤ 1/2 := by
    calc
      Real.sin x/x ≤ |Real.sin x/x| := le_abs_self _
      _ = |Real.sin x|/|x| := abs_div _ _
      _ ≤ 1/|x| := div_le_div_of_nonneg_right (Real.abs_sin_le_one x) ha.le
      _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hx
  linarith

@[fun_prop] lemma fourierCutoff_continuous : Continuous fourierCutoff := by
  apply continuous_of_dominated
    (bound := fun _ : ℝ => (2:ℝ))
  · intro x
    fun_prop
  · intro x
    exact ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      have := Real.neg_one_le_cos (t*x)
      linarith)
  · exact integrable_const _
  · exact ae_of_all _ (fun t => by fun_prop)

lemma real_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun μ t).re = ∫ x, Real.cos (t*x) ∂μ := by
  rw [charFun_apply_real]
  change RCLike.re (∫ x, Complex.exp ((t:ℂ)*x*Complex.I) ∂μ) = _
  rw [← integral_re]
  · apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp [Complex.exp_re])
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])

lemma fourierCutoff_average (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    (∫ x, fourierCutoff (b*x) ∂μ) =
      ∫ t in Set.Ioc (0:ℝ) 1, 1-(charFun μ (t*b)).re := by
  have hi : Integrable (Function.uncurry (fun x t : ℝ => 1-Real.cos (t*(b*x))))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine (integrable_const (2:ℝ)).mono' (by fun_prop) (ae_of_all _ (fun z => ?_))
    change |1-Real.cos (z.2*(b*z.1))| ≤ 2
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    have := Real.neg_one_le_cos (z.2*(b*z.1))
    change 1-Real.cos (z.2*(b*z.1)) ≤ 2
    linarith
  change (∫ x, (∫ t in Set.Ioc (0:ℝ) 1, 1-Real.cos (t*(b*x))) ∂μ) = _
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    dsimp only
    rw [integral_sub (integrable_const _) ((integrable_const (1:ℝ)).mono'
      (by fun_prop) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*(b*x)))))]
    simp only [integral_const, probReal_univ, one_smul, real_charFun, mul_assoc])

lemma stable_tail_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ)
    (hp : 0 < p) (hc : 0 ≤ c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p))
    (a : ℝ) (ha : 0 < a) :
    μ.real {x : ℝ | a < |x|} ≤ (2*c*2^p)*a^(-p) := by
  have hi : Integrable (fun x => fourierCutoff ((2/a)*x)) μ := by
    refine (integrable_const (2:ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fourierCutoff_nonneg _)]
      exact fourierCutoff_le_two _)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => fourierCutoff_nonneg ((2/a)*x))) hi (1/2)
  have hs : μ.real {x : ℝ | a < |x|} ≤ μ.real {x : ℝ | 1/2 ≤ fourierCutoff ((2/a)*x)} := by
    apply measureReal_mono ?_ (by finiteness)
    intro x hx
    apply fourierCutoff_ge_half
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) ha)]
    have h : a ≤ |x| := le_of_lt hx
    calc
      2 = (2/a)*a := by field_simp
      _ ≤ (2/a)*|x| := mul_le_mul_of_nonneg_left h (by positivity)
  have hb : (∫ x, fourierCutoff ((2/a)*x) ∂μ) ≤ c*(2/a)^p := by
    rw [fourierCutoff_average]
    calc
      (∫ t in Set.Ioc (0:ℝ) 1, 1-(charFun μ (t*(2/a))).re) ≤
          ∫ _ in Set.Ioc (0:ℝ) 1, c*(2/a)^p := by
        apply integral_mono_ae
        · apply Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
        · exact integrable_const _
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          rw [hcf]
          have he := Real.add_one_le_exp (-c*|t*(2/a)|^p)
          have ht' : |t*(2/a)| ≤ 2/a := by
            rw [abs_of_nonneg (mul_nonneg ht.1.le (by positivity))]
            exact mul_le_of_le_one_left (by positivity) ht.2
          have hpw := Real.rpow_le_rpow (abs_nonneg _) ht' hp.le
          nlinarith [mul_le_mul_of_nonneg_left hpw hc]
      _ = c*(2/a)^p := by simp
  have he : (2/a)^p = 2^p*a^(-p) := by
    rw [Real.div_rpow (by norm_num) ha.le, Real.rpow_neg ha.le]
    rfl
  rw [he] at hb
  nlinarith

lemma one_sub_cos_quadratic_lower (x : ℝ) (hx : |x| ≤ 2) :
    x^2/8 ≤ 1-Real.cos x := by
  have hpi : (1/2:ℝ) ≤ 2/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  have ha : |x/2| ≤ Real.pi/2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [Real.two_le_pi]
  have h := Real.mul_abs_le_abs_sin ha
  have habs : |x|/4 ≤ |Real.sin (x/2)| := by
    calc
      |x|/4 = (1/2)*|x/2| := by rw [abs_div]; norm_num; ring
      _ ≤ (2/Real.pi)*|x/2| := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
      _ ≤ _ := h
  have hs := sq_le_sq₀ (by positivity : (0:ℝ) ≤ |x|/4) (abs_nonneg (Real.sin (x/2))) |>.mpr habs
  rw [div_pow, sq_abs, sq_abs, Real.sin_sq_eq_half_sub] at hs
  have he : 2*(x/2) = x := by ring
  rw [he] at hs
  nlinarith

lemma fourierCutoff_quadratic (x : ℝ) : min (x^2) 1 ≤ 24*fourierCutoff x := by
  by_cases hx : 2 ≤ |x|
  · have := fourierCutoff_ge_half x hx
    have := min_le_right (x^2) 1
    linarith
  · have hx' : |x| ≤ 2 := le_of_lt (lt_of_not_ge hx)
    have h : x^2/24 ≤ fourierCutoff x := by
      calc
        x^2/24 = ∫ t in Set.Ioc (0:ℝ) 1, (t*x)^2/8 := by
          rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
          simp_rw [show ∀ t : ℝ, (t*x)^2/8 = (x^2/8)*t^2 by intro t; ring]
          rw [intervalIntegral.integral_const_mul, integral_pow]
          norm_num
          ring
        _ ≤ fourierCutoff x := by
          apply integral_mono_ae
          · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
          · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            apply one_sub_cos_quadratic_lower
            rw [abs_mul, abs_of_pos ht.1]
            exact (mul_le_of_le_one_left (abs_nonneg x) ht.2).trans hx'
    have := min_le_left (x^2) 1
    linarith

lemma stable_fourier_average_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c b : ℝ)
    (hp : 0 < p) (hc : 0 ≤ c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p)) :
    (∫ x, fourierCutoff (b*x) ∂μ) ≤ c*|b|^p := by
  rw [fourierCutoff_average]
  calc
    (∫ t in Set.Ioc (0:ℝ) 1, 1-(charFun μ (t*b)).re) ≤
        ∫ _ in Set.Ioc (0:ℝ) 1, c*|b|^p := by
      apply integral_mono_ae
      · exact Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.Ioc_subset_Icc_self
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [hcf]
        have he := Real.add_one_le_exp (-c*|t*b|^p)
        have hb : |t*b| ≤ |b| := by
          rw [abs_mul, abs_of_pos ht.1]
          exact mul_le_of_le_one_left (abs_nonneg b) ht.2
        have hpw := Real.rpow_le_rpow (abs_nonneg _) hb hp.le
        nlinarith [mul_le_mul_of_nonneg_left hpw hc]
    _ = c*|b|^p := by simp

lemma stable_capped_second_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ)
    (hp : 0 < p) (hc : 0 ≤ c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p))
    (a : ℝ) (ha : 0 < a) :
    (∫ x, min (x^2) (a^2) ∂μ) ≤ 24*c*a^(2-p) := by
  have hi : Integrable (fun x => fourierCutoff (a⁻¹*x)) μ := by
    refine (integrable_const (2:ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fourierCutoff_nonneg _)]
      exact fourierCutoff_le_two _)
  have hj : Integrable (fun x : ℝ => min (x^2) (a^2)) μ := by
    refine (integrable_const (a^2)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact min_le_right _ _)
  have hpt (x : ℝ) : min (x^2) (a^2) = a^2*min ((a⁻¹*x)^2) 1 := by
    rw [mul_min_of_nonneg _ _ (sq_nonneg a), mul_one, mul_pow]
    congr 2
    field_simp
  calc
    (∫ x, min (x^2) (a^2) ∂μ) ≤ ∫ x, (24*a^2)*fourierCutoff (a⁻¹*x) ∂μ := by
      apply integral_mono hj (hi.const_mul _)
      intro x
      dsimp only
      rw [hpt]
      nlinarith [mul_le_mul_of_nonneg_left (fourierCutoff_quadratic (a⁻¹*x)) (sq_nonneg a)]
    _ = (24*a^2)*∫ x, fourierCutoff (a⁻¹*x) ∂μ := integral_const_mul _ _
    _ ≤ (24*a^2)*(c*|a⁻¹|^p) := mul_le_mul_of_nonneg_left
      (stable_fourier_average_upper μ p c a⁻¹ hp hc hcf) (by positivity)
    _ = 24*c*a^(2-p) := by
      rw [abs_of_pos (inv_pos.mpr ha), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
        show 24*a^2*(c*a^(-p)) = 24*c*(a^2*a^(-p)) by ring,
        ← Real.rpow_natCast a 2, ← Real.rpow_add ha]
      rfl

lemma charFun_defect_le_capped (μ : Measure ℝ) [IsProbabilityMeasure μ] (t a : ℝ) :
    1-(charFun μ t).re ≤ (t^2/2)*(∫ x, min (x^2) (a^2) ∂μ) +
      2*μ.real {x : ℝ | |a| < |x|} := by
  have hi : Integrable (fun x : ℝ => min (x^2) (a^2)) μ := by
    refine (integrable_const (a^2)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact min_le_right _ _)
  have hc : Integrable (fun x : ℝ => Real.cos (t*x)) μ :=
    (integrable_const (1:ℝ)).mono' (by fun_prop)
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*x)))
  have hs : MeasurableSet {x : ℝ | |a| < |x|} := by measurability
  have hj : Integrable (Set.indicator {x : ℝ | |a| < |x|} (fun _ => (2:ℝ))) μ :=
    (integrable_const _).indicator hs
  have hm : (∫ x, 1-Real.cos (t*x) ∂μ) ≤
      ∫ x, (t^2/2)*min (x^2) (a^2) +
        Set.indicator {x : ℝ | |a| < |x|} (fun _ => (2:ℝ)) x ∂μ := by
    apply integral_mono ((integrable_const _).sub hc) ((hi.const_mul _).add hj)
    intro x
    simp only [Pi.sub_apply, Pi.add_apply]
    by_cases hx : |a| < |x|
    · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | |a| < |x|} from hx)]
      have := Real.neg_one_le_cos (t*x)
      have : 0 ≤ (t^2/2)*min (x^2) (a^2) := by positivity
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | |a| < |x|} from hx), add_zero, min_eq_left (sq_le_sq.mpr (le_of_not_gt hx))]
      have := Real.one_sub_sq_div_two_le_cos (x := t*x)
      nlinarith
  rw [integral_sub (integrable_const _) hc, integral_add (hi.const_mul _) hj,
    integral_const_mul, integral_indicator_const _ hs] at hm
  simpa only [integral_const, probReal_univ, one_smul, real_charFun, smul_eq_mul, mul_comm, mul_one] using hm

lemma exp_defect_lower (c z : ℝ) (hz : 0 ≤ z) (hzc : z ≤ c) :
    Real.exp (-c)*z ≤ 1-Real.exp (-z) := by
  have h1 := Real.add_one_le_exp z
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-z)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  have h3 := Real.exp_le_exp.mpr (neg_le_neg hzc)
  nlinarith [mul_le_mul_of_nonneg_right h3 hz]

lemma exists_small_power (r k : ℝ) (hr : 0 < r) (hk : 0 < k) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d^r ≤ k := by
  refine ⟨min 1 (k^(1/r)), lt_min (by norm_num) (Real.rpow_pos_of_pos hk _), min_le_left _ _, ?_⟩
  calc
    (min 1 (k^(1/r)))^r ≤ (k^(1/r))^r :=
      Real.rpow_le_rpow (le_of_lt (lt_min (by norm_num) (Real.rpow_pos_of_pos hk _)))
        (min_le_right _ _) hr.le
    _ = k := by rw [← Real.rpow_mul hk.le, one_div_mul_cancel hr.ne', Real.rpow_one]

lemma stable_tail_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ)
    (hp : 0 < p) (hp2 : p < 2) (hc : 0 < c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p)) :
    ∃ k : ℝ, 0 < k ∧ ∀ a : ℝ, 1 ≤ a → k*a^(-p) ≤ μ.real {x : ℝ | a < |x|} := by
  obtain ⟨d, hd, hd1, hdp⟩ := exists_small_power (2-p) (Real.exp (-c)/24) (by linarith) (by positivity)
  refine ⟨c*d^p*Real.exp (-c)/4, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have had : 0 ≤ d/a := by positivity
  have hda : d/a ≤ 1 := (div_le_one ha0).mpr (hd1.trans ha)
  have hpw : (d/a)^p ≤ 1 := by
    simpa using Real.rpow_le_rpow had hda hp.le
  have hz : 0 ≤ c*(d/a)^p := by positivity
  have hzc : c*(d/a)^p ≤ c := by nlinarith
  have he := exp_defect_lower c (c*(d/a)^p) hz hzc
  have hf := charFun_defect_le_capped μ (d/a) a
  rw [hcf, abs_of_nonneg had, abs_of_pos ha0] at hf
  have hs := stable_capped_second_upper μ p c hp hc.le hcf a ha0
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ (d/a)^2/2 by positivity)
  have haexp : (d/a)^2/2*(24*c*a^(2-p)) = 12*c*d^2*a^(-p) := by
    rw [div_pow]
    have heq : a^(2-p) = a^2*a^(-p) := by rw [sub_eq_add_neg, Real.rpow_add ha0, Real.rpow_two]
    rw [heq]
    field_simp
    ring
  rw [haexp] at hb
  have hdexp : d^2 = d^p*d^(2-p) := by rw [← Real.rpow_add hd, add_sub_cancel, Real.rpow_two]
  have hsmall : 12*c*d^2 ≤ c*d^p*Real.exp (-c)/2 := by
    rw [hdexp]
    nlinarith [mul_le_mul_of_nonneg_left hdp (show 0 ≤ 12*c*d^p by positivity)]
  have hpower : (d/a)^p = d^p*a^(-p) := by
    rw [Real.div_rpow hd.le ha0.le, Real.rpow_neg ha0.le]
    rfl
  rw [hpower] at he
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg ha0.le (-p))
  have harg : -c*(d/a)^p = -(c*(d/a)^p) := by ring
  rw [harg, hpower] at hf
  nlinarith

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma tail_measurable (μ : Measure ℝ) (f : ℝ → ℝ) :
    Measurable (fun t : ℝ => μ {x | t < f x}) :=
  Antitone.measurable (fun _ _ h => measure_mono (fun _ hx => lt_of_le_of_lt h hx))

lemma tail_real_measurable (μ : Measure ℝ) (f : ℝ → ℝ) :
    Measurable (fun t : ℝ => μ.real {x | t < f x}) :=
  (tail_measurable μ f).ennreal_toReal

lemma integral_power_derivative (q u : ℝ) (hq : 0 < q) (_hu : 0 ≤ u) :
    (∫ t in (0:ℝ)..u, q*t^(q-1)) = u^q := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < q-1)),
    sub_add_cancel, Real.zero_rpow hq.ne', sub_zero]
  field_simp

lemma capped_moment_layercake (μ : Measure ℝ) [IsFiniteMeasure μ]
    (q a : ℝ) (hq : 0 < q) (ha : 0 < a) :
    (∫ x, (min |x| a)^q ∂μ) =
      ∫ t in Set.Ioo (0:ℝ) a, (q*t^(q-1))*μ.real {x : ℝ | t < |x|} := by
  let f : ℝ → ℝ := fun x => min |x| a
  have hf : ∀ x, 0 ≤ f x := fun x => le_min (abs_nonneg x) ha.le
  have hfm : Measurable f := by fun_prop
  have hg : ∀ t > 0, IntervalIntegrable (fun t : ℝ => q*t^(q-1)) volume 0 t :=
    fun _ _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)).const_mul q
  have hgn : ∀ᵐ t ∂volume.restrict (Set.Ioi (0:ℝ)), 0 ≤ q*t^(q-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hq.le (Real.rpow_nonneg (le_of_lt ht) _)
  have hk := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ hf) hfm.aemeasurable hg hgn
  simp_rw [integral_power_derivative q _ hq (hf _)] at hk
  have hmeas : Measurable (fun t : ℝ => μ {x | t < f x} * ENNReal.ofReal (q*t^(q-1))) :=
    (tail_measurable μ f).mul (by fun_prop)
  have hfinite : ∀ᵐ t ∂volume.restrict (Set.Ioi (0:ℝ)),
      μ {x | t < f x} * ENNReal.ofReal (q*t^(q-1)) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.mul_lt_top (by finiteness) ENNReal.ofReal_lt_top)
  calc
    (∫ x, (min |x| a)^q ∂μ) =
        (∫⁻ x, ENNReal.ofReal ((f x)^q) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => Real.rpow_nonneg (hf x) _)) (by fun_prop (disch := positivity))
    _ = (∫⁻ t in Set.Ioi (0:ℝ), μ {x | t < f x}*ENNReal.ofReal (q*t^(q-1))).toReal := by rw [hk]
    _ = ∫ t in Set.Ioi (0:ℝ), (q*t^(q-1))*μ.real {x | t < f x} := by
      rw [← integral_toReal hmeas.aemeasurable hfinite]
      apply integral_congr_ae
      filter_upwards [hgn] with t ht
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht, measureReal_def, mul_comm]
    _ = ∫ t in Set.Ioi (0:ℝ), (Set.Iio a).indicator
          (fun t => (q*t^(q-1))*μ.real {x : ℝ | t < |x|}) t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        dsimp only
        by_cases ht : t < a
        · rw [Set.indicator_of_mem (show t ∈ Set.Iio a from ht)]
          have he : {x | t < f x} = {x : ℝ | t < |x|} := by
            ext x
            simp [f, ht]
          rw [he]
        · rw [Set.indicator_of_notMem (show t ∉ Set.Iio a from ht)]
          have he : {x | t < f x} = ∅ := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            exact not_lt.mpr ((min_le_right |x| a).trans (le_of_not_gt ht))
          rw [he, measureReal_empty, mul_zero])
    _ = _ := by
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have he : Set.Iio a ∩ Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) a := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo, and_comm]
      rw [he]


lemma capped_moment_lower_log (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p k a : ℝ) (hp : 1 < p) (_hk : 0 ≤ k) (ha : 1 ≤ a)
    (htail : ∀ t : ℝ, 1 ≤ t → k*t^(-p) ≤ μ.real {x : ℝ | t < |x|}) :
    k*p*Real.log a ≤ ∫ x, (min |x| a)^p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [capped_moment_layercake μ p a (by linarith) ha0]
  let f : ℝ → ℝ := fun t => (p*t^(p-1))*μ.real {x : ℝ | t < |x|}
  have hf : IntegrableOn f (Set.Ioo 0 a) := by
    refine (((show Continuous (fun t : ℝ => p*t^(p-1)) by
      fun_prop (disch := linarith)).continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self).mono'
      (((by fun_prop : Measurable (fun t : ℝ => p*t^(p-1))).mul
        (tail_real_measurable μ (fun x => |x|))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    dsimp [f]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) measureReal_le_one
  have hsub : Set.Ioo (1:ℝ) a ⊆ Set.Ioo (0:ℝ) a :=
    fun _ ht => ⟨lt_trans zero_lt_one ht.1, ht.2⟩
  calc
    k*p*Real.log a = ∫ t in Set.Ioo (1:ℝ) a, (k*p)*t⁻¹ := by
      rw [integral_const_mul, integral_Ioc_eq_integral_Ioo.symm,
        ← intervalIntegral.integral_of_le ha, integral_inv_of_pos zero_lt_one ha0,
        div_one]
    _ ≤ ∫ t in Set.Ioo (1:ℝ) a, f t := by
      apply integral_mono_ae
        (((continuousOn_const.mul (continuousOn_inv₀.mono (fun t ht =>
          ne_of_gt (zero_lt_one.trans_le ht.1)))).integrableOn_Icc).mono_set
            Set.Ioo_subset_Icc_self) (hf.mono_set hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht.1
      have he : (p*t^(p-1))*(k*t^(-p)) = (k*p)*t⁻¹ := by
        rw [mul_mul_mul_comm, ← Real.rpow_add ht0,
          show p-1+-p = -1 by ring, Real.rpow_neg_one, mul_comm p k]
      change (k*p)*t⁻¹ ≤ (p*t^(p-1))*μ.real {x : ℝ | t < |x|}
      rw [← he]
      exact mul_le_mul_of_nonneg_left (htail t ht.1.le) (by positivity)
    _ ≤ ∫ t in Set.Ioo (0:ℝ) a, f t := by
      apply setIntegral_mono_set hf
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        dsimp [f]
        exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1.le _))
          measureReal_nonneg
      · exact ae_of_all _ (fun _ h => hsub h)


lemma excess_first_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (p C a : ℝ) (hp : 1 < p) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ t : ℝ, 0 < t → μ.real {x : ℝ | t < |x|} ≤ C*t^(-p)) :
    Integrable (fun x : ℝ => max (|x|-a) 0) μ ∧
      (∫ x, max (|x|-a) 0 ∂μ) ≤ C*(1+1/(p-1))*a^(1-p) := by
  let f : ℝ → ℝ := fun x => max (|x|-a) 0
  have hf : ∀ x, 0 ≤ f x := fun x => le_max_right _ _
  have hfm : Measurable f := by fun_prop
  have ht (t : ℝ) (ht : 0 < t) : {x | t < f x} = {x : ℝ | a+t < |x|} := by
    ext x
    simp only [Set.mem_ofPred_eq, f, lt_max_iff, not_lt.mpr ht.le, or_false]
    constructor <;> intro h <;> linarith
  have hbound (t : ℝ) (ht0 : 0 < t) :
      μ {x | t < f x} ≤ ENNReal.ofReal (C*(a+t)^(-p)) := by
    rw [ht t ht0, ← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal (htail (a+t) (add_pos ha ht0))
  have hdec {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : y^(-p) ≤ x^(-p) :=
    Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
  have h1 : (∫⁻ t in Set.Ioc (0:ℝ) a, μ {x | t < f x}) ≤ ENNReal.ofReal (C*a^(-p)*a) := by
    calc
      _ ≤ ∫⁻ t in Set.Ioc (0:ℝ) a, ENNReal.ofReal (C*a^(-p)) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t ht'
        exact (hbound t ht'.1).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hdec ha (le_add_of_nonneg_right ht'.1.le)) hC))
      _ = _ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (mul_nonneg hC (by positivity))]
  have hi : IntegrableOn (fun t : ℝ => C*t^(-p)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) ha).const_mul C
  have h2 : (∫⁻ t in Set.Ioi a, μ {x | t < f x}) ≤ ENNReal.ofReal (C/(p-1)*a^(1-p)) := by
    calc
      _ ≤ ∫⁻ t in Set.Ioi a, ENNReal.ofReal (C*t^(-p)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht'
        exact (hbound t (ha.trans ht')).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hdec (ha.trans ht') (le_add_of_nonneg_left ha.le)) hC))
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi]
        · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -p < -1) ha]
          congr 1
          rw [show -p+1 = -(p-1) by ring, neg_div_neg_eq, show -(p-1) = 1-p by ring]
          ring
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht'
          exact mul_nonneg hC (Real.rpow_nonneg (ha.trans ht').le _)
  have hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (C*(1+1/(p-1))*a^(1-p)) := by
    have he : Set.Ioi (0:ℝ) = Set.Ioc 0 a ∪ Set.Ioi a := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases ht' : t ≤ a
        · exact Or.inl ⟨h,ht'⟩
        · exact Or.inr (lt_of_not_ge ht')
      · intro h
        rcases h with h | h
        · exact h.1
        · exact ha.trans h
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hf) hfm.aemeasurable, he,
      lintegral_union measurableSet_Ioi (by exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h1.2 h2))]
    calc
      _ ≤ ENNReal.ofReal (C*a^(-p)*a) + ENNReal.ofReal (C/(p-1)*a^(1-p)) := add_le_add h1 h2
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hpow : a^(-p)*a = a^(1-p) := by
          calc
            _ = a^(-p)*a^(1:ℝ) := by rw [Real.rpow_one]
            _ = a^(1-p) := by rw [← Real.rpow_add ha]; congr 1; ring
        rw [mul_assoc, hpow]
        ring
  have hfi : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable (ae_of_all _ hf)).mp
      (ne_of_lt (hlin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hfm.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq
    (ENNReal.toReal_ofReal (by positivity))


def clip (a x : ℝ) : ℝ := max (-a) (min x a)

lemma clip_abs (a x : ℝ) (ha : 0 ≤ a) : |clip a x| = min |x| a := by
  unfold clip
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (le_trans (le_min hx ha) (le_max_right _ _)),
      max_eq_right (by exact le_trans (neg_nonpos.mpr ha) (le_min hx ha)), abs_of_nonneg hx]
  · rw [min_eq_left (hx.trans ha), abs_of_nonpos (max_le (neg_nonpos.mpr ha) hx), abs_of_nonpos hx]
    by_cases h : -a ≤ x
    · rw [max_eq_right h, min_eq_left (by linarith)]
    · rw [max_eq_left (le_of_not_ge h), min_eq_right (by linarith), neg_neg]

lemma clip_error (a x : ℝ) (ha : 0 ≤ a) : |x-clip a x| = max (|x|-a) 0 := by
  unfold clip
  rcases le_total x (-a) with hx | hx
  · rw [min_eq_left (hx.trans (by linarith)), max_eq_left hx,
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), max_eq_left (by linarith)]
    ring
  · rcases le_total x a with hxa | hxa
    · rw [min_eq_left hxa, max_eq_right hx, sub_self, abs_zero,
        max_eq_right (by have := abs_le.mpr ⟨hx,hxa⟩; linarith)]
    · rw [min_eq_right hxa, max_eq_right (by linarith), abs_of_nonneg (sub_nonneg.mpr hxa),
        abs_of_nonneg (ha.trans hxa), max_eq_left (sub_nonneg.mpr hxa)]

lemma clip_measurable (a : ℝ) : Measurable (clip a) := by unfold clip; fun_prop

lemma capped_power_lipschitz (p a : ℝ) (hp : 1 ≤ p) (ha : 0 ≤ a) (x y : ℝ) :
    |(min |x| a)^p-(min |y| a)^p| ≤ p*a^(p-1)*|x-y| := by
  have hmem (x : ℝ) : min |x| a ∈ Set.Icc (0:ℝ) a :=
    ⟨le_min (abs_nonneg _) ha, min_le_right _ _⟩
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => t^p) (f' := fun t : ℝ => p*t^(p-1))
    (C := p*a^(p-1)) (fun t _ => (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1 _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 (by linarith)) (by linarith))
    (convex_Icc (0:ℝ) a) (hmem y) (hmem x)
  simp only [Real.norm_eq_abs] at hm
  refine hm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact (abs_min_sub_min_le_max |x| a |y| a).trans (by
    simp only [sub_self, abs_zero]
    exact max_le (abs_abs_sub_abs_le_abs_sub x y) (abs_nonneg _))

lemma capped_power_tail_bound (p a x : ℝ) (hp : 0 < p) (hp2 : p < 2) (ha : 0 < a) :
    0 ≤ |x|^p-(min |x| a)^p ∧ |x|^p-(min |x| a)^p ≤ a^(p-2)*x^2 := by
  have hn : (min |x| a)^p ≤ |x|^p :=
    Real.rpow_le_rpow (le_min (abs_nonneg _) ha.le) (min_le_left _ _) hp.le
  refine ⟨sub_nonneg.mpr hn, ?_⟩
  by_cases hx : |x| ≤ a
  · rw [min_eq_left hx, sub_self]
    positivity
  · have hx0 : 0 < |x| := ha.trans (lt_of_not_ge hx)
    have he : |x|^p = |x|^(p-2)*x^2 := by
      rw [← sq_abs x, ← Real.rpow_natCast |x| 2, ← Real.rpow_add hx0]
      congr 1
      norm_num
    calc
      |x|^p-(min |x| a)^p ≤ |x|^p := sub_le_self _ (Real.rpow_nonneg (le_min hx0.le ha.le) _)
      _ = |x|^(p-2)*x^2 := he
      _ ≤ a^(p-2)*x^2 := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos ha (le_of_not_ge hx) (by linarith)) (sq_nonneg _)


lemma bounded_power_integrable {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hm : Measurable f)
    (p K : ℝ) (hp : 0 < p) (_hK : 0 ≤ K) (hf : ∀ x, |f x| ≤ K) :
    Integrable (fun x => |f x|^p) μ := by
  refine (integrable_const (K^p)).mono' (by fun_prop (disch := positivity)) ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hf x) hp.le)

lemma bounded_capped_integrable {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hm : Measurable f)
    (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    Integrable (fun x => (min |f x| a)^p) μ := by
  refine (integrable_const (a^p)).mono' (by fun_prop (disch := positivity)) ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_min (abs_nonneg _) ha) _)]
    exact Real.rpow_le_rpow (le_min (abs_nonneg _) ha) (min_le_right _ _) hp.le)

lemma matrix_clip_bounds {E : Type uE} [Fintype E] (P : Matrix E E ℝ)
    (Y : E → ℝ) (T H : ℝ) (hT : 0 ≤ T)
    (hrow : ∀ e, (∑ f, |P e f|) ≤ H) (hPY : P.mulVec Y = Y) :
    (∀ e, |P.mulVec (fun f => clip T (Y f)) e| ≤ H*T) ∧
    (∀ e, |Y e-P.mulVec (fun f => clip T (Y f)) e| ≤
      ∑ f, |P e f| *max (|Y f|-T) 0) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · calc
      _ ≤ ∑ f, |P e f*clip T (Y f)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ f, |P e f| *T := Finset.sum_le_sum (fun f _ => by
        rw [abs_mul, clip_abs T _ hT]
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg _))
      _ = (∑ f, |P e f|)*T := (Finset.sum_mul ..).symm
      _ ≤ H*T := mul_le_mul_of_nonneg_right (hrow e) hT
  · have he : Y e-P.mulVec (fun f => clip T (Y f)) e =
        ∑ f, P e f*(Y f-clip T (Y f)) := by
      rw [← congr_fun hPY e]
      change (∑ f, P e f*Y f)-(∑ f, P e f*clip T (Y f)) = _
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [he]
    simpa only [abs_mul, clip_error T _ hT] using Finset.abs_sum_le_sum_abs
      (fun f => P e f*(Y f-clip T (Y f))) Finset.univ

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma below_projection_moments {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → E → ℝ)
    (hm : ∀ e, Measurable (fun x => Y x e)) (P : Matrix E E ℝ)
    (lam : E → ℝ) (hlam : ∀ e, 0 ≤ lam e) (hls : ∑ e, lam e = 1)
    (p T a H b err B : ℝ) (hp : 1 < p) (hp2 : p < 2) (hT : 0 ≤ T)
    (ha : 0 < a) (hH : 0 ≤ H) (herr : 0 ≤ err)
    (hrow : ∀ e, (∑ f, |P e f|) ≤ H) (hPY : ∀ x, P.mulVec (Y x) = Y x)
    (hex : ∀ e, Integrable (fun x => max (|Y x e|-T) 0) μ)
    (hexm : ∀ e, (∫ x, max (|Y x e|-T) 0 ∂μ) ≤ err)
    (hb : ∀ e, (∫ x, (min |Y x e| a)^p ∂μ) = b)
    (henergy : (∑ e, lam e*(∫ x, (P.mulVec (fun f => clip T (Y x f)) e)^2 ∂μ)) ≤ B) :
    (∑ e, lam e*|(∫ x, |P.mulVec (fun f => clip T (Y x f)) e|^p ∂μ)-b|) ≤
      (p*a^(p-1))*H*err+a^(p-2)*B := by
  let F : Ω → E → ℝ := fun x => P.mulVec (fun f => clip T (Y x f))
  have hFm (e : E) : Measurable (fun x => F x e) := by
    exact Finset.measurable_sum _ (fun f _ =>
      measurable_const.mul ((clip_measurable T).comp (hm f)))
  have hFb (x : Ω) (e : E) : |F x e| ≤ H*T :=
    (matrix_clip_bounds P (Y x) T H hT hrow (hPY x)).1 e
  have hFp (e : E) : Integrable (fun x => |F x e|^p) μ :=
    bounded_power_integrable μ _ (hFm e) p (H*T) (by linarith) (mul_nonneg hH hT) (fun x => hFb x e)
  have hFc (e : E) : Integrable (fun x => (min |F x e| a)^p) μ :=
    bounded_capped_integrable μ _ (hFm e) p a (by linarith) ha.le
  have hYc (e : E) : Integrable (fun x => (min |Y x e| a)^p) μ :=
    bounded_capped_integrable μ _ (hm e) p a (by linarith) ha.le
  have hFe (e : E) : Integrable (fun x => (F x e)^2) μ := by
    simpa only [Real.rpow_two, sq_abs] using
      bounded_power_integrable μ _ (hFm e) 2 (H*T) (by norm_num) (mul_nonneg hH hT) (fun x => hFb x e)
  have hd (e : E) : (∫ x, |Y x e-F x e| ∂μ) ≤ H*err ∧
      Integrable (fun x => |Y x e-F x e|) μ := by
    have hi : Integrable (fun x => ∑ f, |P e f| *max (|Y x f|-T) 0) μ :=
      integrable_finsetSum _ (fun f _ => (hex f).const_mul _)
    have hle (x : Ω) : |Y x e-F x e| ≤ ∑ f, |P e f| *max (|Y x f|-T) 0 :=
      (matrix_clip_bounds P (Y x) T H hT hrow (hPY x)).2 e
    have hdi : Integrable (fun x => |Y x e-F x e|) μ :=
      hi.mono' ((hm e).sub (hFm e)).abs.aestronglyMeasurable
        (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_abs] using hle x))
    refine ⟨?_,hdi⟩
    calc
      _ ≤ ∫ x, ∑ f, |P e f| *max (|Y x f|-T) 0 ∂μ := integral_mono hdi hi hle
      _ = ∑ f, |P e f| *(∫ x, max (|Y x f|-T) 0 ∂μ) := by
        rw [integral_finsetSum _ (fun f _ => (hex f).const_mul _)]
        simp only [integral_const_mul]
      _ ≤ ∑ f, |P e f| *err := Finset.sum_le_sum (fun f _ =>
        mul_le_mul_of_nonneg_left (hexm f) (abs_nonneg _))
      _ = (∑ f, |P e f|)*err := (Finset.sum_mul ..).symm
      _ ≤ H*err := mul_le_mul_of_nonneg_right (hrow e) herr
  have hc (e : E) : |(∫ x, (min |F x e| a)^p ∂μ)-b| ≤ (p*a^(p-1))*H*err := by
    rw [← hb e, ← integral_sub (hFc e) (hYc e)]
    calc
      _ ≤ ∫ x, |(min |F x e| a)^p-(min |Y x e| a)^p| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (p*a^(p-1))*|Y x e-F x e| ∂μ := by
        apply integral_mono ((hFc e).sub (hYc e)).abs ((hd e).2.const_mul _)
        intro x
        simpa only [Pi.sub_apply, abs_sub_comm] using capped_power_lipschitz p a hp.le ha.le (F x e) (Y x e)
      _ = (p*a^(p-1))*(∫ x, |Y x e-F x e| ∂μ) := integral_const_mul _ _
      _ ≤ (p*a^(p-1))*H*err := by
        have hpos : 0 ≤ p*a^(p-1) := mul_nonneg (by linarith) (Real.rpow_nonneg ha.le _)
        nlinarith [mul_le_mul_of_nonneg_left (hd e).1 hpos]
  have htail (e : E) : 0 ≤ (∫ x, |F x e|^p ∂μ)-(∫ x, (min |F x e| a)^p ∂μ) ∧
      (∫ x, |F x e|^p ∂μ)-(∫ x, (min |F x e| a)^p ∂μ) ≤ a^(p-2)*(∫ x, (F x e)^2 ∂μ) := by
    rw [← integral_sub (hFp e) (hFc e), ← integral_const_mul]
    refine ⟨integral_nonneg (fun x => (capped_power_tail_bound p a (F x e) (by linarith) hp2 ha).1), ?_⟩
    exact integral_mono ((hFp e).sub (hFc e)) ((hFe e).const_mul _)
      (fun x => (capped_power_tail_bound p a (F x e) (by linarith) hp2 ha).2)
  calc
    _ ≤ ∑ e, lam e*((p*a^(p-1))*H*err+a^(p-2)*(∫ x, (F x e)^2 ∂μ)) := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_left _ (hlam e)
      have ht := abs_add_le ((∫ x, |F x e|^p ∂μ)-(∫ x, (min |F x e| a)^p ∂μ))
        ((∫ x, (min |F x e| a)^p ∂μ)-b)
      rw [sub_add_sub_cancel, abs_of_nonneg (htail e).1] at ht
      linarith [(htail e).2, hc e]
    _ = (p*a^(p-1))*H*err+a^(p-2)*(∑ e, lam e*(∫ x, (F x e)^2 ∂μ)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hls, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left henergy (Real.rpow_nonneg ha.le _)) _


lemma L2_norm_sq {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma Lp_coe_sum {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    (fun x => (∑ i ∈ s, f i) x) =ᵐ[μ] (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa only [Finset.sum_empty, Pi.zero_apply] using hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hy
    simp only [Pi.add_apply] at hx
    rw [hx, hy]

lemma L2_hilbertMul_energy {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) (f : E → Ω → ℝ) (hf : ∀ e, MemLp (f e) 2 μ)
    (P : Matrix E E ℝ) (e : E) :
    ‖hilbertMul P (fun e => (hf e).toLp (f e)) e‖^2 =
      ∫ x, (∑ a, P e a*f a x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hc : ∀ a, (fun x => (P e a • (hf a).toLp (f a)) x) =ᵐ[μ] fun x => P e a*f a x := by
    intro a
    filter_upwards [Lp.coeFn_smul (P e a) ((hf a).toLp (f a)), (hf a).coeFn_toLp] with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul, hy] using hx
  apply integral_congr_ae
  filter_upwards [Lp_coe_sum μ Finset.univ (fun a => P e a • (hf a).toLp (f a)),
    ae_all_iff.mpr hc] with x hx hy
  change inner ℝ ((∑ a, P e a • (hf a).toLp (f a)) x)
    ((∑ a, P e a • (hf a).toLp (f a)) x) = _
  rw [hx]
  simp only [hy, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]


lemma charFun_linear_sum {ι : Type uι} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (g : ι → ℝ) (t : ℝ) :
    charFun ((Measure.pi μ).map (fun x : ι → ℝ => ∑ i, g i*x i)) t =
      ∏ i, charFun (μ i) (t*g i) := by
  have hm : Measurable (fun x : ι → ℝ => ∑ i, g i*x i) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [Complex.ofReal_sum]
  have he : ∀ x : ι → ℝ,
      Complex.exp ((t:ℂ)*(∑ i, ((g i*x i:ℝ):ℂ))*Complex.I) =
        ∏ i, Complex.exp ((((t*g i:ℝ):ℂ)*x i)*Complex.I) := by
    intro x
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Complex.exp ((((t*g i:ℝ):ℂ)*x)*Complex.I))]
  simp only [charFun_apply_real]

lemma stable_linear_sum_identical {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ) (_hp : 0 < p)
    (hcf : ∀ t : ℝ, charFun μ t = Complex.exp ((-c*|t|^p:ℝ):ℂ))
    (g : ι → ℝ) (hg : ∑ i, |g i|^p = 1) :
    (Measure.pi (fun _ : ι => μ)).map (fun x : ι → ℝ => ∑ i, g i*x i) = μ := by
  have : IsProbabilityMeasure ((Measure.pi (fun _ : ι => μ)).map
      (fun x : ι → ℝ => ∑ i, g i*x i)) := Measure.isProbabilityMeasure_map
        (by fun_prop : Measurable (fun x : ι → ℝ => ∑ i, g i*x i)).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_linear_sum, hcf]
  simp_rw [hcf]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum]
  congr 2
  simp_rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum, hg, mul_one]

lemma stable_joint_gradient {ι : Type uι} {ε : Type uε} [Fintype ι] [Fintype ε]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ) (hp : 0 < p)
    (hcf : ∀ t : ℝ, charFun μ t = Complex.exp ((-c*|t|^p:ℝ):ℂ))
    (V : Submodule ℝ (ε → ℝ)) (g : ι → ε → ℝ)
    (hV : ∀ i, g i ∈ V) (hg : ∀ e, ∑ i, |g i e|^p = 1) :
    ∃ Y : (ι → ℝ) → ε → ℝ, Measurable Y ∧ (∀ x, Y x ∈ V) ∧
      ∀ e, (Measure.pi (fun _ : ι => μ)).map (fun x => Y x e) = μ := by
  refine ⟨fun x => ∑ i, x i • g i, by fun_prop, ?_, ?_⟩
  · intro x
    exact V.sum_mem (fun i _ => V.smul_mem _ (hV i))
  · intro e
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
      stable_linear_sum_identical μ p c hp hcf (fun i => g i e) (hg e)


lemma clip_sq (T x : ℝ) (hT : 0 ≤ T) : (clip T x)^2 = min (x^2) (T^2) := by
  rw [← sq_abs (clip T x), clip_abs T x hT]
  by_cases hx : |x| ≤ T
  · rw [min_eq_left hx, sq_abs, min_eq_left]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hT).mpr hx
  · have ht : T ≤ |x| := le_of_not_ge hx
    rw [min_eq_right ht, min_eq_right]
    nlinarith [sq_abs x, abs_nonneg x]

lemma stable_retraction_moments {Ω : Type uΩ} {E : Type uE} {V : Type uV} [MeasurableSpace Ω]
    [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] [Nonempty E]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p c : ℝ) (hp : 1 < p) (hp2 : p < 2) (hc : 0 < c)
    (hcf : ∀ t : ℝ, (charFun μ t).re = Real.exp (-c*|t|^p))
    (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (Y : Ω → E → ℝ) (hm : Measurable Y)
    (hY : ∀ x, ∃ z, (normalizedGradient src dst δ).mulVec z = Y x)
    (hLaw : ∀ e, ν.map (fun x => Y x e) = μ)
    (T a : ℝ) (hT : 0 < T) (ha : 0 < a) :
    ∃ F : Ω → E → ℝ, Measurable F ∧
      (∀ x, ∃ z, (normalizedGradient src dst δ).mulVec z = F x) ∧
      (∀ x e, |F x e| ≤ (4*Real.log (Fintype.card V:ℝ))*T) ∧
      (∑ e, lam e*|(∫ x, |F x e|^p ∂ν)-(∫ x, (min |x| a)^p ∂μ)|) ≤
        (p*a^(p-1))*(4*Real.log (Fintype.card V:ℝ))*
          ((2*c*2^p)*(1+1/(p-1))*T^(1-p))+
        a^(p-2)*(96*c*T^(2-p)) := by
  let A := normalizedGradient src dst δ
  let H := 4*Real.log (Fintype.card V:ℝ)
  have hH : 0 ≤ H := by
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card V))
  have hym (e : E) : Measurable (fun x => Y x e) := (measurable_pi_apply e).comp hm
  let f : E → Ω → ℝ := fun e x => clip T (Y x e)
  have hfm (e : E) : Measurable (f e) := (clip_measurable T).comp (hym e)
  have hflp (e : E) : MemLp (f e) 2 ν := by
    apply memLp_of_bounded (a := -T) (b := T) _ (hfm e).aestronglyMeasurable
    exact ae_of_all _ (fun x => (abs_le.mp ((clip_abs T _ hT.le).trans_le (min_le_right _ _))))
  have hint (e : E) (g : ℝ → ℝ) (hg : AEStronglyMeasurable g μ) :
      (∫ x, g (Y x e) ∂ν) = ∫ x, g x ∂μ := by
    rw [← hLaw e] at hg ⊢
    exact (integral_map (hym e).aemeasurable hg).symm
  have hf2 (e : E) : ‖(hflp e).toLp (f e)‖^2 ≤ 24*c*T^(2-p) := by
    rw [L2_norm_sq ν _ (hflp e)]
    simp only [f, clip_sq T _ hT.le]
    rw [hint e (fun x => min (x^2) (T^2)) (by fun_prop)]
    exact stable_capped_second_upper μ p c (by linarith) hc.le hcf T hT
  obtain ⟨P,hP,hrow,henergy⟩ := controlled_retraction_bounds
    src dst δ lam hδ hlam hls hcard hinc hconn
    (fun _ : Unit => fun e => (hflp e).toLp (f e)) (fun _ => 24*c*T^(2-p))
    (fun _ => by positivity) (fun _ e => hf2 e)
  let F : Ω → E → ℝ := fun x => P.mulVec (fun e => f e x)
  have hPY (x : Ω) : P.mulVec (Y x) = Y x := by
    obtain ⟨z,hz⟩ := hY x
    rw [← hz, Matrix.mulVec_mulVec, hP.1]
  have hrow' (e : E) : (∑ a, |P e a|) ≤ H := hrow e
  have he : (∑ e, lam e*(∫ x, (F x e)^2 ∂ν)) ≤ 96*c*T^(2-p) := by
    have hh := henergy ()
    simp_rw [L2_hilbertMul_energy ν f hflp P] at hh
    change (∑ e, lam e*(∫ x, (F x e)^2 ∂ν)) ≤ 4*(24*c*T^(2-p)) at hh
    linarith
  have hex0 := excess_first_moment μ p (2*c*2^p) T hp (by positivity) hT
    (fun t ht => stable_tail_upper μ p c (by linarith) hc.le hcf t ht)
  have hex (e : E) : Integrable (fun x => max (|Y x e|-T) 0) ν := by
    have h := hex0.1
    rw [← hLaw e] at h
    exact h.comp_measurable (hym e)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · apply Measurable.of_eval
    intro e
    exact Finset.measurable_sum _ (fun a _ => measurable_const.mul (hfm a))
  · intro x
    obtain ⟨B,hB⟩ := hP.2
    refine ⟨B.mulVec (fun e => f e x), ?_⟩
    rw [Matrix.mulVec_mulVec, ← hB]
  · exact fun x e => (matrix_clip_bounds P (Y x) T H hT.le hrow' (hPY x)).1 e
  · exact below_projection_moments ν Y hym P lam (fun e => (hlam e).le) hls
      p T a H (∫ x, (min |x| a)^p ∂μ) ((2*c*2^p)*(1+1/(p-1))*T^(1-p))
      (96*c*T^(2-p)) hp hp2 hT.le ha hH (by positivity) hrow' hPY hex
      (fun e => by rw [hint e (fun x => max (|x|-T) 0) (by fun_prop)]; exact hex0.2)
      (fun e => hint e (fun x => (min |x| a)^p) (by fun_prop (disch := positivity))) he

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

def powerIntensity (p : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity (fun r => ENNReal.ofReal (p*r^(-p-1)))

lemma powerIntensity_integral (p : ℝ) (hp : 0 < p) {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) :
    (∫ r, f r ∂powerIntensity p) = ∫ r in Set.Ioi 0, (p*r^(-p-1)) • f r := by
  rw [powerIntensity, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun r => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [ENNReal.toReal_ofReal (mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt hr) _))]

lemma powerIntensity_restrict_integral (p : ℝ) (hp : 0 < p) {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Set.Ioi 0) :
    (∫ r in s, f r ∂powerIntensity p) = ∫ r in s, (p*r^(-p-1)) • f r := by
  rw [powerIntensity, restrict_withDensity hs, Measure.restrict_restrict hs,
    Set.inter_eq_left.mpr hs0,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun r => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with r hr
  have hr0 := hs0 hr
  rw [ENNReal.toReal_ofReal (mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt hr0) _))]

lemma powerIntensity_tail (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    powerIntensity p (Set.Ioi a) = ENNReal.ofReal (a^(-p)) := by
  rw [powerIntensity, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi ha.le)]
  have hn : ∀ᵐ r ∂volume.restrict (Set.Ioi a), 0 ≤ p*r^(-p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := ha.trans hr
    positivity
  have hi : IntegrableOn (fun r : ℝ => p*r^(-p-1)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p-1 < -1) ha).const_mul p
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -p-1 < -1) ha]
  congr 1
  rw [show -p-1+1 = -p by ring]
  field_simp


lemma powerIntensity_large_moment (p q a : ℝ) (hp : 0 < p) (hqp : q < p)
    (ha : 0 < a) :
    (∫ r in Set.Ioi a, r^q ∂powerIntensity p) = p/(p-q)*a^(q-p) := by
  rw [powerIntensity_restrict_integral p hp _ measurableSet_Ioi (Set.Ioi_subset_Ioi ha.le)]
  have he : (fun r : ℝ => (p*r^(-p-1)) • r^q) =ᵐ[volume.restrict (Set.Ioi a)]
      fun r => p*r^(q-p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := ha.trans hr
    simp only [smul_eq_mul, mul_assoc, ← Real.rpow_add hr0]
    congr 2
    ring
  rw [integral_congr_ae he, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : q-p-1 < -1) ha]
  rw [show q-p-1+1 = q-p by ring]
  rw [show q-p = -(p-q) by ring, neg_div_neg_eq]
  ring

lemma powerIntensity_critical_moment (p a b : ℝ) (hp : 0 < p) (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Set.Ioc a b, r^p ∂powerIntensity p) = p*Real.log (b/a) := by
  rw [powerIntensity_restrict_integral p hp _ measurableSet_Ioc
    (fun r hr => ha.trans hr.1)]
  have he : (fun r : ℝ => (p*r^(-p-1)) • r^p) =ᵐ[volume.restrict (Set.Ioc a b)]
      fun r => p*r⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := ha.trans hr.1
    simp only [smul_eq_mul, mul_assoc, ← Real.rpow_add hr0]
    rw [show -p-1+p = -1 by ring, Real.rpow_neg_one]
  rw [integral_congr_ae he, integral_const_mul, ← intervalIntegral.integral_of_le hab,
    integral_inv_of_pos ha (ha.trans_le hab)]


def stableKernel (p t r : ℝ) : ℝ := (Real.cos (t*r)-1)*r^(-p-1)

lemma stableKernel_abs_le_quadratic (p t r : ℝ) (hr : 0 < r) :
    |stableKernel p t r| ≤ (t^2/2)*r^(1-p) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := t*r)
  have he : |Real.cos (t*r)-1| ≤ (t*r)^2/2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    linarith
  calc
    |stableKernel p t r| = |Real.cos (t*r)-1| * r^(-p-1) := by
      rw [stableKernel, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    _ ≤ ((t*r)^2/2)*r^(-p-1) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = (t^2/2)*r^(1-p) := by
      have heq : r^2*r^(-p-1) = r^(1-p) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
        congr 1
        norm_num
        ring
      calc
        ((t*r)^2/2)*r^(-p-1) = (t^2/2)*(r^2*r^(-p-1)) := by ring
        _ = _ := by rw [heq]

lemma stableKernel_abs_le_large (p t r : ℝ) (hr : 0 ≤ r) :
    |stableKernel p t r| ≤ 2*r^(-p-1) := by
  rw [stableKernel, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr _)
  calc
    |Real.cos (t*r)-1| ≤ |Real.cos (t*r)| + |(1:ℝ)| := abs_sub _ _
    _ ≤ 2 := by have := Real.abs_cos_le_one (t*r); norm_num at *; linarith

lemma stableKernel_integrable (p t : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    IntegrableOn (stableKernel p t) (Set.Ioi 0) := by
  have hs : IntegrableOn (stableKernel p t) (Set.Ioc 0 1) := by
    have hi : IntegrableOn (fun r : ℝ => r^(1-p)) (Set.Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 1-p)).1
    exact (hi.const_mul (t^2/2)).mono' (by unfold stableKernel; fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simpa only [Real.norm_eq_abs] using stableKernel_abs_le_quadratic p t r hr.1)
  have hl : IntegrableOn (stableKernel p t) (Set.Ioi 1) := by
    exact ((integrableOn_Ioi_rpow_of_lt (by linarith : -p-1 < -1) zero_lt_one).const_mul 2).mono'
      (by unfold stableKernel; fun_prop) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        simpa only [Real.norm_eq_abs] using stableKernel_abs_le_large p t r (le_trans (by norm_num) (le_of_lt hr)))
  have hset : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext r
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h,_⟩|h)
      · exact h
      · linarith
    · intro h
      by_cases h' : r ≤ 1
      · exact Or.inl ⟨h,h'⟩
      · exact Or.inr (lt_of_not_ge h')
  rw [← hset]
  exact hs.union hl

lemma stableKernel_scaling_pos (p t : ℝ) (ht : 0 < t) :
    (∫ r in Set.Ioi 0, stableKernel p t r) =
      t^p * ∫ r in Set.Ioi 0, stableKernel p 1 r := by
  have he : (fun r => stableKernel p t r) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun r => t^(p+1) * stableKernel p 1 (t*r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [stableKernel, one_mul, Real.mul_rpow ht.le (le_of_lt hr)]
    rw [show t^(p+1)*((Real.cos (t*r)-1)*(t^(-p-1)*r^(-p-1))) =
      (Real.cos (t*r)-1)*((t^(p+1)*t^(-p-1))*r^(-p-1)) by ring,
      ← Real.rpow_add ht, show p+1+(-p-1) = 0 by ring, Real.rpow_zero, one_mul]
  rw [integral_congr_ae he, integral_const_mul,
    integral_comp_mul_left_Ioi (stableKernel p 1) 0 ht, mul_zero, smul_eq_mul,
    ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add ht]
  congr 2
  ring

lemma stableKernel_scaling (p t : ℝ) (hp : 0 < p) :
    (∫ r in Set.Ioi 0, stableKernel p t r) =
      |t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have he : stableKernel p t = stableKernel p (-t) := by
      funext r
      simp [stableKernel, neg_mul, Real.cos_neg]
    rw [he, stableKernel_scaling_pos p (-t) (neg_pos.mpr ht), abs_of_neg ht]
  · subst t
    simp [stableKernel, Real.zero_rpow hp.ne']
  · rw [stableKernel_scaling_pos p t ht, abs_of_pos ht]

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

section Compound
variable {E : Type uE} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

def convolutionPower (μ : Measure E) : ℕ → Measure E
  | 0 => Measure.dirac 0
  | n+1 => convolutionPower μ n ∗ μ

instance convolutionPower_probability (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convolutionPower μ n) := by
  induction n with
  | zero => dsimp [convolutionPower]; infer_instance
  | succ n ih => dsimp [convolutionPower]; infer_instance

def compoundPoisson (r : ℝ≥0) (μ : Measure E) : Measure E :=
  Measure.sum (fun n => ENNReal.ofReal (Real.exp (-r)*r^n/(n.factorial)) • convolutionPower μ n)

instance compoundPoisson_probability (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoisson r μ) := by
  constructor
  simp only [compoundPoisson, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq]
  simp

omit [MeasurableAdd₂ E] in
omit [MeasurableAdd₂ E] in
lemma integral_compoundPoisson {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ≥0) (μ : Measure E) (f : E → F) (hf : Integrable f (compoundPoisson r μ)) :
    (∫ x, f x ∂compoundPoisson r μ) =
      ∑' n, (Real.exp (-r)*r^n/(n.factorial):ℝ) • ∫ x, f x ∂convolutionPower μ n := by
  rw [compoundPoisson, integral_sum_measure hf]
  congr with n
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

lemma convolutionPower_map {F : Type uF} [AddCommMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (μ : Measure E) [IsProbabilityMeasure μ] (L : E →+ F) (hL : Measurable L) (n : ℕ) :
    (convolutionPower μ n).map L = convolutionPower (μ.map L) n := by
  have : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map hL.aemeasurable
  induction n with
  | zero => simp [convolutionPower, Measure.map_dirac' hL 0]
  | succ n ih => rw [convolutionPower, Measure.map_conv_addMonoidHom L hL, ih, convolutionPower]


end Compound

section Characteristic
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma charFun_convolutionPower (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (t : E) :
    charFun (convolutionPower μ n) t = (charFun μ t)^n := by
  induction n with
  | zero => simp [convolutionPower, charFun_dirac]
  | succ n ih => rw [convolutionPower, charFun_conv, ih, pow_succ]

lemma charFun_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    charFun (compoundPoisson r μ) t = Complex.exp (r * (charFun μ t-1)) := by
  rw [charFun_apply, integral_compoundPoisson]
  · simp only [← charFun_apply, charFun_convolutionPower, Complex.real_smul]
    calc
      (∑' n, (Real.exp (-r)*r^n/(n.factorial):ℝ)*(charFun μ t)^n) =
          (Real.exp (-r):ℂ) * ∑' n, ((r:ℂ)*charFun μ t)^n/(n.factorial) := by
        rw [← tsum_mul_left]
        congr with n
        push_cast
        ring
      _ = (Real.exp (-r):ℂ)*Complex.exp ((r:ℂ)*charFun μ t) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFun μ t)).tsum_eq, Complex.exp_eq_exp_ℂ]
      _ = _ := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])

end Characteristic

lemma exp_integrable_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (hμ : Integrable (fun x => Real.exp (t*x)) μ)
    (hν : Integrable (fun x => Real.exp (t*x)) ν) :
    Integrable (fun x => Real.exp (t*x)) (μ ∗ ν) := by
  rw [integrable_conv_iff (by fun_prop)]
  constructor
  · exact ae_of_all _ fun x => by
      simpa only [mul_add, Real.exp_add] using hν.const_mul (Real.exp (t*x))
  · simp only [Real.norm_eq_abs]
    simp_rw [abs_of_pos (Real.exp_pos _), mul_add, Real.exp_add, integral_const_mul]
    exact hμ.mul_const _

lemma exp_integral_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (hμ : Integrable (fun x => Real.exp (t*x)) μ)
    (hν : Integrable (fun x => Real.exp (t*x)) ν) :
    (∫ x, Real.exp (t*x) ∂(μ ∗ ν)) =
      (∫ x, Real.exp (t*x) ∂μ) * ∫ x, Real.exp (t*x) ∂ν := by
  rw [integral_conv (exp_integrable_conv μ ν t hμ hν)]
  simp only [mul_add, Real.exp_add, integral_const_mul, integral_mul_const]

lemma exp_convolutionPower (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ)
    (hμ : Integrable (fun x => Real.exp (t*x)) μ) (n : ℕ) :
    Integrable (fun x => Real.exp (t*x)) (convolutionPower μ n) ∧
    (∫ x, Real.exp (t*x) ∂convolutionPower μ n) = (∫ x, Real.exp (t*x) ∂μ)^n := by
  induction n with
  | zero => exact ⟨integrable_dirac (by simp), by simp [convolutionPower]⟩
  | succ n ih =>
    exact ⟨exp_integrable_conv _ _ t ih.1 hμ, by
      rw [convolutionPower, exp_integral_conv _ _ t ih.1 hμ, ih.2, pow_succ]⟩


lemma bounded_exp_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (B : ℝ)
    (hB : ∀ᵐ x ∂μ, |x| ≤ B) (t : ℝ) : Integrable (fun x => Real.exp (t*x)) μ := by
  apply (integrable_const (Real.exp (|t| * B))).mono' (by fun_prop)
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc t*x ≤ |t*x| := le_abs_self _
       _ = |t| * |x| := abs_mul _ _
       _ ≤ |t| * B := mul_le_mul_of_nonneg_left hx (abs_nonneg _)


def symmetrize (μ : Measure ℝ) : Measure ℝ :=
  (2:ℝ≥0∞)⁻¹ • μ + (2:ℝ≥0∞)⁻¹ • μ.map Neg.neg

instance symmetrize_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetrize μ) := by
  have : IsProbabilityMeasure (μ.map Neg.neg) := Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  constructor
  simp [symmetrize, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

lemma integral_symmetrize {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure ℝ) (f : ℝ → F) (hf : Integrable f μ)
    (hn : Integrable (fun x => f (-x)) μ) :
    (∫ x, f x ∂symmetrize μ) = (1/2:ℝ) • ((∫ x, f x ∂μ)+(∫ x, f (-x) ∂μ)) := by
  have hmap : Integrable f (μ.map Neg.neg) :=
    (measurableEmbedding_neg.integrable_map_iff).mpr hn
  rw [symmetrize, integral_add_measure (hf.smul_measure (by norm_num))
    (hmap.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure,
    integral_map (by fun_prop) hmap.aestronglyMeasurable]
  norm_num [ENNReal.toReal_inv, div_eq_inv_mul, smul_add]

lemma charFun_symmetrize (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (symmetrize μ) t = (∫ x, Real.cos (t*x) ∂μ : ℝ) := by
  rw [charFun_apply_real, integral_symmetrize]
  · rw [← integral_add]
    · rw [← integral_smul, ← integral_complex_ofReal]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        simp only [Complex.real_smul]
        simp only [Complex.ofReal_neg, mul_neg]
        rw [Complex.exp_mul_I, Complex.exp_mul_I]
        simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_mul,
          ← Complex.ofReal_cos]
        push_cast
        ring
    · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])
    · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma exists_probability_charFun_limit
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ) (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (f t))) :
    ∃ ν : ProbabilityMeasure E, (∀ t, charFun ν t = f t) ∧ Tendsto μ atTop (𝓝 ν) := by
  have ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure E))) :=
    isTightMeasureSet_of_tendsto_charFun hf h
  have hc : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by convert! ht using 1; ext x; simp)
  obtain ⟨ν, _, φ, hφ, hν⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hcf : ∀ t, charFun ν t = f t := by
    intro t
    exact tendsto_nhds_unique
      ((ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hν) t)
      ((h t).comp hφ.tendsto_atTop)
  refine ⟨ν, hcf, ProbabilityMeasure.tendsto_of_tendsto_charFun (fun t => ?_)⟩
  simpa only [hcf] using h t


def paretoJump (p a : ℝ) : Measure ℝ :=
  ENNReal.ofReal (a^p) • (powerIntensity p).restrict (Set.Ioi a)

lemma paretoJump_probability (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    IsProbabilityMeasure (paretoJump p a) := by
  constructor
  simp only [paretoJump, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    powerIntensity_tail p a hp ha]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le p), ← Real.rpow_add ha,
    add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one]

lemma paretoJump_cos_exponent (p a t : ℝ) (hp : 0 < p) (ha : 0 < a) :
    a^(-p) * ((∫ r, Real.cos (t*r) ∂paretoJump p a)-1) =
      p * ∫ r in Set.Ioi a, stableKernel p t r := by
  have := paretoJump_probability p a hp ha
  have hi : Integrable (fun r => Real.cos (t*r)) (paretoJump p a) :=
    (integrable_const (1:ℝ)).mono' (by fun_prop) (ae_of_all _ (fun r => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*r)))
  have hc : (∫ _ : ℝ, (1:ℝ) ∂paretoJump p a) = 1 := by simp
  rw [← hc, ← integral_sub hi (integrable_const _)]
  rw [paretoJump, integral_smul_measure, ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _),
    smul_eq_mul, ← mul_assoc, ← Real.rpow_add ha, neg_add_cancel, Real.rpow_zero, one_mul,
    powerIntensity_restrict_integral p hp _ measurableSet_Ioi (Set.Ioi_subset_Ioi ha.le)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by simp only [stableKernel, smul_eq_mul]; ring)

def stableApprox (p a : ℝ) : Measure ℝ :=
  compoundPoisson (Real.toNNReal (a^(-p))) (symmetrize (paretoJump p a))

lemma stableApprox_probability (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    IsProbabilityMeasure (stableApprox p a) := by
  have := paretoJump_probability p a hp ha
  unfold stableApprox
  infer_instance

lemma charFun_stableApprox (p a t : ℝ) (hp : 0 < p) (ha : 0 < a) :
    charFun (stableApprox p a) t =
      Complex.exp (p * ∫ r in Set.Ioi a, stableKernel p t r) := by
  have := paretoJump_probability p a hp ha
  rw [stableApprox, charFun_compoundPoisson, charFun_symmetrize,
    Real.coe_toNNReal _ (Real.rpow_nonneg ha.le _)]
  congr 1
  norm_cast
  exact paretoJump_cos_exponent p a t hp ha

lemma positive_cutoff_union :
    (⋃ n : ℕ, Set.Ioi ((n+1:ℝ)⁻¹)) = Set.Ioi (0:ℝ) := by
  ext r
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn⟩
    exact lt_trans (by positivity) hn
  · intro hr
    obtain ⟨n, hn⟩ := exists_nat_gt r⁻¹
    refine ⟨n, ?_⟩
    have h : r⁻¹ < (n:ℝ)+1 := by linarith
    have h' := (inv_lt_inv₀ (by positivity : (0:ℝ) < n+1) (inv_pos.mpr hr)).mpr h
    simpa using h'

lemma stableKernel_cutoff_limit (p t : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    Tendsto (fun n : ℕ => ∫ r in Set.Ioi ((n+1:ℝ)⁻¹), stableKernel p t r)
      atTop (𝓝 (|t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r)) := by
  rw [← stableKernel_scaling p t hp]
  have hi : IntegrableOn (stableKernel p t) (⋃ n : ℕ, Set.Ioi ((n+1:ℝ)⁻¹)) := by
    rw [positive_cutoff_union]
    exact stableKernel_integrable p t hp hp2
  have hm : Monotone (fun n : ℕ => Set.Ioi ((n+1:ℝ)⁻¹)) := by
    intro n m hnm
    apply Set.Ioi_subset_Ioi
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  simpa only [positive_cutoff_union] using
    tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioi) hm hi

lemma exists_stable_law (p : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ t : ℝ,
      charFun μ t = Complex.exp ((p * |t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r : ℝ) : ℂ) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun n => ⟨stableApprox p ((n+1:ℝ)⁻¹),
    stableApprox_probability p _ hp (by positivity)⟩
  have h : ∀ t : ℝ, Tendsto (fun n => charFun (μ n) t) atTop
      (𝓝 (Complex.exp ((p * |t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r : ℝ) : ℂ))) := by
    intro t
    have he : ∀ n, charFun (μ n) t =
        Complex.exp ((p * ∫ r in Set.Ioi ((n+1:ℝ)⁻¹), stableKernel p t r : ℝ) : ℂ) := by
      intro n
      simpa only [μ, ProbabilityMeasure.coe_mk, Complex.ofReal_mul] using
        charFun_stableApprox p ((n+1:ℝ)⁻¹) t hp (by positivity)
    simp_rw [he]
    have ht := (Complex.continuous_exp.tendsto _).comp
      (Complex.continuous_ofReal.tendsto _ |>.comp ((stableKernel_cutoff_limit p t hp hp2).const_mul p))
    simpa only [Function.comp_def, mul_assoc] using ht
  obtain ⟨ν, hν, _⟩ := exists_probability_charFun_limit μ _ (by
    apply Continuous.continuousAt
    fun_prop (disch := positivity)) h
  exact ⟨ν, hν⟩

def stableConstant (p : ℝ) : ℝ := -p * ∫ r in Set.Ioi 0, stableKernel p 1 r

lemma stableConstant_pos (p : ℝ) (hp : 0 < p) (hp2 : p < 2) : 0 < stableConstant p := by
  have hi := (stableKernel_integrable p 1 hp hp2).neg
  have hn : ∀ᵐ r ∂volume.restrict (Set.Ioi (0:ℝ)), 0 ≤ -stableKernel p 1 r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    unfold stableKernel
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (Real.cos_le_one _)) (Real.rpow_nonneg (le_of_lt hr) _))
  have hsub : Set.Ioo (Real.pi/2) Real.pi ⊆ Function.support (fun r => -stableKernel p 1 r) := by
    intro r hr
    have hr0 : 0 < r := Real.pi_div_two_pos.trans hr.1
    have hc : Real.cos r < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hr.1
      (hr.2.trans (by linarith [Real.pi_pos]))
    show -stableKernel p 1 r ≠ 0
    apply ne_of_gt
    unfold stableKernel
    simp only [one_mul]
    exact neg_pos.mpr (mul_neg_of_neg_of_pos (by linarith) (Real.rpow_pos_of_pos hr0 _))
  have hm : 0 < (volume.restrict (Set.Ioi (0:ℝ))) (Set.Ioo (Real.pi/2) Real.pi) := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (show Set.Ioo (Real.pi/2) Real.pi ⊆ Set.Ioi (0:ℝ) from
        fun r hr => Real.pi_div_two_pos.trans hr.1), Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  have hpos := (integral_pos_iff_support_of_nonneg_ae hn hi).mpr
    (lt_of_lt_of_le hm (measure_mono hsub))
  rw [integral_neg] at hpos
  unfold stableConstant
  nlinarith


lemma exists_stable_law_full (p : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ t : ℝ,
      charFun μ t = Complex.exp ((-stableConstant p*|t|^p:ℝ):ℂ) := by
  obtain ⟨μ,hμ⟩ := exists_stable_law p hp hp2
  refine ⟨μ,fun t => ?_⟩
  rw [hμ]
  congr 2
  unfold stableConstant
  ring

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma below_error_algebra (p c T H : ℝ) (hT : 0 < T) (hH : 0 < H) :
    (p*(T/H)^(p-1))*H*((2*c*2^p)*(1+1/(p-1))*T^(1-p))+
      (T/H)^(p-2)*(96*c*T^(2-p)) =
    (p*(2*c*2^p)*(1+1/(p-1))+96*c)*H^(2-p) := by
  have h₁ : T^(p-1)*T^(1-p) = 1 := by rw [← Real.rpow_add hT]; simp
  have h₂ : T^(p-2)*T^(2-p) = 1 := by rw [← Real.rpow_add hT]; simp
  have h₃ : H/H^(p-1) = H^(2-p) := by
    conv_lhs => lhs; rw [← Real.rpow_one H]
    rw [← Real.rpow_sub hH]
    congr 1
    ring
  have h₄ : 1/H^(p-2) = H^(2-p) := by rw [one_div, ← Real.rpow_neg hH.le]; congr 1; ring
  rw [Real.div_rpow hT.le hH.le, Real.div_rpow hT.le hH.le]
  calc
    _ = (p*(2*c*2^p)*(1+1/(p-1)))*(H/H^(p-1))*(T^(p-1)*T^(1-p))+
      (96*c)*(1/H^(p-2))*(T^(p-2)*T^(2-p)) := by ring
    _ = _ := by rw [h₁,h₂,h₃,h₄]; ring

lemma stable_gradient_weighted {ι : Type uι} {E : Type uE} {V : Type uV} [Fintype ι]
    [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] [Nonempty E]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hc : 0 < c) (hcf : ∀ t : ℝ, charFun μ t = Complex.exp ((-c*|t|^p:ℝ):ℂ))
    (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (g : ι → E → ℝ) (hgV : ∀ i, ∃ z, (normalizedGradient src dst δ).mulVec z = g i)
    (hg : ∀ e, ∑ i, |g i e|^p = 1)
    (T : ℝ) (hT : 0 < T) :
    let H := 4*Real.log (Fintype.card V:ℝ)
    ∃ F : (ι → ℝ) → E → ℝ, Measurable F ∧
      (∀ x, ∃ z, (normalizedGradient src dst δ).mulVec z = F x) ∧
      (∀ x e, |F x e| ≤ H*T) ∧
      (∑ e, lam e*|(∫ x, |F x e|^p ∂Measure.pi (fun _ : ι => μ))-
        (∫ x, (min |x| (T/H))^p ∂μ)|) ≤
        (p*(2*c*2^p)*(1+1/(p-1))+96*c)*H^(2-p) := by
  classical
  dsimp only
  let A := normalizedGradient src dst δ
  let V' : Submodule ℝ (E → ℝ) := LinearMap.range A.mulVecLin
  have hgV' (i : ι) : g i ∈ V' := hgV i
  obtain ⟨Y,hYm,hYV,hYLaw⟩ := stable_joint_gradient μ p c (by linarith) hcf V' g hgV' hg
  have hH : 0 < 4*Real.log (Fintype.card V:ℝ) := by
    apply mul_pos (by norm_num)
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < Fintype.card V))
  obtain ⟨F,hFm,hFV,hFb,hFerr⟩ := stable_retraction_moments
    (Measure.pi (fun _ : ι => μ)) μ p c hp hp2 hc
    (fun t => by rw [hcf, Complex.exp_ofReal_re])
    src dst δ lam hδ hlam hls hcard hinc hconn Y hYm hYV hYLaw T
    (T/(4*Real.log (Fintype.card V:ℝ))) hT (div_pos hT hH)
  refine ⟨F,hFm,hFV,hFb,?_⟩
  rwa [below_error_algebra p c T _ hT hH] at hFerr


lemma moment_integral_mem {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set (E → ℝ)) (F : Ω → E → ℝ)
    (hF : Measurable F) (hFS : ∀ x, F x ∈ S) (M : ℝ)
    (hM : ∀ x e, ‖F x e‖ ≤ M) :
    (fun e => ∫ x, F x e ∂μ) ∈ closedConvexHull ℝ S := by
  have hi (e : E) : Integrable (fun x => F x e) μ :=
    Integrable.of_bound ((measurable_pi_apply e).comp hF).aestronglyMeasurable M (Filter.Eventually.of_forall (fun x => hM x e))
  have hiv : Integrable F μ := integrable_pi_iff.mpr hi
  have hh := convex_closedConvexHull.integral_mem (isClosed_closedConvexHull (𝕜 := ℝ) (s := S))
    (Filter.Eventually.of_forall fun x => subset_closedConvexHull (hFS x)) hiv
  have he : (∫ x, F x ∂μ) = fun e => ∫ x, F x e ∂μ := by
    ext e
    exact ((ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).integral_comp_comm hiv).symm
  rwa [he] at hh

lemma weighted_gradient_samples {Ω : Type uΩ} {E : Type uE} {V : Type uV} [MeasurableSpace Ω]
    [Fintype E] [Fintype V] [Nonempty E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix E V ℝ) (p K b ε : ℝ) (hp : 0 < p) (hK : 0 ≤ K) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ F : Ω → E → ℝ, Measurable F ∧
        (∀ x, ∃ z, A.mulVec z = F x) ∧ (∀ x e, |F x e| ≤ K) ∧
        (∑ e, w e*|(∫ x, |F x e|^p ∂μ)-b|) ≤ ε)
    (d : ℕ) (hd : 0 < d)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1) :
    ∃ z : Fin d → V → ℝ, ∀ e,
      |(∑ a, |A.mulVec (z a) e|^p)/(d:ℝ)-b| < 3*ε := by
  classical
  let S : Set (E → ℝ) := {m | ∃ z : V → ℝ,
    (∀ e, |A.mulVec z e| ≤ K) ∧ ∀ e, m e = |A.mulVec z e|^p}
  have hS : ∀ m ∈ S, ∀ e, m e ∈ Set.Icc 0 (K^p) := by
    rintro m ⟨z,hz,rflz⟩ e
    rw [rflz e]
    exact ⟨Real.rpow_nonneg (abs_nonneg _) _, Real.rpow_le_rpow (abs_nonneg _) (hz e) hp.le⟩
  have hw' : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ m ∈ closedConvexHull ℝ S, (∑ e, w e*|m e-b|) ≤ ε := by
    intro w hw0 hws
    obtain ⟨F,hFm,hFV,hFb,hFe⟩ := hw w hw0 hws
    refine ⟨fun e => ∫ x, |F x e|^p ∂μ, ?_, hFe⟩
    refine moment_integral_mem μ S (fun x e => |F x e|^p) (by fun_prop) ?_ (K^p) ?_
    · intro x
      obtain ⟨z,hz⟩ := hFV x
      exact ⟨z, by simpa only [hz] using hFb x, fun e => by rw [hz]⟩
    · intro x e
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hFb x e) hp.le
  obtain ⟨m,hm,hme⟩ := weighted_moments_samples (S := S) (K^p)
    (Real.rpow_nonneg hK _) hS b ε hε hw' d hd hprob
  choose z hz hmz using hm
  refine ⟨z,fun e => ?_⟩
  simpa only [hmz] using hme e

instance pairIndexDecidableEq (n : ℕ) : DecidableEq (PairIndex n) := by
  unfold PairIndex
  infer_instance

lemma pairIndex_nonempty (n : ℕ) (hn : 2 ≤ n) : Nonempty (PairIndex n) :=
  ⟨⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0:ℕ) < 1; omega⟩⟩

lemma pairIndex_connected (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∃ e : PairIndex n, (e.val.1 = i ∧ e.val.2 = j) ∨ (e.val.1 = j ∧ e.val.2 = i) := by
  rcases lt_or_gt_of_ne hij with h|h
  · exact ⟨⟨(i,j),h⟩,Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨⟨(j,i),h⟩,Or.inr ⟨rfl,rfl⟩⟩

lemma pairIndex_incident (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    ∃ e : PairIndex n, e.val.1 = i ∨ e.val.2 = i := by
  let j : Fin n := if i.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    dsimp [j] at hh
    split_ifs at hh with hi
    · change i.val = 1 at hh
      omega
    · change i.val = 0 at hh
      exact hi hh
  obtain ⟨e,h|h⟩ := pairIndex_connected n i j hij
  · exact ⟨e,Or.inl h.1⟩
  · exact ⟨e,Or.inr h.2⟩

lemma normalizedGradient_apply {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq V] (src dst : E → V) (δ : E → ℝ)
    (z : V → ℝ) (e : E) :
    (normalizedGradient src dst δ).mulVec z e = (z (src e)-z (dst e))/δ e := by
  rw [normalizedGradient, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, incidence_mulVec]
  simp [div_eq_mul_inv, mul_comm]

lemma normalized_coordinate_gradient (p : ℝ) (hp : 0 < p) {n k : ℕ}
    (y : Fin n → Fin k → ℝ) (δ : PairIndex n → ℝ) (hδ : ∀ e, 0 < δ e)
    (hy : ∀ e : PairIndex n, coordinateDistance p (y e.val.1) (y e.val.2) = δ e) :
    ∀ e : PairIndex n, ∑ a : Fin k,
      |(normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ).mulVec
        (fun i => y i a) e|^p = 1 := by
  classical
  intro e
  simp_rw [normalizedGradient_apply, abs_div, abs_of_pos (hδ e),
    Real.div_rpow (abs_nonneg _) (hδ e).le]
  rw [← Finset.sum_div]
  have hh := congrArg (fun t : ℝ => t^p) (hy e)
  rw [coordinateDistance_rpow p hp] at hh
  change (∑ a, |y e.val.1 a-y e.val.2 a|^p) = (δ e)^p at hh
  rw [hh, div_self (Real.rpow_pos_of_pos (hδ e) _).ne']

lemma sampled_labels_embedding (p D b ε : ℝ) (hp : 0 < p) (hD : 0 ≤ D)
    (hb : 0 < b-3*ε) (hDb : b+3*ε ≤ D^p*(b-3*ε))
    {n d : ℕ} (hd : 0 < d) (δ : PairIndex n → ℝ) (hδ : ∀ e, 0 < δ e)
    (z : Fin d → Fin n → ℝ)
    (hz : ∀ e : PairIndex n,
      |(∑ a, |(normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ).mulVec
        (z a) e|^p)/(d:ℝ)-b| < 3*ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ e : PairIndex n,
      s*δ e ≤ coordinateDistance p (fun a => z a e.val.1) (fun a => z a e.val.2) ∧
      coordinateDistance p (fun a => z a e.val.1) (fun a => z a e.val.2) ≤ D*s*δ e := by
  classical
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  let s := ((d:ℝ)*(b-3*ε))^(1/p)
  have hs : 0 < s := Real.rpow_pos_of_pos (mul_pos hd0 hb) _
  have hsp : s^p = (d:ℝ)*(b-3*ε) := by
    dsimp [s]
    rw [← Real.rpow_mul (mul_pos hd0 hb).le, one_div_mul_cancel hp.ne', Real.rpow_one]
  refine ⟨s,hs,fun e => ?_⟩
  let m := ∑ a, |(normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ).mulVec (z a) e|^p
  have hm : (d:ℝ)*(b-3*ε) ≤ m ∧ m ≤ (d:ℝ)*(b+3*ε) := by
    have he := abs_lt.mp (hz e)
    constructor
    · have hh : b-3*ε ≤ m/d := by dsimp [m]; linarith [he.1]
      simpa only [mul_comm] using (le_div_iff₀ hd0).mp hh
    · have hh : m/d ≤ b+3*ε := by dsimp [m]; linarith [he.2]
      simpa only [mul_comm] using (div_le_iff₀ hd0).mp hh
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : (∑ a, |z a e.val.1-z a e.val.2|^p) = (δ e)^p*m := by
    dsimp [m]
    simp_rw [normalizedGradient_apply, abs_div, abs_of_pos (hδ e), Real.div_rpow (abs_nonneg _) (hδ e).le]
    rw [← Finset.sum_div, mul_div_cancel₀ _ (Real.rpow_pos_of_pos (hδ e) p).ne']
  have hdist : coordinateDistance p (fun a => z a e.val.1) (fun a => z a e.val.2) = δ e*m^(1/p) := by
    rw [coordinateDistance, hsum, Real.mul_rpow (Real.rpow_nonneg (hδ e).le _) hm0,
      ← Real.rpow_mul (hδ e).le, mul_one_div_cancel hp.ne', Real.rpow_one]
  rw [hdist]
  constructor
  · have hh := Real.rpow_le_rpow (mul_pos hd0 hb).le hm.1 (by positivity : 0 ≤ 1/p)
    dsimp [s] at *
    nlinarith [mul_nonneg (hδ e).le (sub_nonneg.mpr hh)]
  · have hh : m ≤ (D*s)^p := by
      rw [Real.mul_rpow hD hs.le, hsp]
      have ht := mul_le_mul_of_nonneg_left hDb hd0.le
      nlinarith [hm.2]
    have ht := Real.rpow_le_rpow hm0 hh (by positivity : 0 ≤ 1/p)
    rw [← Real.rpow_mul (mul_nonneg hD hs.le), mul_one_div_cancel hp.ne', Real.rpow_one] at ht
    nlinarith [mul_nonneg (hδ e).le (sub_nonneg.mpr ht)]


lemma distortion_ratio (p D : ℝ) (hp : 0 < p) (hD : 1 < D) :
    ∃ R : ℝ, 3 < R ∧ ∀ b ε : ℝ, 0 < ε → R*ε ≤ b →
      0 < b-3*ε ∧ b+3*ε ≤ D^p*(b-3*ε) := by
  have hd : 1 < D^p := Real.one_lt_rpow hD hp
  let R := 3+6/(D^p-1)
  have hR : 3 < R := by
    have hh : 0 < 6/(D^p-1) := by positivity
    dsimp [R]; linarith
  have hReq : R*(D^p-1) = 3*(D^p+1) := by
    dsimp [R]
    field_simp [show D^p-1 ≠ 0 by linarith]
    ring
  refine ⟨R,hR,fun b ε hε hb => ⟨?_,?_⟩⟩
  · have hh := mul_lt_mul_of_pos_right hR hε
    linarith
  · have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ D^p-1 by linarith)
    nlinarith

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma log_nat_lower (n : ℕ) (hn : 2 ≤ n) : (1/2:ℝ) ≤ Real.log n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hh := Real.one_sub_inv_le_log_of_pos hn0
  have hi : (n:ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hn2
  linarith

lemma sampling_dimension_estimate (p r A : ℝ) (hp : 0 < p) (hr : 0 < r) (hA : 0 ≤ A)
    (n : ℕ) (hn : 2 ≤ n) :
    let H := 4*Real.log (n:ℝ)
    let K := H^2*Real.exp (A*(H^r+1))
    let d := ⌈(K^p)^2*(H+1)⌉₊+1
    (d:ℝ) ≤ Real.exp ((3+(4*p+1)/r+4*p*A)*4^r*(Real.log (n:ℝ))^r) := by
  dsimp only
  let H := 4*Real.log (n:ℝ)
  let K := H^2*Real.exp (A*(H^r+1))
  have hL := log_nat_lower n hn
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHr : 1 ≤ H^r := Real.one_le_rpow hH hr.le
  have hK : 1 ≤ K := by
    have he : 1 ≤ Real.exp (A*(H^r+1)) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp [K]
    nlinarith [sq_nonneg (H-1)]
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hM : 1 ≤ K^p := Real.one_le_rpow hK hp.le
  have hX : 1 ≤ (K^p)^2*(H+1) := by nlinarith [sq_nonneg (K^p-1)]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (K^p)^2*(H+1) by positivity)
  have hd : (⌈(K^p)^2*(H+1)⌉₊+1:ℕ) ≤ (3:ℝ)*((K^p)^2*(H+1)) := by
    push_cast
    nlinarith
  have hlogH : Real.log H ≤ H^r/r := Real.log_le_rpow_div hH0.le hr
  have hlogK : Real.log K ≤ (2/r+2*A)*H^r := by
    rw [show K = H^2*Real.exp (A*(H^r+1)) from rfl,
      Real.log_mul (pow_ne_zero _ hH0.ne') (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    have he := mul_le_mul_of_nonneg_left hHr hA
    simp only [div_eq_mul_inv] at hlogH ⊢
    nlinarith
  have hlogHp : Real.log (H+1) ≤ (1+1/r)*H^r := by
    have hh := Real.log_le_log (by positivity : 0 < H+1) (show H+1 ≤ 2*H by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hH0.ne'] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    simp only [div_eq_mul_inv] at hlogH ⊢
    nlinarith
  have hlog3 : Real.log (3:ℝ) ≤ 2*H^r := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    nlinarith
  have hlog : Real.log (3*((K^p)^2*(H+1))) ≤ (3+(4*p+1)/r+4*p*A)*H^r := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hK0]
    have hh := mul_le_mul_of_nonneg_left hlogK (by positivity : 0 ≤ 2*p)
    calc
      _ ≤ 2*H^r+(2*p)*((2/r+2*A)*H^r)+(1+1/r)*H^r := by linarith
      _ = _ := by ring
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity)] at he
  have hHr' : H^r = 4^r*(Real.log (n:ℝ))^r := by
    exact Real.mul_rpow (by norm_num) (by linarith)
  have ht := hd.trans he
  rw [hHr'] at ht
  simpa only [mul_assoc] using ht

lemma sampling_probability_estimate (M ε : ℝ) (hM : 0 < M) (hε : 1 ≤ ε)
    (n N : ℕ) (hn : 2 ≤ n) (hN : 0 < N) (hNn : N ≤ n^2) :
    let H := 4*Real.log (n:ℝ)
    let d := ⌈M^2*(H+1)⌉₊+1
    (2*N:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1 := by
  dsimp only
  let H := 4*Real.log (n:ℝ)
  let d := ⌈M^2*(H+1)⌉₊+1
  have hL := log_nat_lower n hn
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hd : (0:ℝ) < d := by dsimp [d]; positivity
  have hdM : M^2*(H+1) ≤ (d:ℝ) := by
    have hh := Nat.le_ceil (M^2*(H+1))
    dsimp [d]
    push_cast
    linarith
  have heps : 1 ≤ ε^2 := by nlinarith
  have halg : -((d:ℝ)*ε)^2/(2*d*(M/2)^2) = -(2*(d:ℝ)*ε^2/M^2) := by
    field_simp
  have hexp : -((d:ℝ)*ε)^2/(2*d*(M/2)^2) ≤ -2*(H+1) := by
    rw [halg]
    have hh : 2*(H+1) ≤ 2*(d:ℝ)*ε^2/M^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
      have ht := mul_le_mul_of_nonneg_left heps hd.le
      nlinarith
    linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (2*(N:ℝ)) ≤ 1+2*Real.log (n:ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < 2*(N:ℝ))
      (show 2*(N:ℝ) ≤ 2*(n:ℝ)^2 by exact_mod_cast Nat.mul_le_mul_left 2 hNn)
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), Real.log_pow] at hh
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh
    linarith
  change (2*(N:ℝ))*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1
  calc
    _ = Real.exp (Real.log (2*(N:ℝ))+-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
    _ < 1 := Real.exp_lt_one_iff.mpr (by dsimp [H] at hexp; linarith)

lemma coordinateDistance_comm (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) :
    coordinateDistance p x y = coordinateDistance p y x := by
  unfold coordinateDistance
  congr 1
  exact Finset.sum_congr rfl (fun a _ => by rw [abs_sub_comm])

lemma coordinateDistance_self (p : ℝ) (hp : 0 < p) {d : ℕ} (x : Fin d → ℝ) :
    coordinateDistance p x x = 0 := by
  simp [coordinateDistance, Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]

lemma all_pairs_of_edge_bounds {X : Type uX} [SeminormedAddCommGroup X] (p D s : ℝ) (hp : 0 < p)
    {n d : ℕ} (x : Fin n → X) (y : Fin n → Fin d → ℝ)
    (h : ∀ e : PairIndex n,
      s*‖x e.val.1-x e.val.2‖ ≤ coordinateDistance p (y e.val.1) (y e.val.2) ∧
      coordinateDistance p (y e.val.1) (y e.val.2) ≤ D*s*‖x e.val.1-x e.val.2‖) :
    ∀ i j, s*‖x i-x j‖ ≤ coordinateDistance p (y i) (y j) ∧
      coordinateDistance p (y i) (y j) ≤ D*s*‖x i-x j‖ := by
  intro i j
  rcases lt_trichotomy i j with hij|hij|hij
  · exact h ⟨(i,j),hij⟩
  · subst j
    simp [coordinateDistance_self p hp]
  · have hh := h ⟨(j,i),hij⟩
    simpa only [coordinateDistance_comm p (y j), norm_sub_rev (x j)] using hh

lemma pairIndex_card_le_square (n : ℕ) : Fintype.card (PairIndex n) ≤ n^2 := by
  calc
    _ ≤ Fintype.card (Fin n × Fin n) := Fintype.card_subtype_le _
    _ = n^2 := by simp [pow_two]

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma below_main_upper (p D : ℝ) (hp : 1 < p) (hp2 : p < 2) (hD : 1 < D) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C*(Real.log (n:ℝ))^(2-p)) := by
  classical
  have hp0 : 0 < p := by linarith
  let c := stableConstant p
  have hc : 0 < c := stableConstant_pos p hp0 hp2
  obtain ⟨μ,hμ⟩ := exists_stable_law_full p hp0 hp2
  obtain ⟨k,hk,hTail⟩ := stable_tail_lower (μ : Measure ℝ) p c hp0 hp2 hc
    (fun t => by rw [hμ t, Complex.exp_ofReal_re])
  obtain ⟨R,hR,hRD⟩ := distortion_ratio p D hp0 hD
  let C0 := p*(2*c*2^p)*(1+1/(p-1))+96*c
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  let A := R*(C0+1)/(k*p)
  have hA : 0 < A := by dsimp [A]; positivity
  let C := (3+(4*p+1)/(2-p)+4*p*A)*4^(2-p)
  refine ⟨C,fun n hn => ?_⟩
  let H := 4*Real.log (n:ℝ)
  have hH : 0 < H := by
    have hh := log_nat_lower n hn
    dsimp [H]; linarith
  let T := H*Real.exp (A*(H^(2-p)+1))
  have hT : 0 < T := by dsimp [T]; positivity
  let K := H^2*Real.exp (A*(H^(2-p)+1))
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := (C0+1)*(H^(2-p)+1)
  have hε1 : 1 ≤ ε := by
    have ht : 0 ≤ H^(2-p) := Real.rpow_nonneg hH.le _
    dsimp [ε]
    nlinarith
  have hε : 0 < ε := zero_lt_one.trans_le hε1
  let b := ∫ x, (min |x| (T/H))^p ∂(μ:Measure ℝ)
  have ha : 1 ≤ T/H := by
    dsimp [T]
    rw [mul_div_cancel_left₀ _ hH.ne']
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hbR : R*ε ≤ b := by
    have hh := capped_moment_lower_log (μ:Measure ℝ) p k (T/H) hp hk.le ha hTail
    have he : k*p*Real.log (T/H) = R*ε := by
      dsimp [T]
      rw [mul_div_cancel_left₀ _ hH.ne', Real.log_exp]
      dsimp [A, ε]
      field_simp
    rwa [he] at hh
  obtain ⟨hb,hDb⟩ := hRD b ε hε hbR
  let d := ⌈(K^p)^2*(H+1)⌉₊+1
  have hd : 0 < d := by dsimp [d]; omega
  have hgood : GoodDimension.{u} p n D d := by
    intro Ω mΩ ν x hx
    let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    let : Nonempty (PairIndex n) := pairIndex_nonempty n hn
    obtain ⟨y,hy⟩ := exact_discretization p hp n hn ν x hx
    let δ : PairIndex n → ℝ := fun e => ‖x e.val.1-x e.val.2‖
    have hδ (e : PairIndex n) : 0 < δ e :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => (ne_of_lt e.2) (hx he)))
    let B := normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ
    let g : Fin (n.choose 2) → PairIndex n → ℝ := fun a => B.mulVec (fun i => y i a)
    have hg : ∀ e, ∑ a, |g a e|^p = 1 :=
      normalized_coordinate_gradient p hp0 y δ hδ (fun e => hy e.val.1 e.val.2)
    have hw : ∀ w : PairIndex n → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
        ∃ F : (Fin (n.choose 2) → ℝ) → PairIndex n → ℝ, Measurable F ∧
          (∀ r, ∃ z, B.mulVec z = F r) ∧ (∀ r e, |F r e| ≤ K) ∧
          (∑ e, w e*|(∫ r, |F r e|^p ∂Measure.pi (fun _ : Fin (n.choose 2) => (μ:Measure ℝ)))-b|) ≤ ε := by
      intro w hw0 hws
      obtain ⟨F,hFm,hFV,hFb,hFe⟩ := stable_gradient_weighted (μ:Measure ℝ) p c hp hp2 hc hμ
        (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ w hδ hw0 hws
        (by simpa using hn) (pairIndex_incident n hn) (pairIndex_connected n)
        g (fun a => ⟨fun i => y i a,rfl⟩) hg T hT
      have hHn : (4*Real.log (Fintype.card (Fin n):ℝ)) = H := by simp [H]
      rw [hHn] at hFb hFe
      refine ⟨F,hFm,hFV,?_,?_⟩
      · have he : H*T = K := by dsimp [T,K]; ring
        simpa only [he] using hFb
      · have he : C0*H^(2-p) ≤ ε := by
          have ht : 0 ≤ H^(2-p) := Real.rpow_nonneg hH.le _
          dsimp [ε]; nlinarith
        exact hFe.trans he
    have hprob : (2*Fintype.card (PairIndex n):ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1 :=
      sampling_probability_estimate (K^p) ε (Real.rpow_pos_of_pos hK _) hε1 n _ hn
        Fintype.card_pos (pairIndex_card_le_square n)
    obtain ⟨z,hz⟩ := weighted_gradient_samples
      (Measure.pi (fun _ : Fin (n.choose 2) => (μ:Measure ℝ))) B p K b ε hp0 hK.le hε hw d hd hprob
    obtain ⟨s,hs,hse⟩ := sampled_labels_embedding p D b ε hp0 (by linarith) hb hDb hd δ hδ z hz
    refine ⟨fun i a => z a i,s,hs,?_⟩
    exact all_pairs_of_edge_bounds p D s hp0 x (fun i a => z a i) hse
  have hdim : dimension.{u} p n D ≤ d := Nat.sInf_le hgood
  have hnumer := sampling_dimension_estimate p (2-p) A hp0 (by linarith) hA.le n hn
  exact (show (dimension.{u} p n D:ℝ) ≤ d by exact_mod_cast hdim).trans hnumer

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set
open scoped BigOperators Topology Matrix ENNReal NNReal

namespace SubpolynomialLp

lemma symmetric_power_near (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1/2 →
      ((1+u)^q+(1-u)^q)/2 ≤ 1+C*u^2 := by
  let f : ℝ → ℝ := fun u => ((1+u)^q+(1-u)^q)/2
  have hf : ContDiffOn ℝ 2 f (Icc 0 (1/2)) := by
    apply ContDiffOn.div_const
    apply ContDiffOn.add
    · exact (contDiffOn_const.add contDiffOn_id).rpow_const_of_ne
        (fun x hx => ne_of_gt (by linarith [hx.1] : 0 < 1+x))
    · exact (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
        (fun x hx => ne_of_gt (by linarith [hx.2] : 0 < 1-x))
  obtain ⟨C,hC⟩ := exists_taylor_mean_remainder_bound (n := 1) (by norm_num : (0:ℝ) ≤ 1/2) hf
  have hd : HasDerivAt f 0 0 := by
    have h₁ := ((hasDerivAt_const (0:ℝ) (1:ℝ)).add (hasDerivAt_id (0:ℝ))).rpow_const
      (p := q) (Or.inl (by norm_num : (1:ℝ)+0 ≠ 0))
    have h₂ := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ))).rpow_const
      (p := q) (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0))
    simpa [f] using (h₁.add h₂).div_const 2
  have ht (u : ℝ) : taylorWithinEval f 1 (Icc 0 (1/2)) 0 u = 1 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_one, hd.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1/2) 0 (by constructor <;> norm_num))]
    simp [f]
  refine ⟨max C 0, le_max_right _ _, fun u hu hu' => ?_⟩
  have hh := hC u ⟨hu,hu'⟩
  rw [ht, sub_zero, Real.norm_eq_abs] at hh
  have hc := mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg u)
  have hl := le_abs_self (f u-1)
  dsimp [f] at hl hh
  linarith

lemma symmetric_power_unit_upper (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      (|1+u|^q+|1-u|^q)/2 ≤ 1+(1+ε)*u^q+C*u^2 := by
  obtain ⟨C,hC,hnear⟩ := symmetric_power_near q
  let δ := (1+ε)^(1/q)-1
  have hδ : 0 < δ := by
    have hh := Real.one_lt_rpow (by linarith : (1:ℝ) < 1+ε) (by positivity : 0 < 1/q)
    dsimp [δ]; linarith
  have hδq : (1+δ)^q = 1+ε := by
    dsimp [δ]
    rw [show 1+((1+ε)^(1/q)-1) = (1+ε)^(1/q) by ring, ← Real.rpow_mul (by linarith : 0 ≤ 1+ε),
      one_div_mul_cancel hq.ne', Real.rpow_one]
  let R := max 2 δ⁻¹
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let K := max C (4*(1+R)^q)
  have hK : 0 ≤ K := hC.trans (le_max_left _ _)
  refine ⟨K,hK,fun u hu => ?_⟩
  by_cases hsmall : u ≤ 1/2
  · rw [abs_of_nonneg (by linarith : 0 ≤ 1+u), abs_of_nonneg (by linarith : 0 ≤ 1-u)]
    have hh := hnear u hu hsmall
    have hk := mul_le_mul_of_nonneg_right (le_max_left C (4*(1+R)^q)) (sq_nonneg u)
    have hn : 0 ≤ (1+ε)*u^q := by positivity
    dsimp [K] at *
    linarith
  by_cases hlarge : R ≤ u
  · have hu0 : 0 < u := hR.trans_le hlarge
    have hdu : 1 ≤ δ*u := by
      have hi : δ⁻¹ ≤ u := (le_max_right _ _).trans hlarge
      have hh := mul_le_mul_of_nonneg_left hi hδ.le
      rwa [mul_inv_cancel₀ hδ.ne'] at hh
    have ha : |1+u| ≤ (1+δ)*u := by rw [abs_of_nonneg (by linarith)]; nlinarith
    have hb : |1-u| ≤ (1+δ)*u := by
      exact (abs_sub _ _).trans (by simp only [abs_one, abs_of_nonneg hu]; nlinarith)
    have hp₁ := Real.rpow_le_rpow (abs_nonneg _) ha hq.le
    have hp₂ := Real.rpow_le_rpow (abs_nonneg _) hb hq.le
    rw [Real.mul_rpow (by linarith : 0 ≤ 1+δ) hu, hδq] at hp₁ hp₂
    nlinarith [mul_nonneg hK (sq_nonneg u)]
  · have hur : u ≤ R := le_of_not_ge hlarge
    have ha : |1+u| ≤ 1+R := by rw [abs_of_nonneg (by linarith)]; linarith
    have hb : |1-u| ≤ 1+R := (abs_sub _ _).trans (by simpa only [abs_one, abs_of_nonneg hu] using add_le_add_right hur 1)
    have hp₁ := Real.rpow_le_rpow (abs_nonneg _) ha hq.le
    have hp₂ := Real.rpow_le_rpow (abs_nonneg _) hb hq.le
    have hu2 : 1/4 ≤ u^2 := by nlinarith
    have hpow : 0 ≤ (1+R)^q := Real.rpow_nonneg (by linarith) _
    have hk : 4*(1+R)^q ≤ K := le_max_right _ _
    have hh := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 4*(1+R)^q)
    have hh' := mul_le_mul_of_nonneg_right hk (sq_nonneg u)
    have hn : 0 ≤ (1+ε)*u^q := by positivity
    nlinarith

lemma sq_rpow_half_abs (x q : ℝ) : (x^2)^(q/2) = |x|^q := by
  rw [← sq_abs x, ← Real.rpow_natCast_mul (abs_nonneg x)]
  congr 1
  ring

lemma symmetric_power_lower (q : ℝ) (hq : 2 ≤ q) (a b : ℝ) :
    |a|^q+|b|^q ≤ (|a+b|^q+|a-b|^q)/2 := by
  have hconv := (convexOn_rpow (by linarith : 1 ≤ q/2)).2
    (show (a+b)^2 ∈ Ici (0:ℝ) from sq_nonneg (a+b)) (show (a-b)^2 ∈ Ici (0:ℝ) from sq_nonneg (a-b))
    (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul, sq_rpow_half_abs] at hconv
  have halg : (1/2:ℝ)*(a+b)^2+1/2*(a-b)^2 = a^2+b^2 := by ring
  rw [halg] at hconv
  have hlow := Real.add_rpow_le_rpow_add (sq_nonneg a) (sq_nonneg b) (by linarith : 1 ≤ q/2)
  rw [sq_rpow_half_abs, sq_rpow_half_abs] at hlow
  linarith

lemma symmetric_power_abs (q a b : ℝ) :
    |a+b|^q+|a-b|^q = (|a|+|b|)^q+|(|a|-|b|)|^q := by
  rcases le_total 0 a with ha|ha <;> rcases le_total 0 b with hb|hb
  · simp only [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb]
    have h₁ : a-b = a+-b := by ring
    have h₂ : a- -b = a+b := by ring
    rw [h₂, h₁, abs_of_nonneg (by linarith : 0 ≤ a+-b), add_comm]
  · rw [abs_of_nonpos ha, abs_of_nonneg hb]
    have h₁ : a-b = -(-a+b) := by ring
    have h₂ : -a-b = -(a+b) := by ring
    rw [h₁, h₂, abs_neg, abs_neg, abs_of_nonneg (by linarith : 0 ≤ -a+b), add_comm]
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (add_nonpos ha hb)]
    have h₁ : -(a+b) = -a+-b := by ring
    have h₂ : -a- -b = -(a-b) := by ring
    rw [h₁, h₂, abs_neg]

lemma symmetric_power_upper (q ε : ℝ) (hq : 2 < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ,
      (|a+b|^q+|a-b|^q)/2 ≤ |a|^q+(1+ε)* |b|^q+C* |a|^(q-2)*b^2 := by
  obtain ⟨C,hC,hh⟩ := symmetric_power_unit_upper q ε (by linarith) hε
  refine ⟨C,hC,fun a b => ?_⟩
  by_cases ha : a=0
  · subst a
    simp only [zero_add, zero_sub, abs_neg, abs_zero, Real.zero_rpow (by linarith : q ≠ 0),
      Real.zero_rpow (by linarith : q-2 ≠ 0), mul_zero, zero_mul, add_zero]
    nlinarith [Real.rpow_nonneg (abs_nonneg b) q]
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have he := hh (|b|/|a|) (by positivity)
  have he' := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ha0.le q)
  rw [symmetric_power_abs]
  have hsum : |a|+|b| = |a| *(1+|b|/|a|) := by field_simp
  have hsub : |(|a|-|b|)| = |a| * |(1-|b|/|a|)| := by
    calc
      _ = |(|a| *(1-|b|/|a|))| := by congr 1; field_simp
      _ = _ := by rw [abs_mul, abs_of_pos ha0]
  have hpow : |a|^q*(|b|/|a|)^q = |b|^q := by
    rw [← Real.mul_rpow ha0.le (by positivity), mul_div_cancel₀ _ ha0.ne']
  have hq2 : |a|^q*(|b|/|a|)^2 = |a|^(q-2)*b^2 := by
    rw [div_pow, sq_abs, Real.rpow_sub ha0, Real.rpow_two]
    ring
  rw [hsum, hsub, Real.mul_rpow ha0.le (by positivity), Real.mul_rpow ha0.le (abs_nonneg _)]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1+|b|/|a|)] at he'
  have halg : |a|^q*(1+(1+ε)*(|b|/|a|)^q+C*(|b|/|a|)^2) =
      |a|^q+(1+ε)* |b|^q+C* |a|^(q-2)*b^2 := by
    calc
      _ = |a|^q+(1+ε)*(|a|^q*(|b|/|a|)^q)+C*(|a|^q*(|b|/|a|)^2) := by ring
      _ = _ := by rw [hpow,hq2]; ring
  rw [halg] at he'
  linarith


lemma bounded_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A B : ℝ) (hμ : ∀ᵐ x ∂μ, |x| ≤ A) (hν : ∀ᵐ x ∂ν, |x| ≤ B) :
    ∀ᵐ x ∂(μ ∗ ν), |x| ≤ A+B := by
  rw [Measure.conv, ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
  apply (Measure.ae_prod_iff_ae_ae (p := fun x : ℝ × ℝ => |x.1+x.2| ≤ A+B)
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  exact hμ.mono (fun x hx => hν.mono (fun y hy =>
    (abs_add_le x y).trans (add_le_add hx hy)))

lemma bounded_abs_moment_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B q : ℝ) (hB : ∀ᵐ x ∂μ, |x| ≤ B) (hq : 0 ≤ q) :
    Integrable (fun x => |x|^q) μ := by
  apply (integrable_const (B^q)).mono' (by fun_prop)
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) hx hq

lemma bounded_abs_shift_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B q a : ℝ) (hB : ∀ᵐ x ∂μ, |x| ≤ B) (hq : 0 ≤ q) :
    Integrable (fun x => |a+x|^q) μ := by
  apply (integrable_const ((|a|+B)^q)).mono' (by fun_prop)
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) ((abs_add_le _ _).trans (add_le_add_right hx _)) hq

lemma symmetric_integral (μ : Measure ℝ) (hs : μ.map (fun x => -x) = μ)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μ) :
    (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ := by
  have hh := integral_map (μ := μ) (φ := fun x : ℝ => -x) (by fun_prop)
    (f := f) (by rwa [hs])
  simpa only [hs] using hh.symm

lemma bounded_moment_interpolation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B q : ℝ) (hq : 2 < q) (hB : ∀ᵐ x ∂μ, |x| ≤ B) :
    (∫ x, |x|^(q-2) ∂μ) ≤ (∫ x, |x|^q ∂μ)^((q-2)/q) := by
  have hq0 : 0 < q := by linarith
  have hr : 0 ≤ (q-2)/q := by positivity
  have hr1 : (q-2)/q ≤ 1 := (div_le_one hq0).mpr (by linarith)
  have he (x : ℝ) : (|x|^q)^((q-2)/q) = |x|^(q-2) := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hi := bounded_abs_moment_integrable μ B (q-2) hB (by linarith)
  have hh := (Real.concaveOn_rpow hr hr1).le_map_integral
    (Real.continuous_rpow_const hr).continuousOn isClosed_Ici
    (ae_of_all μ (fun x => Real.rpow_nonneg (abs_nonneg x) q))
    (bounded_abs_moment_integrable μ B q hB hq0.le)
    (show Integrable ((fun x : ℝ => x^((q-2)/q)) ∘ (fun x : ℝ => |x|^q)) μ by
      simpa only [Function.comp_def, he] using hi)
  simpa only [he] using hh

lemma symmetric_conv_moment (q ε C : ℝ) (hq : 2 < q) (hC : 0 ≤ C)
    (hscalar : ∀ a b : ℝ,
      (|a+b|^q+|a-b|^q)/2 ≤ |a|^q+(1+ε)* |b|^q+C* |a|^(q-2)*b^2)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A B : ℝ) (hμ : ∀ᵐ x ∂μ, |x| ≤ A) (hν : ∀ᵐ x ∂ν, |x| ≤ B)
    (hs : ν.map (fun x => -x) = ν) :
    (∫ x, |x|^q ∂μ)+(∫ x, |x|^q ∂ν) ≤ ∫ x, |x|^q ∂(μ ∗ ν) ∧
    (∫ x, |x|^q ∂(μ ∗ ν)) ≤ (∫ x, |x|^q ∂μ)+(1+ε)*(∫ x, |x|^q ∂ν)+
      C*(∫ x, |x|^q ∂μ)^((q-2)/q)*(∫ x, x^2 ∂ν) := by
  have hq0 : 0 ≤ q := by linarith
  have hiμ := bounded_abs_moment_integrable μ A q hμ hq0
  have hiν := bounded_abs_moment_integrable ν B q hν hq0
  have hiν2 : Integrable (fun x => x^2) ν := by
    simpa only [Real.rpow_two, sq_abs] using bounded_abs_moment_integrable ν B 2 hν (by norm_num)
  have hiμr := bounded_abs_moment_integrable μ A (q-2) hμ (by linarith)
  have hic := bounded_abs_moment_integrable (μ ∗ ν) (A+B) q (bounded_conv μ ν A B hμ hν) hq0
  have hisub (a : ℝ) : Integrable (fun x => |a-x|^q) ν := by
    apply (integrable_const ((|a|+B)^q)).mono' (by fun_prop)
    filter_upwards [hν] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) ((abs_sub _ _).trans (add_le_add_right hx _)) hq0
  have he (a : ℝ) : (∫ x, (|a+x|^q+|a-x|^q)/2 ∂ν) = ∫ x, |a+x|^q ∂ν := by
    rw [integral_div, integral_add (bounded_abs_shift_integrable ν B q a hν hq0) (hisub a)]
    have hs' := symmetric_integral ν hs (fun x => |a+x|^q) (by fun_prop)
    simp only [← sub_eq_add_neg] at hs'
    rw [hs']; ring
  have hl (a : ℝ) : |a|^q+(∫ x, |x|^q ∂ν) ≤ ∫ x, |a+x|^q ∂ν := by
    rw [← he]
    have hh := integral_mono ((integrable_const (|a|^q)).add hiν)
      (((bounded_abs_shift_integrable ν B q a hν hq0).add (hisub a)).div_const 2)
      (fun b => symmetric_power_lower q hq.le a b)
    simpa only [Pi.add_apply, integral_add (integrable_const _) hiν, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  have hu (a : ℝ) : (∫ x, |a+x|^q ∂ν) ≤ |a|^q+(1+ε)*(∫ x, |x|^q ∂ν)+
      C* |a|^(q-2)*(∫ x, x^2 ∂ν) := by
    rw [← he]
    have hh := integral_mono
      (((bounded_abs_shift_integrable ν B q a hν hq0).add (hisub a)).div_const 2)
      (((integrable_const (|a|^q)).add (hiν.const_mul (1+ε))).add (hiν2.const_mul (C* |a|^(q-2))))
      (hscalar a)
    simp only [Pi.add_apply] at hh
    have hi12 : Integrable (fun x => |a|^q+(1+ε)* |x|^q) ν :=
      (integrable_const (|a|^q)).add (hiν.const_mul (1+ε))
    rw [integral_add hi12 (hiν2.const_mul (C* |a|^(q-2))),
      integral_add (integrable_const (|a|^q)) (hiν.const_mul (1+ε)),
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    exact hh
  rw [integral_conv hic]
  have hif := (integrable_conv_iff (by fun_prop)).mp hic
  have houter : Integrable (fun a => ∫ b, |a+b|^q ∂ν) μ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hif.2
  constructor
  · have hh := integral_mono (hiμ.add (integrable_const _)) houter hl
    simpa only [Pi.add_apply, integral_add hiμ (integrable_const _), integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  · have hh := integral_mono houter
      ((hiμ.add (integrable_const _)).add ((hiμr.const_mul C).mul_const _)) hu
    simp only [Pi.add_apply] at hh
    have hi12 : Integrable (fun x => |x|^q+(1+ε)*(∫ x, |x|^q ∂ν)) μ :=
      hiμ.add (integrable_const _)
    have hi3 : Integrable (fun x => C* |x|^(q-2)*(∫ x, x^2 ∂ν)) μ :=
      (hiμr.const_mul C).mul_const _
    rw [integral_add hi12 hi3,
      integral_add hiμ (integrable_const _)] at hh
    simp only [integral_mul_const, integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    have hi := bounded_moment_interpolation μ A q hq hμ
    have hn : 0 ≤ (∫ x, x^2 ∂ν) := integral_nonneg (fun x => sq_nonneg x)
    exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hC) hn) _)

lemma sublinear_absorption (r δ a b x : ℝ) (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : x ≤ a+b*x^r) :
    x ≤ (1+δ)*a+(b*(1+δ)/δ)^(1/(1-r)) := by
  by_cases hs : x ≤ (1+δ)*a
  · exact hs.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
  have hx0 : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ (1+δ)*a) (lt_of_not_ge hs)
  have hxb : x ≤ b*((1+δ)/δ)*x^r := by
    have hsmall : a < x/(1+δ) := (lt_div_iff₀ (by positivity : 0 < 1+δ)).mpr (by nlinarith)
    have hh : x*δ ≤ b*x^r*(1+δ) := by
      have hm := (mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 1+δ))
      nlinarith
    apply (le_div_iff₀ hδ).mpr at hh
    calc x ≤ b*x^r*(1+δ)/δ := hh
         _ = _ := by ring
  have hpower : x^(1-r) ≤ b*(1+δ)/δ := by
    have hp0 : 0 < x^r := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_sub hx0, Real.rpow_one]
    apply (div_le_iff₀ hp0).mpr
    simpa only [mul_div_assoc] using hxb
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx _) hpower (by positivity : 0 ≤ 1/(1-r))
  rw [← Real.rpow_mul hx, mul_one_div_cancel (by linarith : 1-r ≠ 0), Real.rpow_one] at hh
  exact hh.trans (le_add_of_nonneg_left (by positivity))

lemma near_additive_recurrence (r δ C m a : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (M : ℕ → ℝ) (hzero : M 0 = 0) (hstep : ∀ k,
      M k+m ≤ M (k+1) ∧ M (k+1) ≤ M k+(1+δ)*m+C*a*(M k)^r) (N : ℕ) :
    (N:ℝ)*m ≤ M N ∧ M N ≤ (1+δ)^2*(N:ℝ)*m+
      (C*(1+δ)/δ)^(1/(1-r))*((N:ℝ)*a)^(1/(1-r)) := by
  have hmono : Monotone M := monotone_nat_of_le_succ (fun k =>
    (le_add_of_nonneg_right hm).trans (hstep k).1)
  have hnonneg (k : ℕ) : 0 ≤ M k := by simpa only [hzero] using hmono (Nat.zero_le k)
  have hl (k : ℕ) : (k:ℝ)*m ≤ M k := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have hh := (hstep k).1
      push_cast
      nlinarith
  have hu : ∀ k, k ≤ N → M k ≤ (k:ℝ)*((1+δ)*m+C*a*(M N)^r) := by
    intro k hk
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have hkn : k ≤ N := by omega
      have hrp := Real.rpow_le_rpow (hnonneg k) (hmono hkn) hr0
      have hh := (hstep k).2
      have hmul := mul_le_mul_of_nonneg_left hrp (mul_nonneg hC ha)
      have hi := ih hkn
      push_cast
      nlinarith
  have hineq : M N ≤ ((1+δ)*(N:ℝ)*m)+(C*((N:ℝ)*a))*(M N)^r := by
    have hh := hu N le_rfl
    nlinarith
  have habs := sublinear_absorption r δ ((1+δ)*(N:ℝ)*m) (C*((N:ℝ)*a)) (M N)
    hr0 hr1 hδ (by positivity) (by positivity) (hnonneg N) hineq
  have he : C*((N:ℝ)*a)*(1+δ)/δ = (C*(1+δ)/δ)*((N:ℝ)*a) := by ring
  rw [he, Real.mul_rpow (by positivity : 0 ≤ C*(1+δ)/δ) (by positivity)] at habs
  refine ⟨hl N, ?_⟩
  convert habs using 1; ring

lemma convolutionPower_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |x| ≤ B) (n : ℕ) :
    ∀ᵐ x ∂convolutionPower μ n, |x| ≤ (n:ℝ)*B := by
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    have h := bounded_conv (convolutionPower μ n) μ ((n:ℝ)*B) B ih hB
    simpa only [convolutionPower, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

lemma convolutionPower_near_moment (q ε : ℝ) (hq : 2 < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (B : ℝ), (∀ᵐ x ∂μ, |x| ≤ B) → μ.map (fun x => -x) = μ → ∀ n : ℕ,
      (n:ℝ)*(∫ x, |x|^q ∂μ) ≤ ∫ x, |x|^q ∂convolutionPower μ n ∧
      (∫ x, |x|^q ∂convolutionPower μ n) ≤
        (1+ε)^2*(n:ℝ)*(∫ x, |x|^q ∂μ)+C*((n:ℝ)*(∫ x, x^2 ∂μ))^(q/2) := by
  obtain ⟨C,hC,hscalar⟩ := symmetric_power_upper q ε hq hε
  have hr0 : 0 ≤ (q-2)/q := by positivity
  have hr1 : (q-2)/q < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have he : 1/(1-(q-2)/q) = q/2 := by field_simp; ring
  refine ⟨(C*(1+ε)/ε)^(q/2), by positivity, ?_⟩
  intro μ _ B hB hs n
  let M : ℕ → ℝ := fun k => ∫ x, |x|^q ∂convolutionPower μ k
  have hz : M 0 = 0 := by simp [M, convolutionPower, Real.zero_rpow (by linarith : q ≠ 0)]
  have hstep (k : ℕ) : M k+(∫ x, |x|^q ∂μ) ≤ M (k+1) ∧
      M (k+1) ≤ M k+(1+ε)*(∫ x, |x|^q ∂μ)+C*(∫ x, x^2 ∂μ)*(M k)^((q-2)/q) := by
    have h := symmetric_conv_moment q ε C hq hC hscalar (convolutionPower μ k) μ
      ((k:ℝ)*B) B (convolutionPower_bounded μ B hB k) hB hs
    simpa only [M, convolutionPower, mul_right_comm C] using h
  have h := near_additive_recurrence ((q-2)/q) ε C (∫ x, |x|^q ∂μ)
    (∫ x, x^2 ∂μ) hr0 hr1 hε hC
    (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    (integral_nonneg (fun x => sq_nonneg x)) M hz hstep n
  simpa only [he, M] using h

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set
open scoped BigOperators Topology Matrix ENNReal NNReal

namespace SubpolynomialLp

lemma power_difference_epsilon (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
      abs (|a+b|^p-|a|^p) ≤ ε*|a|^p+C*|b|^p := by
  have hc : ContinuousAt (fun t : ℝ => |1+t|^p) 0 := by
    exact (continuousAt_const.add continuousAt_id).abs.rpow_const (Or.inr hp.le)
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp hc ε hε
  let C : ℝ := 1+(1+δ⁻¹)^p+(δ⁻¹)^p
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun a b => ?_⟩
  have ha0 : 0 ≤ |a|^p := Real.rpow_nonneg (abs_nonneg a) p
  have hb0 : 0 ≤ |b|^p := Real.rpow_nonneg (abs_nonneg b) p
  by_cases ha : a = 0
  · subst a
    simp only [zero_add, abs_zero, Real.zero_rpow hp.ne', sub_zero, mul_zero, zero_add,
      abs_of_nonneg hb0]
    have hC1 : 1 ≤ C := by
      have h₁ : 0 ≤ (1+δ⁻¹)^p := by positivity
      have h₂ : 0 ≤ (δ⁻¹)^p := by positivity
      dsimp [C]; linarith
    nlinarith
  have haa : 0 < |a| := abs_pos.mpr ha
  by_cases hb : |b| < δ*|a|
  · have hr : dist (b/a) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_div]
      exact (div_lt_iff₀ haa).mpr (by nlinarith)
    have hn := (hnear hr).le
    simp only [Real.dist_eq, add_zero, abs_one, Real.one_rpow] at hn
    have he : |a+b|^p = |a|^p*|1+b/a|^p := by
      rw [← Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← abs_mul]
      congr 2
      field_simp
    rw [he, show |a|^p*|1+b/a|^p-|a|^p = |a|^p*(|1+b/a|^p-1) by ring,
      abs_mul, abs_of_nonneg ha0]
    exact (mul_le_mul_of_nonneg_left hn ha0).trans (by nlinarith)
  · have hab : |a| ≤ δ⁻¹*|b| := by
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hδ).mpr
      nlinarith [le_of_not_gt hb]
    have hadd : |a+b| ≤ (1+δ⁻¹)*|b| := by
      have hh := abs_add_le a b
      nlinarith
    have haP := Real.rpow_le_rpow (abs_nonneg _) hab hp.le
    have hbP := Real.rpow_le_rpow (abs_nonneg _) hadd hp.le
    rw [Real.mul_rpow (by positivity) (abs_nonneg _)] at haP hbP
    have h := abs_sub (|a+b|^p) (|a|^p)
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_of_nonneg ha0] at h
    dsimp [C]
    nlinarith

lemma rpow_le_constant_exp (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x^p ≤ C*Real.exp x := by
  obtain ⟨m,hm⟩ := exists_nat_ge p
  let C : ℝ := (m.factorial:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun x hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · have hpow : x^p ≤ 1 := by simpa only [Real.one_rpow] using Real.rpow_le_rpow hx hx1 hp
    have hex : 1 ≤ Real.exp x := Real.one_le_exp hx
    dsimp [C]
    have hf : 0 ≤ (m.factorial:ℝ) := by positivity
    nlinarith [Real.exp_pos x]
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hm
    rw [Real.rpow_natCast] at hpow
    have hex := Real.pow_div_factorial_le_exp x hx m
    have hf : 0 < (m.factorial:ℝ) := by positivity
    have hmexp := (div_le_iff₀ hf).mp hex
    dsimp [C]
    have hex0 := Real.exp_pos x
    nlinarith

lemma symmetric_exp_quadratic (x : ℝ) (hx : |x| ≤ 1) :
    (Real.exp x+Real.exp (-x))/2 ≤ 1+x^2 := by
  have h₁ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  have h₂ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := -x) (by simpa only [abs_neg] using hx))).2
  nlinarith

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set
open scoped BigOperators Topology Matrix ENNReal NNReal

namespace SubpolynomialLp

lemma powerIntensity_scaling (p c : ℝ) (hp : 0 < p) (hc : 0 < c) (f : ℝ → ℝ) :
    (∫ r, f (c*r) ∂powerIntensity p) = c^p * ∫ r, f r ∂powerIntensity p := by
  rw [powerIntensity_integral p hp, powerIntensity_integral p hp]
  have he : (fun r : ℝ => (p*r^(-p-1)) • f (c*r)) =ᵐ[volume.restrict (Ioi 0)]
      fun r => c^(p+1)*((p*(c*r)^(-p-1)) • f (c*r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [smul_eq_mul, Real.mul_rpow hc.le (le_of_lt hr)]
    rw [show c^(p+1)*(p*(c^(-p-1)*r^(-p-1))*f (c*r)) =
      (c^(p+1)*c^(-p-1))*(p*r^(-p-1)*f (c*r)) by ring,
      ← Real.rpow_add hc, show p+1+(-p-1) = 0 by ring, Real.rpow_zero, one_mul]
  rw [integral_congr_ae he, integral_const_mul,
    integral_comp_mul_left_Ioi (fun r => (p*r^(-p-1)) • f r) 0 hc,
    mul_zero, smul_eq_mul, ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 2
  ring

lemma powerIntensity_even_scaling (p c : ℝ) (hp : 0 < p) (f : ℝ → ℝ)
    (hf : ∀ x, f (-x) = f x) (hf0 : f 0 = 0) :
    (∫ r, f (c*r) ∂powerIntensity p) = |c|^p * ∫ r, f r ∂powerIntensity p := by
  rcases lt_trichotomy c 0 with hc|hc|hc
  · have he (r : ℝ) : f (c*r) = f ((-c)*r) := by rw [neg_mul, hf]
    simp_rw [he]
    rw [powerIntensity_scaling p (-c) hp (neg_pos.mpr hc) f, abs_of_neg hc]
  · subst c
    simp [hf0, Real.zero_rpow hp.ne']
  · rw [powerIntensity_scaling p c hp hc f, abs_of_pos hc]

def pareto (p : ℝ) : Measure ℝ := (powerIntensity p).restrict (Ioi 1)

lemma pareto_probability (p : ℝ) (hp : 0 < p) : IsProbabilityMeasure (pareto p) := by
  constructor
  simp only [pareto, Measure.restrict_apply_univ, powerIntensity_tail p 1 hp zero_lt_one, Real.one_rpow, ENNReal.ofReal_one]

lemma powerIntensity_supported_positive (p : ℝ) : ∀ᵐ r ∂powerIntensity p, 0 < r := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

lemma pareto_integral_eq_full (p c : ℝ) (hc : |c| ≤ 1) (f : ℝ → ℝ)
    (hf : ∀ x, |x| ≤ 1 → f x = 0) :
    (∫ r, f (c*r) ∂pareto p) = ∫ r, f (c*r) ∂powerIntensity p := by
  rw [pareto, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [powerIntensity_supported_positive p] with r hr
  by_cases h : r ∈ Ioi (1:ℝ)
  · simp only [indicator_of_mem h]
  · rw [indicator_of_notMem h]
    exact (hf (c*r) (by
      have hr1 : r ≤ 1 := le_of_not_gt h
      rw [abs_mul, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_right hc hr.le).trans (by linarith))).symm

lemma pareto_even_scaling (p c : ℝ) (hp : 0 < p) (hc : |c| ≤ 1) (f : ℝ → ℝ)
    (hf : ∀ x, f (-x) = f x) (hzero : ∀ x, |x| ≤ 1 → f x = 0) :
    (∫ r, f (c*r) ∂pareto p) = |c|^p * ∫ r, f r ∂pareto p := by
  rw [pareto_integral_eq_full p c hc f hzero,
    powerIntensity_even_scaling p c hp f hf (hzero 0 (by norm_num))]
  have h := pareto_integral_eq_full p 1 (by norm_num) f hzero
  simp only [one_mul] at h
  rw [h]

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal

namespace SubpolynomialLp

lemma geometric_tail_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m N : ℕ) :
    (∑ k ∈ Ico m N, q^k) ≤ q^m/(1-q) := by
  rw [sum_Ico_eq_sum_range]
  simp only [pow_add, ← mul_sum]
  have h := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum
    (range (N-m)) (fun k _ => pow_nonneg hq0 k)
  rw [tsum_geometric_of_lt_one hq0 hq1] at h
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h (pow_nonneg hq0 m)

lemma two_sum_bound (N : ℕ) : (∑ k ∈ range N, (2:ℝ)^k) ≤ 2^N := by
  have h := geom_sum_mul (2:ℝ) N
  norm_num at h
  linarith

lemma dyadic_cauchy (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (N m : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Ico m N, a k)^2 ≤
      (∑ k ∈ range N, (q^k)⁻¹*(a k)^2) * (q^m/(1-q)) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (Ico m N)
    (f := fun k => (q^k)⁻¹*(a k)^2) (g := fun k => q^k) (r := a)
    (fun k _ => by positivity) (fun k _ => by positivity)
    (fun k _ => by rw [mul_right_comm, inv_mul_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul])
  have he : (∑ k ∈ Ico m N, (q^k)⁻¹*(a k)^2) ≤
      ∑ k ∈ range N, (q^k)⁻¹*(a k)^2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact mem_range.mpr (mem_Ico.mp hk).2
    · intro k _ _
      positivity
  exact h.trans (mul_le_mul he (geometric_tail_bound q hq0.le hq1 m N)
    (sum_nonneg (fun k _ => pow_nonneg hq0.le k)) (sum_nonneg (fun k _ => by positivity)))

lemma dyadic_interpolation (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (A : ℝ) (a : ℕ → ℝ), 0 < A →
      (∀ k, 0 ≤ a k) → (∀ k < N, a k ≤ A*2^k) →
      (∑ k ∈ range N, a k)^p ≤ C*A^(p-2)*
        ∑ k ∈ range N, (((2:ℝ)^(2-p))^k)⁻¹ * (a k)^2 := by
  let q : ℝ := (2:ℝ)^(2-p)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let C : ℝ := 4*8^(p-2)/(1-q)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N A a hA ha haB
  let S : ℝ := ∑ k ∈ range N, a k
  let E : ℝ := ∑ k ∈ range N, (q^k)⁻¹*(a k)^2
  change S^p ≤ C*A^(p-2)*E
  have hS : 0 ≤ S := sum_nonneg (fun k _ => ha k)
  have hE : 0 ≤ E := sum_nonneg (fun k _ => by positivity)
  have hSp : S^p = S^2*S^(p-2) := by
    rw [← Real.rpow_two, ← Real.rpow_add' hS (by linarith : 2+(p-2) ≠ 0)]
    congr 1
    ring
  have hglobal : S^2 ≤ E/(1-q) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero, div_eq_mul_inv, one_mul] using
      dyadic_cauchy q hq0 hq1 N 0 a
  have hbound : S ≤ A*2^N := by
    calc
      S ≤ ∑ k ∈ range N, A*2^k := sum_le_sum (fun k hk => haB k (mem_range.mp hk))
      _ = A*∑ k ∈ range N, (2:ℝ)^k := (mul_sum _ _ _).symm
      _ ≤ A*2^N := mul_le_mul_of_nonneg_left (two_sum_bound N) hA.le
  have hnorm : (8*A)^(p-2) = 8^(p-2)*A^(p-2) := Real.mul_rpow (by norm_num) hA.le
  by_cases hs : S ≤ 4*A
  · have hsmall : S^(p-2) ≤ (8*A)^(p-2) := Real.rpow_le_rpow hS (by linarith) (by linarith)
    calc
      S^p = S^2*S^(p-2) := hSp
      _ ≤ (E/(1-q)) * ((8*A)^(p-2)) := mul_le_mul hglobal hsmall (by positivity) (by positivity)
      _ ≤ C*A^(p-2)*E := by
        have hn : 0 ≤ (E/(1-q))*((8*A)^(p-2)) := by positivity
        calc
          _ ≤ 4*((E/(1-q))*((8*A)^(p-2))) := by linarith
          _ = _ := by rw [hnorm]; dsimp [C]; ring
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity : 0 < 4*A) (le_of_not_ge hs)
  obtain ⟨m,hmlo,hmhi⟩ := exists_nat_pow_near
    (show (1:ℝ) ≤ S/(4*A) by apply (le_div_iff₀ (by positivity)).mpr; linarith)
    (by norm_num : (1:ℝ) < 2)
  have hmS : A*2^m ≤ S/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*A)).mp hmlo
    nlinarith
  have hmN : m ≤ N := by
    by_contra h
    have hNm : N ≤ m := by omega
    have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hNm
    have hmul := mul_le_mul_of_nonneg_left hpow hA.le
    linarith
  have hlow : (∑ k ∈ range m, a k) ≤ S/4 := by
    calc
      _ ≤ ∑ k ∈ range m, A*2^k := sum_le_sum (fun k hk => haB k (lt_of_lt_of_le (mem_range.mp hk) hmN))
      _ = A*∑ k ∈ range m, (2:ℝ)^k := (mul_sum _ _ _).symm
      _ ≤ A*2^m := mul_le_mul_of_nonneg_left (two_sum_bound m) hA.le
      _ ≤ S/4 := hmS
  have hsplit : S = (∑ k ∈ range m, a k)+(∑ k ∈ Ico m N, a k) :=
    (sum_range_add_sum_Ico a hmN).symm
  have htail0 : 0 ≤ ∑ k ∈ Ico m N, a k := sum_nonneg (fun k _ => ha k)
  have hhalf : S ≤ 2*∑ k ∈ Ico m N, a k := by linarith
  have htail := dyadic_cauchy q hq0 hq1 N m a
  have hsq : S^2 ≤ 4*E*(q^m/(1-q)) := by
    have hh := sq_le_sq₀ hS (by positivity) |>.mpr hhalf
    nlinarith
  have hbase : S/(8*A) ≤ 2^m := by
    have h := (div_lt_iff₀ (by positivity : 0 < 4*A)).mp hmhi
    rw [pow_succ] at h
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hpow : S^(p-2) ≤ (8*A)^(p-2)*(2^m)^(p-2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow hS _ (by linarith)
    have h := (div_le_iff₀ (by positivity : 0 < 8*A)).mp hbase
    nlinarith
  have hcancel : q^m * (2^m : ℝ)^(p-2) = 1 := by
    dsimp [q]
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show (2-p)*(m:ℝ)+(m:ℝ)*(p-2) = 0 by ring, Real.rpow_zero]
  calc
    S^p = S^2*S^(p-2) := hSp
    _ ≤ (4*E*(q^m/(1-q)))*((8*A)^(p-2)*(2^m)^(p-2)) :=
      mul_le_mul hsq hpow (by positivity) (by positivity)
    _ = C*A^(p-2)*E := by
      rw [hnorm]
      calc
        _ = (4*8^(p-2)/(1-q))*A^(p-2)*E*(q^m*(2^m : ℝ)^(p-2)) := by ring
        _ = _ := by rw [hcancel, mul_one]

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal

namespace SubpolynomialLp

def tailPart (a x : ℝ) : ℝ := if a < |x| then x else 0

def cutPart (a x : ℝ) : ℝ := if |x| ≤ a then x else 0

def bandPart (a b x : ℝ) : ℝ := if a < |x| ∧ |x| ≤ b then x else 0

def dyadicRamp (ℓ : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range ℓ, bandPart ((2:ℝ)^k) (2^(k+ℓ)) x

@[fun_prop] lemma tailPart_measurable (a : ℝ) : Measurable (tailPart a) := by
  exact measurable_id.piecewise (measurableSet_lt measurable_const measurable_abs) measurable_const

@[fun_prop] lemma cutPart_measurable (a : ℝ) : Measurable (cutPart a) := by
  exact measurable_id.piecewise (measurableSet_le measurable_abs measurable_const) measurable_const

@[fun_prop] lemma bandPart_measurable (a b : ℝ) : Measurable (bandPart a b) := by
  exact measurable_id.piecewise ((measurableSet_lt measurable_const measurable_abs).inter
    (measurableSet_le measurable_abs measurable_const)) measurable_const

@[fun_prop] lemma dyadicRamp_measurable (ℓ : ℕ) : Measurable (dyadicRamp ℓ) := by
  exact Finset.measurable_sum _ (fun _ _ => bandPart_measurable _ _)

lemma tailPart_add_cutPart (a x : ℝ) : tailPart a x + cutPart a x = x := by
  unfold tailPart cutPart
  by_cases h : a < |x| <;> simp [h, le_of_not_gt, not_le.mpr]

lemma bandPart_eq_cutPart (a b x : ℝ) (hab : a ≤ b) :
    bandPart a b x = cutPart b x - cutPart a x := by
  unfold bandPart cutPart
  by_cases ha : a < |x| <;> by_cases hb : |x| ≤ b <;> simp [ha,hb,not_le.mpr,le_of_not_gt]
  exfalso; linarith


lemma abs_cutPart_le (a x : ℝ) (ha : 0 ≤ a) : |cutPart a x| ≤ a := by
  unfold cutPart
  split_ifs with h <;> simp_all

lemma bandPart_neg (a b x : ℝ) : bandPart a b (-x) = -bandPart a b x := by
  simp only [bandPart,abs_neg]
  split_ifs <;> simp

lemma dyadicRamp_neg (ℓ : ℕ) (x : ℝ) : dyadicRamp ℓ (-x) = -dyadicRamp ℓ x := by
  simp only [dyadicRamp,bandPart_neg,Finset.sum_neg_distrib]

lemma dyadicRamp_zero_small (ℓ : ℕ) (x : ℝ) (hx : |x| ≤ 1) : dyadicRamp ℓ x = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have h : ¬ (2:ℝ)^k < |x| := not_lt.mpr (hx.trans (one_le_pow₀ (by norm_num)))
  simp [bandPart,h]

lemma abs_bandPart_le (a b x : ℝ) (hb : 0 ≤ b) : |bandPart a b x| ≤ b := by
  unfold bandPart
  split_ifs with h
  · exact h.2
  · simpa using hb

lemma abs_bandPart_le_tail (a b x : ℝ) : |bandPart a b x| ≤ |tailPart a x| := by
  unfold bandPart tailPart
  split_ifs <;> simp_all

lemma abs_dyadicRamp_le (ℓ : ℕ) (x : ℝ) : |dyadicRamp ℓ x| ≤ (2:ℝ)^(2*ℓ) := by
  calc
    |dyadicRamp ℓ x| ≤ ∑ k ∈ Finset.range ℓ, |bandPart ((2:ℝ)^k) (2^(k+ℓ)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range ℓ, (2:ℝ)^(k+ℓ) :=
      Finset.sum_le_sum (fun k _ => abs_bandPart_le _ _ _ (by positivity))
    _ = (∑ k ∈ Finset.range ℓ, (2:ℝ)^k)*2^ℓ := by simp only [pow_add,Finset.sum_mul]
    _ ≤ (2:ℝ)^ℓ*2^ℓ := mul_le_mul_of_nonneg_right (two_sum_bound ℓ) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega


lemma dyadicRamp_plateau (m : ℕ) (x : ℝ)
    (hx : (2:ℝ)^(2*m) < x) (hx' : x ≤ (2:ℝ)^(3*m)) :
    (m:ℝ)*x ≤ dyadicRamp (2*m) x := by
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) < 2^(2*m)).le.trans hx.le
  have hb (k : ℕ) (hk : k ∈ Finset.Ico m (2*m)) :
      bandPart ((2:ℝ)^k) (2^(k+2*m)) x = x := by
    have hk' := Finset.mem_Ico.mp hk
    apply ite_eq_left
    rw [abs_of_nonneg hx0]
    exact ⟨lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) (by omega)) hx,
      hx'.trans (pow_le_pow_right₀ (by norm_num) (by omega))⟩
  calc
    (m:ℝ)*x = ∑ k ∈ Finset.Ico m (2*m), bandPart ((2:ℝ)^k) (2^(k+2*m)) x := by
      rw [Finset.sum_congr rfl hb]
      simp [show 2*m-m=m by omega]
    _ ≤ dyadicRamp (2*m) x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
      · intro k _ _; unfold bandPart; split_ifs <;> positivity

lemma pareto_integrable_moment (p q : ℝ) (hp : 0 < p) (hqp : q < p) :
    Integrable (fun r : ℝ => r^q) (pareto p) := by
  rw [pareto,powerIntensity,restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun r : ℝ => ENNReal.ofReal (p*r^(-p-1))) by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  have he : (fun r : ℝ => (ENNReal.ofReal (p*r^(-p-1))).toReal • r^q) =ᵐ[volume.restrict (Ioi 1)]
      fun r => p*r^(q-p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    rw [ENNReal.toReal_ofReal (by positivity),smul_eq_mul,mul_assoc,← Real.rpow_add hr0]
    congr 2
    ring
  apply Integrable.congr _ he.symm
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : q-p-1 < -1) zero_lt_one).const_mul p

lemma pareto_tailPart_moment (p q a : ℝ) (hp : 0 < p) (hq : 0 < q) (hqp : q < p) (ha : 1 ≤ a) :
    (∫ r, |tailPart a r|^q ∂pareto p) = p/(p-q)*a^(q-p) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have he : (fun r => |tailPart a r|^q) =ᵐ[pareto p] (Ioi a).indicator (fun r : ℝ => r^q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := powerIntensity p)] with r hr
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    by_cases h : a < r
    · simp [tailPart,abs_of_pos hr0,h]
    · simp [tailPart,abs_of_pos hr0,h,Real.zero_rpow (by linarith : q ≠ 0)]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioi,pareto,
    Measure.restrict_restrict measurableSet_Ioi,Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi ha)]
  exact powerIntensity_large_moment p q a hp hqp ha0


lemma tailPart_abs_le (a x : ℝ) : |tailPart a x| ≤ |x| := by
  unfold tailPart
  split_ifs <;> simp

lemma tailPart_neg (a x : ℝ) : tailPart a (-x) = -tailPart a x := by
  simp only [tailPart,abs_neg]
  split_ifs <;> simp

lemma pareto_tail_sq_integrable (p a c : ℝ) (hp : 2 < p) (hc : |c| ≤ 1) :
    Integrable (fun r => (tailPart a (c*r))^2) (pareto p) := by
  have hi : Integrable (fun r : ℝ => r^2) (pareto p) := by
    simpa only [Real.rpow_two] using pareto_integrable_moment p 2 (by linarith) hp
  apply hi.mono' (show Measurable (fun r => (tailPart a (c*r))^2) by fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := powerIntensity p)] with r hr
  have hr0 : 0 ≤ r := (lt_trans zero_lt_one hr).le
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh : |tailPart a (c*r)| ≤ r := (tailPart_abs_le _ _).trans (by
    rw [abs_mul,abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_right hc hr0).trans_eq (one_mul _))
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr0).mpr hh

lemma pareto_tail_sq_moment (p a c : ℝ) (hp : 2 < p) (ha : 1 ≤ a) (hc : |c| ≤ 1) :
    (∫ r, (tailPart a (c*r))^2 ∂pareto p) = |c|^p*(p/(p-2)*a^(2-p)) := by
  have hf : ∀ x : ℝ, |x| ≤ 1 → |tailPart a x|^(2:ℝ) = 0 := by
    intro x hx
    simp [tailPart,not_lt.mpr (hx.trans ha)]
  have hs := pareto_even_scaling p c (by linarith) hc (fun x => |tailPart a x|^(2:ℝ))
    (fun x => by rw [tailPart_neg,abs_neg]) hf
  rw [pareto_tailPart_moment p 2 a (by linarith) (by norm_num) hp ha] at hs
  simpa only [Real.rpow_two,sq_abs] using hs

lemma dyadicRamp_moment_integrable (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q) (ℓ : ℕ) :
    Integrable (fun r => |dyadicRamp ℓ r|^q) (pareto p) := by
  have := pareto_probability p hp
  apply Integrable.of_bound (by fun_prop (disch := positivity)) (((2:ℝ)^(2*ℓ))^q)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_dyadicRamp_le ℓ x) hq

lemma pareto_dyadicRamp_energy_lower (p : ℝ) (hp : 0 < p) (m : ℕ) (hm : 1 ≤ m) :
    p*Real.log 2*(m:ℝ)^(p+1) ≤ ∫ r, |dyadicRamp (2*m) r|^p ∂pareto p := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have ha : (1:ℝ) ≤ 2^(2*m) := one_le_pow₀ (by norm_num)
  have hab : (2:ℝ)^(2*m) ≤ 2^(3*m) := pow_le_pow_right₀ (by norm_num) (by omega)
  let s : Set ℝ := Ioc ((2:ℝ)^(2*m)) (2^(3*m))
  have hsi : IntegrableOn (fun r : ℝ => r^p) s (pareto p) := by
    have := pareto_probability p hp
    apply Integrable.of_bound (by fun_prop (disch := positivity)) (((2:ℝ)^(3*m))^p)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := ha.trans hr.1.le |>.trans' (by norm_num : (0:ℝ) ≤ 1)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr0 _)]
    exact Real.rpow_le_rpow hr0 hr.2 hp.le
  have him := dyadicRamp_moment_integrable p p hp hp.le (2*m)
  have hl : (∫ r in s, (m:ℝ)^p*r^p ∂pareto p) ≤
      ∫ r in s, |dyadicRamp (2*m) r|^p ∂pareto p := by
    apply integral_mono_ae (hsi.const_mul _) him.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := (by positivity : (0:ℝ) < 2^(2*m)).le.trans hr.1.le
    rw [← Real.mul_rpow hm0.le hr0]
    exact Real.rpow_le_rpow (by positivity)
      ((dyadicRamp_plateau m r hr.1 hr.2).trans (le_abs_self _)) hp.le
  have hrest : (∫ r in s, |dyadicRamp (2*m) r|^p ∂pareto p) ≤
      ∫ r, |dyadicRamp (2*m) r|^p ∂pareto p :=
    setIntegral_le_integral him (ae_of_all _ (fun r => Real.rpow_nonneg (abs_nonneg _) _))
  have he : (∫ r in s, (m:ℝ)^p*r^p ∂pareto p) = p*Real.log 2*(m:ℝ)^(p+1) := by
    rw [integral_const_mul,pareto,Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr (show s ⊆ Ioi (1:ℝ) from fun r hr => ha.trans_lt hr.1)]
    rw [powerIntensity_critical_moment p _ _ hp (by positivity) hab,
      Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow,
      Real.rpow_add hm0,Real.rpow_one]
    push_cast
    ring
  exact he ▸ hl.trans hrest

lemma dyadic_variance_weight (p : ℝ) (k : ℕ) :
    (((2:ℝ)^((2-p)/2))^k)⁻¹*((2:ℝ)^k)^(2-p) = ((2:ℝ)^((2-p)/2))^k := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

lemma pareto_dyadicRamp_variance (p : ℝ) (hp : 2 < p) (ℓ : ℕ) :
    (∫ r, (dyadicRamp ℓ r)^2 ∂pareto p) ≤
      (p/(p-2))/(1-(2:ℝ)^((2-p)/2))^2 := by
  let s : ℝ := (2:ℝ)^((2-p)/2)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hi (k : ℕ) : Integrable (fun r => (tailPart ((2:ℝ)^k) r)^2) (pareto p) := by
    simpa only [one_mul] using pareto_tail_sq_integrable p ((2:ℝ)^k) 1 hp (by norm_num)
  have hJ : Integrable (fun r => (∑ k ∈ Finset.range ℓ, (s^k)⁻¹*(tailPart ((2:ℝ)^k) r)^2)/(1-s))
      (pareto p) := (integrable_finsetSum _ (fun k _ => (hi k).const_mul _)).div_const _
  have hM : Integrable (fun r => (dyadicRamp ℓ r)^2) (pareto p) := by
    simpa only [Real.rpow_two,sq_abs] using dyadicRamp_moment_integrable p 2 (by linarith) (by norm_num) ℓ
  have hpt (r : ℝ) : (dyadicRamp ℓ r)^2 ≤
      (∑ k ∈ Finset.range ℓ, (s^k)⁻¹*(tailPart ((2:ℝ)^k) r)^2)/(1-s) := by
    have ht : |dyadicRamp ℓ r| ≤ ∑ k ∈ Finset.range ℓ, |tailPart ((2:ℝ)^k) r| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun k _ => abs_bandPart_le_tail _ _ _))
    have hc := dyadic_cauchy s hs0 hs1 ℓ 0 (fun k => |tailPart ((2:ℝ)^k) r|)
    simp only [Nat.Ico_zero_eq_range,pow_zero,sq_abs,div_eq_mul_inv,one_mul] at hc
    have hh := (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun k _ => abs_nonneg _))).mpr ht
    rw [sq_abs] at hh
    simpa only [div_eq_mul_inv] using hh.trans hc
  have hints (k : ℕ) : (∫ r, (tailPart ((2:ℝ)^k) r)^2 ∂pareto p) =
      p/(p-2)*((2:ℝ)^k)^(2-p) := by
    simpa only [one_mul,abs_one,Real.one_rpow] using
      pareto_tail_sq_moment p ((2:ℝ)^k) 1 hp (one_le_pow₀ (by norm_num)) (by norm_num)
  calc
    _ ≤ ∫ r, (∑ k ∈ Finset.range ℓ, (s^k)⁻¹*(tailPart ((2:ℝ)^k) r)^2)/(1-s) ∂pareto p :=
      integral_mono hM hJ hpt
    _ = (p/(p-2))*(∑ k ∈ Finset.range ℓ, s^k)/(1-s) := by
      rw [integral_div,integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
      simp only [integral_const_mul,hints]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_left_comm,dyadic_variance_weight]
    _ ≤ (p/(p-2))*(1/(1-s))/(1-s) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.Ico_zero_eq_range,pow_zero] using geometric_tail_bound s hs0.le hs1 0 ℓ
    _ = _ := by
      change (p/(p-2))*(1/(1-s))/(1-s) = (p/(p-2))/(1-s)^2
      field_simp

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal

namespace SubpolynomialLp

variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]

def averageLaw (μ : ι → Measure Ω) : Measure Ω :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, μ i

instance averageLaw_probability [Nonempty ι] (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (averageLaw μ) := by
  constructor
  simp [averageLaw,Measure.smul_apply,Measure.finsetSum_apply,ENNReal.inv_mul_cancel,
    Fintype.card_ne_zero]

lemma averageLaw_integrable (μ : ι → Measure Ω) (f : Ω → ℝ)
    (hf : ∀ i, Integrable f (μ i)) : Integrable f (averageLaw μ) := by
  by_cases h : IsEmpty ι
  · let _ := h
    simp [averageLaw]
  · have : Nonempty ι := not_isEmpty_iff.mp h
    exact (integrable_finsetSum_measure.mpr (fun i _ => hf i)).smul_measure (by simp)

lemma averageLaw_integral (μ : ι → Measure Ω) (f : Ω → ℝ)
    (hf : ∀ i, Integrable f (μ i)) :
    (∫ x, f x ∂averageLaw μ) = (∑ i, ∫ x, f x ∂μ i)/(Fintype.card ι : ℝ) := by
  rw [averageLaw,integral_smul_measure,integral_finsetSum_measure (fun i _ => hf i)]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma averageLaw_ae [Nonempty ι] (μ : ι → Measure Ω) (P : Ω → Prop)
    (hP : ∀ i, ∀ᵐ x ∂μ i, P x) : ∀ᵐ x ∂averageLaw μ, P x := by
  exact Measure.ae_smul_measure (ae_finsetSum_measure_iff.mpr (fun i _ => hP i)) _

section Symmetric
variable {E : Type uE} [AddCommGroup E] [MeasurableSpace E] [MeasurableNeg E]

def symmetricLaw (μ : Measure E) : Measure E := (1/2 : ℝ≥0∞) • μ +
  (1/2 : ℝ≥0∞) • μ.map (fun x => -x)

instance symmetricLaw_probability (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetricLaw μ) := by
  have : IsProbabilityMeasure (μ.map (fun x=>-x)) := Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  constructor
  norm_num [symmetricLaw,Measure.add_apply,Measure.smul_apply,ENNReal.inv_two_add_inv_two]

lemma symmetricLaw_symmetry (μ : Measure E) :
    (symmetricLaw μ).map (fun x=>-x) = symmetricLaw μ := by
  rw [symmetricLaw,Measure.map_add _ _ measurable_neg,
    Measure.map_smul,
    Measure.map_smul,
    Measure.map_map measurable_neg measurable_neg]
  simp only [Function.comp_def,neg_neg,Measure.map_id']
  exact add_comm _ _

lemma symmetricLaw_ae (μ : Measure E) (P : E → Prop)
    (hP : ∀ᵐ x ∂μ, P x) (hN : ∀ x, P x → P (-x)) :
    ∀ᵐ x ∂symmetricLaw μ, P x := by
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure hP _
  · apply Measure.ae_smul_measure
    exact (measurableEmbedding_neg.ae_map_iff).mpr (hP.mono hN)


lemma symmetricLaw_even_integral (μ : Measure E) (f : E → ℝ) (hf : Measurable f)
    (hi : Integrable f μ) (hn : ∀ x, f (-x) = f x) :
    (∫ x, f x ∂symmetricLaw μ) = ∫ x, f x ∂μ := by
  have hi' : Integrable f (μ.map (fun x=>-x)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable measurable_neg.aemeasurable]
    simpa only [Function.comp_def,hn] using hi
  rw [symmetricLaw,integral_add_measure (hi.smul_measure (by norm_num))
    (hi'.smul_measure (by norm_num)),integral_smul_measure,integral_smul_measure,
    integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
  simp only [hn,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  ring
end Symmetric

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal

namespace SubpolynomialLp

variable {I : Type uI} {E : Type uE} [Fintype I] [Nonempty I] [Fintype E]

def paretoVectorLaw (p : ℝ) (g : I → E → ℝ) : Measure (E → ℝ) :=
  averageLaw (fun i => (pareto p).map (fun r e => g i e*r))

lemma paretoVectorLaw_probability (p : ℝ) (hp : 0 < p) (g : I → E → ℝ) :
    IsProbabilityMeasure (paretoVectorLaw p g) := by
  let :=  pareto_probability p hp
  have : ∀ i : I, IsProbabilityMeasure ((pareto p).map (fun r e => g i e*r)) :=
    fun _ => (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact averageLaw_probability _

omit [Nonempty I] [Fintype E] in
lemma normalized_coefficients_bounded (p : ℝ) (hp : 0 < p) (g : I → E → ℝ)
    (hg : ∀ e, ∑ i, |g i e|^p = 1) : ∀ i e, |g i e| ≤ 1 := by
  intro i e
  have hh : |g i e|^p ≤ 1 := by
    rw [← hg e]
    exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg (g j e)) p) (Finset.mem_univ i)
  by_contra hn
  have hpow : 1 < |g i e|^p := Real.one_lt_rpow (lt_of_not_ge hn) hp
  linarith

omit [Nonempty I] in
lemma paretoVectorLaw_integrable (p : ℝ) (g : I → E → ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (e : E)
    (hi : ∀ i, Integrable (fun r => f (g i e*r)) (pareto p)) :
    Integrable (fun z => f (z e)) (paretoVectorLaw p g) := by
  apply averageLaw_integrable
  intro i
  rw [integrable_map_measure (show Measurable (fun z : E → ℝ => f (z e)) from hf.comp (measurable_pi_apply e)).aestronglyMeasurable (by fun_prop)]
  exact hi i

omit [Nonempty I] in
lemma paretoVectorLaw_moment (p : ℝ) (hp : 0 < p) (g : I → E → ℝ)
    (hg : ∀ e, ∑ i, |g i e|^p = 1) (f : ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ x, f (-x)=f x) (hz : ∀ x, |x| ≤ 1 → f x=0) (e : E)
    (hi : ∀ i, Integrable (fun r => f (g i e*r)) (pareto p)) :
    (∫ z, f (z e) ∂paretoVectorLaw p g) = (∫ r, f r ∂pareto p)/(Fintype.card I : ℝ) := by
  have habs := normalized_coefficients_bounded p hp g hg
  rw [paretoVectorLaw,averageLaw_integral]
  · have he (i : I) : (∫ z, f (z e) ∂(pareto p).map (fun r e => g i e*r)) = |g i e|^p*(∫ r, f r ∂pareto p) := by
      rw [integral_map (by fun_prop) (show Measurable (fun z : E → ℝ => f (z e)) from hf.comp (measurable_pi_apply e)).aestronglyMeasurable]
      exact pareto_even_scaling p _ hp (habs i e) f hn hz
    simp_rw [he]
    rw [← Finset.sum_mul,hg e,one_mul]
  · intro i
    rw [integrable_map_measure (show Measurable (fun z : E → ℝ => f (z e)) from hf.comp (measurable_pi_apply e)).aestronglyMeasurable (by fun_prop)]
    exact hi i

omit [Nonempty I] in
lemma paretoVectorLaw_tail_integrable (p a : ℝ) (hp : 2 < p) (g : I → E → ℝ)
    (hg : ∀ e, ∑ i, |g i e|^p = 1) (e : E) :
    Integrable (fun z => (tailPart a (z e))^2) (paretoVectorLaw p g) := by
  apply paretoVectorLaw_integrable p g (fun x => (tailPart a x)^2) (by fun_prop) e
  intro i
  exact pareto_tail_sq_integrable p a (g i e) hp (normalized_coefficients_bounded p (by linarith) g hg i e)

omit [Nonempty I] in
lemma paretoVectorLaw_tail_moment (p a : ℝ) (hp : 2 < p) (ha : 1 ≤ a)
    (g : I → E → ℝ) (hg : ∀ e, ∑ i, |g i e|^p=1) (e : E) :
    (∫ z, (tailPart a (z e))^2 ∂paretoVectorLaw p g) =
      (p/(p-2)*a^(2-p))/(Fintype.card I : ℝ) := by
  have hx : ∀ x, |x| ≤ 1 → (tailPart a x)^2 = 0 := by
    intro x hx
    simp [tailPart,not_lt.mpr (hx.trans ha)]
  rw [paretoVectorLaw_moment p (by linarith) g hg _ (by fun_prop)
    (fun x => by rw [tailPart_neg,neg_sq]) hx e]
  · congr 1
    simpa only [one_mul,abs_one,Real.one_rpow] using pareto_tail_sq_moment p a 1 hp ha (by norm_num)
  · intro i
    exact pareto_tail_sq_integrable p a (g i e) hp (normalized_coefficients_bounded p (by linarith) g hg i e)

lemma paretoVectorLaw_ramp_integrable (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (g : I → E → ℝ) (ℓ : ℕ) (e : E) :
    Integrable (fun z => |dyadicRamp ℓ (z e)|^q) (paretoVectorLaw p g) := by
  let :=  paretoVectorLaw_probability p hp g
  apply Integrable.of_bound (show Measurable (fun z : E → ℝ => |dyadicRamp ℓ (z e)|^q) by fun_prop).aestronglyMeasurable
    (((2:ℝ)^(2*ℓ))^q)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_dyadicRamp_le ℓ (z e)) hq

omit [Nonempty I] in
lemma paretoVectorLaw_ramp_moment (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (g : I → E → ℝ) (hg : ∀ e, ∑ i, |g i e|^p=1) (ℓ : ℕ) (e : E) :
    (∫ z, |dyadicRamp ℓ (z e)|^q ∂paretoVectorLaw p g) =
      (∫ r, |dyadicRamp ℓ r|^q ∂pareto p)/(Fintype.card I : ℝ) := by
  apply paretoVectorLaw_moment p hp g hg (fun x => |dyadicRamp ℓ x|^q) (by fun_prop)
    (fun x => by rw [dyadicRamp_neg,abs_neg])
    (fun x hx => by rw [dyadicRamp_zero_small _ _ hx,abs_zero,Real.zero_rpow hq.ne']) e
  intro i
  let :=  pareto_probability p hp
  apply Integrable.of_bound (show Measurable (fun r : ℝ => |dyadicRamp ℓ (g i e*r)|^q) by fun_prop).aestronglyMeasurable
    (((2:ℝ)^(2*ℓ))^q)
  apply ae_of_all
  intro r
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_dyadicRamp_le ℓ _) hq.le

lemma paretoVectorLaw_range {V : Type uV} [Fintype V]
    (p : ℝ) (g : I → E → ℝ) (A : Matrix E V ℝ)
    (hg : ∀ i, ∃ x, A.mulVec x=g i) :
    ∀ᵐ z ∂paretoVectorLaw p g, ∃ x, A.mulVec x=z := by
  classical
  have hs : MeasurableSet {z : E → ℝ | ∃ x, A.mulVec x=z} :=
    (LinearMap.range (Matrix.toLin' A)).closed_of_finiteDimensional.measurableSet
  apply averageLaw_ae
  intro i
  apply (ae_map_iff (by fun_prop) hs).mpr
  apply ae_of_all
  intro r
  obtain ⟨x,hx⟩ := hg i
  refine ⟨r • x,?_⟩
  rw [Matrix.mulVec_smul,hx]
  ext e
  simp [smul_eq_mul,mul_comm]

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma controlled_retraction_integrals {Ω : Type uΩ} {E : Type uE} {V : Type uV} {J : Type uJ} [MeasurableSpace Ω]
    [Fintype E] [Fintype V] [Fintype J] [DecidableEq E] [DecidableEq V] [Nonempty E]
    (μ : Measure Ω) (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (f : J → E → Ω → ℝ) (hf : ∀ j e, MemLp (f j e) 2 μ)
    (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hbound : ∀ j e, (∫ x, (f j e x)^2 ∂μ) ≤ B j) :
    ∃ P ∈ retractions (normalizedGradient src dst δ),
      (∀ e, matrixRowNorm P e ≤ 4*Real.log (Fintype.card V : ℝ)) ∧
      (∀ j, (∑ e, lam e * (∫ x, (P.mulVec (fun a => f j a x) e)^2 ∂μ)) ≤ 4*B j) := by
  have hnorm (j : J) (e : E) : ‖(hf j e).toLp (f j e)‖^2 ≤ B j := by
    rw [L2_norm_sq]; exact hbound j e
  obtain ⟨P,hP,hr,hE⟩ := controlled_retraction_bounds src dst δ lam hδ hlam hls hcard hinc hconn
    (fun j e => (hf j e).toLp (f j e)) B hB hnorm
  refine ⟨P,hP,hr,fun j => ?_⟩
  simpa only [L2_hilbertMul_energy,Matrix.mulVec,dotProduct] using hE j

lemma retraction_fixes {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]
    (A : Matrix E V ℝ) (P : Matrix E E ℝ) (hP : P ∈ retractions A)
    (v : E → ℝ) (hv : ∃ x, A.mulVec x = v) : P.mulVec v = v := by
  obtain ⟨x,rfl⟩ := hv
  rw [Matrix.mulVec_mulVec,hP.1]

lemma retraction_range {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]
    (A : Matrix E V ℝ) (P : Matrix E E ℝ) (hP : P ∈ retractions A)
    (v : E → ℝ) : ∃ x, A.mulVec x = P.mulVec v := by
  obtain ⟨B,hB⟩ := hP.2
  exact ⟨B.mulVec v,by rw [Matrix.mulVec_mulVec,← hB]⟩

lemma matrix_mulVec_bound {E : Type uE} [Fintype E]
    (P : Matrix E E ℝ) (v : E → ℝ) (K : ℝ) (hK : ∀ e, |v e| ≤ K) (e : E) :
    |P.mulVec v e| ≤ matrixRowNorm P e * K := by
  calc
    _ ≤ ∑ f, |P e f*v f| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f, |P e f| *K := Finset.sum_le_sum (fun f _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK f) (abs_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

lemma matrix_memLp {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) (P : Matrix E E ℝ) (f : E → Ω → ℝ)
    (hf : ∀ e, MemLp (f e) 2 μ) (e : E) : MemLp (fun x => P.mulVec (fun a => f a x) e) 2 μ := by
  convert memLp_finsetSum' Finset.univ (fun a _ => (hf a).const_mul (P e a)) using 1
  ext x
  simp only [Matrix.mulVec,dotProduct,Finset.sum_apply]

lemma matrix_integral_sq_bound {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) (P : Matrix E E ℝ) (f : E → Ω → ℝ)
    (hf : ∀ e, MemLp (f e) 2 μ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ e, (∫ x, (f e x)^2 ∂μ) ≤ B) (e : E) :
    (∫ x, (P.mulVec (fun a => f a x) e)^2 ∂μ) ≤ (matrixRowNorm P e)^2*B := by
  have hnorm (a : E) : ‖(hf a).toLp (f a)‖ ≤ Real.sqrt B := by
    apply (Real.le_sqrt (norm_nonneg _) hB).mpr
    rw [L2_norm_sq]; exact hbound a
  have hsum : ‖hilbertMul P (fun a => (hf a).toLp (f a)) e‖ ≤ matrixRowNorm P e*Real.sqrt B := by
    calc
      _ ≤ ∑ a, ‖P e a • (hf a).toLp (f a)‖ := norm_sum_le _ _
      _ ≤ ∑ a, |P e a| *Real.sqrt B := Finset.sum_le_sum (fun a _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hnorm a) (abs_nonneg _))
      _ = _ := (Finset.sum_mul ..).symm
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (matrixRowNorm_nonneg P e) (Real.sqrt_nonneg B))).mpr hsum
  rw [L2_hilbertMul_energy,mul_pow,Real.sq_sqrt hB] at hh
  exact hh

lemma ramp_error_le_cut_errors {E : Type uE} [Fintype E]
    (P : Matrix E E ℝ) (v : E → ℝ) (ℓ : ℕ) (e : E) :
    |P.mulVec (fun a => dyadicRamp ℓ (v a)) e - dyadicRamp ℓ (v e)| ≤
      ∑ k ∈ Finset.range (2*ℓ),
        |P.mulVec (fun a => cutPart ((2:ℝ)^k) (v a)) e-cutPart ((2:ℝ)^k) (v e)| := by
  let d : ℕ → ℝ := fun k => P.mulVec (fun a => cutPart ((2:ℝ)^k) (v a)) e-cutPart ((2:ℝ)^k) (v e)
  have he : P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e) =
      ∑ k ∈ Finset.range ℓ, (d (k+ℓ)-d k) := by
    simp only [dyadicRamp,bandPart_eq_cutPart _ _ _ (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right _ _)),
      Matrix.mulVec,dotProduct,d]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range ℓ, |d (k+ℓ)-d k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range ℓ, (|d (k+ℓ)|+|d k|) := Finset.sum_le_sum (fun k _ => abs_sub _ _)
    _ = ∑ k ∈ Finset.range (2*ℓ), |d k| := by
      rw [Finset.sum_add_distrib,show 2*ℓ=ℓ+ℓ by omega,Finset.sum_range_add]
      simp only [Nat.add_comm]
      ring

lemma cut_error_eq_neg_tail_error {E : Type uE} [Fintype E]
    (P : Matrix E E ℝ) (v : E → ℝ) (hv : P.mulVec v=v) (a : ℝ) (e : E) :
    P.mulVec (fun f => cutPart a (v f)) e-cutPart a (v e) =
      -(P.mulVec (fun f => tailPart a (v f)) e-tailPart a (v e)) := by
  have ht : (fun f => tailPart a (v f))+(fun f => cutPart a (v f))=v := by
    ext f; exact tailPart_add_cutPart a (v f)
  have hh := congrFun (congrArg (P.mulVec) ht) e
  rw [Matrix.mulVec_add,hv] at hh
  have he := tailPart_add_cutPart a (v e)
  change P.mulVec (fun f => tailPart a (v f)) e+P.mulVec (fun f => cutPart a (v f)) e=v e at hh
  linarith

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma cut_error_bound {E : Type uE} [Fintype E] (P : Matrix E E ℝ) (H a : ℝ)
    (hH : 1 ≤ H) (ha : 0 ≤ a) (hr : ∀ e, matrixRowNorm P e ≤ H)
    (v : E → ℝ) (e : E) :
    |P.mulVec (fun f => cutPart a (v f)) e-cutPart a (v e)| ≤ 2*H*a := by
  have hm := matrix_mulVec_bound P (fun f => cutPart a (v f)) a (fun f => abs_cutPart_le a (v f) ha) e
  have ht := abs_sub (P.mulVec (fun f => cutPart a (v f)) e) (cutPart a (v e))
  have hc := abs_cutPart_le a (v e) ha
  have hh := mul_le_mul_of_nonneg_right (hr e) ha
  nlinarith

lemma ramp_error_bound {E : Type uE} [Fintype E] (P : Matrix E E ℝ) (H : ℝ)
    (hH : 1 ≤ H) (hr : ∀ e, matrixRowNorm P e ≤ H)
    (ℓ : ℕ) (v : E → ℝ) (e : E) :
    |P.mulVec (fun f => dyadicRamp ℓ (v f)) e-dyadicRamp ℓ (v e)| ≤ 2*H*2^(2*ℓ) := by
  have hm := matrix_mulVec_bound P (fun f => dyadicRamp ℓ (v f)) (2^(2*ℓ)) (fun f => abs_dyadicRamp_le ℓ (v f)) e
  have ht := abs_sub (P.mulVec (fun f => dyadicRamp ℓ (v f)) e) (dyadicRamp ℓ (v e))
  have hc := abs_dyadicRamp_le ℓ (v e)
  have hh := mul_le_mul_of_nonneg_right (hr e) (by positivity : (0:ℝ) ≤ 2^(2*ℓ))
  have hpow : (0:ℝ) ≤ 2^(2*ℓ) := by positivity
  have := mul_le_mul_of_nonneg_right hH hpow
  nlinarith

lemma ramp_projection_error (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) [Fintype E]
      (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
      (P : Matrix E E ℝ) (w : E → ℝ) (_hw : ∀ e, 0 ≤ w e) (_hws : ∑ e, w e=1)
      (H B : ℝ) (_hH : 1 ≤ H) (_hB : 0 ≤ B) (ℓ : ℕ),
      (∀ e, matrixRowNorm P e ≤ H) →
      (∀ᵐ v ∂μ, P.mulVec v=v) →
      (∀ k < 2*ℓ, ∀ e, Integrable (fun v => (tailPart ((2:ℝ)^k) (v e))^2) μ) →
      (∀ k < 2*ℓ, ∀ e, (∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ) ≤ B*((2:ℝ)^(2-p))^k) →
      (∀ k < 2*ℓ, (∑ e, w e*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ)) ≤
        4*B*((2:ℝ)^(2-p))^k) →
      (∑ e, w e*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ)) ≤
        C*H^(p-2)*(ℓ:ℝ)*B := by
  obtain ⟨C,hC,hdy⟩ := dyadic_interpolation p hp
  refine ⟨20*C*2^(p-2),by positivity,?_⟩
  intro E _ μ _ P w hw hws H B hH _hB ℓ hr hfix htailI htail hPE
  let q : ℝ := (2:ℝ)^(2-p)
  have hq : 0 < q := by dsimp [q]; positivity
  let d : ℕ → E → (E → ℝ) → ℝ := fun k e v =>
    P.mulVec (fun a => cutPart ((2:ℝ)^k) (v a)) e-cutPart ((2:ℝ)^k) (v e)
  let R : E → (E → ℝ) → ℝ := fun e v =>
    P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)
  have hdm (k : ℕ) (e : E) : Measurable (d k e) := by
    dsimp [d,Matrix.mulVec,dotProduct]; fun_prop
  have hdB (k : ℕ) (e : E) (v : E → ℝ) : |d k e v| ≤ 2*H*2^k :=
    cut_error_bound P H _ hH (by positivity) hr v e
  have hdI (k : ℕ) (e : E) : Integrable (fun v => (d k e v)^2) μ := by
    simpa only [Real.rpow_two,sq_abs] using bounded_power_integrable μ (d k e) (hdm k e) 2 (2*H*2^k)
      (by norm_num) (by positivity) (hdB k e)
  have hRm (e : E) : Measurable (R e) := by dsimp [R,Matrix.mulVec,dotProduct]; fun_prop
  have hRI (e : E) : Integrable (fun v => |R e v|^p) μ :=
    bounded_power_integrable μ _ (hRm e) p (2*H*2^(2*ℓ)) (by linarith) (by positivity)
      (fun v => ramp_error_bound P H hH hr ℓ v e)
  have hdE (k : ℕ) (hk : k < 2*ℓ) :
      (∑ e, w e*(∫ v, (d k e v)^2 ∂μ)) ≤ 10*B*q^k := by
    have htL (e : E) : MemLp (fun v : E → ℝ => tailPart ((2:ℝ)^k) (v e)) 2 μ :=
      (memLp_two_iff_integrable_sq (show Measurable (fun v : E → ℝ => tailPart ((2:ℝ)^k) (v e)) by fun_prop).aestronglyMeasurable).mpr (htailI k hk e)
    have hi (e : E) : Integrable (fun v => (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2) μ :=
      (matrix_memLp μ P _ htL e).integrable_sq
    have he (e : E) : (∫ v, (d k e v)^2 ∂μ) ≤
        2*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ)+
        2*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ) := by
      rw [← integral_const_mul,← integral_const_mul,← integral_add ((hi e).const_mul 2) ((htailI k hk e).const_mul 2)]
      apply integral_mono_ae (hdI k e) (((hi e).const_mul 2).add ((htailI k hk e).const_mul 2))
      filter_upwards [hfix] with v hv
      dsimp [d]
      rw [cut_error_eq_neg_tail_error P v hv,neg_sq]
      nlinarith [sq_nonneg (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e+tailPart ((2:ℝ)^k) (v e))]
    have hs : (∑ e, w e*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ)) ≤ B*q^k := by
      calc
        _ ≤ ∑ e, w e*(B*q^k) := Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (htail k hk e) (hw e))
        _ = _ := by rw [← Finset.sum_mul,hws,one_mul]
    calc
      _ ≤ ∑ e, w e*(2*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ)+
        2*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ)) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (he e) (hw e))
      _ = 2*(∑ e, w e*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ))+
          2*(∑ e, w e*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ)) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
      _ ≤ _ := by have hh := hPE k hk; change _ ≤ 4*B*q^k at hh; linarith
  have hpoint (e : E) (v : E → ℝ) : |R e v|^p ≤
      C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(d k e v)^2) := by
    have hh := hdy (2*ℓ) (2*H) (fun k => |d k e v|) (by positivity)
      (fun k => abs_nonneg _) (fun k _ => hdB k e v)
    have hb := Real.rpow_le_rpow (abs_nonneg _) (ramp_error_le_cut_errors P v ℓ e) (by linarith : 0 ≤ p)
    simpa only [sq_abs] using hb.trans hh
  have heI (e : E) : (∫ v, |R e v|^p ∂μ) ≤
      C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(∫ v, (d k e v)^2 ∂μ)) := by
    have hsI : Integrable (fun v => ∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(d k e v)^2) μ :=
      integrable_finsetSum _ (fun k _ => (hdI k e).const_mul _)
    calc
      _ ≤ ∫ v, C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(d k e v)^2) ∂μ :=
        integral_mono (hRI e) (hsI.const_mul _) (hpoint e)
      _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun k _ => (hdI k e).const_mul _)]
                  simp only [integral_const_mul]
  calc
    _ ≤ ∑ e, w e*(C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(∫ v, (d k e v)^2 ∂μ))) :=
      Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (heI e) (hw e))
    _ = C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(∑ e, w e*(∫ v, (d k e v)^2 ∂μ))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(10*B*q^k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hdE k (Finset.mem_range.mp hk)) (by positivity))
    _ = _ := by
      have he (k : ℕ) : (q^k)⁻¹*(10*B*q^k)=10*B := by field_simp
      simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ H)]
      ring

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

def aboveVariance (p : ℝ) : ℝ := (p/(p-2))/(1-(2:ℝ)^((2-p)/2))^2

lemma aboveVariance_pos (p : ℝ) (hp : 2 < p) : 0 < aboveVariance p := by
  have hs : (2:ℝ)^((2-p)/2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  dsimp [aboveVariance]
  positivity

lemma dyadic_tail_power (p : ℝ) (k : ℕ) : ((2:ℝ)^k)^(2-p) = ((2:ℝ)^(2-p))^k := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm]

lemma ramp_retraction (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) (V : Type uV) (I : Type uI) [Fintype E] [Fintype V] [Fintype I]
      [DecidableEq E] [DecidableEq V] [Nonempty E] [Nonempty I]
      (src dst : E → V) (δ w : E → ℝ) (_hδ : ∀ e, 0 < δ e)
      (_hw : ∀ e, 0 < w e) (_hws : ∑ e, w e=1)
      (_hcard : 2 ≤ Fintype.card V)
      (_hinc : ∀ i : V, ∃ e, src e=i ∨ dst e=i)
      (_hconn : ∀ i j : V, i ≠ j → ∃ e,
        (src e=i ∧ dst e=j) ∨ (src e=j ∧ dst e=i))
      (g : I → E → ℝ) (_hg : ∀ e, ∑ i, |g i e|^p=1)
      (_hgr : ∀ i, ∃ x, (normalizedGradient src dst δ).mulVec x=g i)
      (ℓ : ℕ),
      let μ := paretoVectorLaw p g
      let H := 4*Real.log (Fintype.card V : ℝ)
      let N := (Fintype.card I : ℝ)
      let u := fun v : E → ℝ => fun e => dyadicRamp ℓ (v e)
      ∃ P ∈ retractions (normalizedGradient src dst δ),
        (∀ e, matrixRowNorm P e ≤ H) ∧
        (∑ e, w e*(∫ v, |P.mulVec (u v) e-u v e|^p ∂μ)) ≤ C*H^(p-2)*(ℓ:ℝ)/N ∧
        (∑ e, w e*(∫ v, (P.mulVec (u v) e)^2 ∂μ)) ≤ 4*aboveVariance p/N ∧
        (∀ e, (∫ v, (P.mulVec (u v) e)^2 ∂μ) ≤ H^2*aboveVariance p/N) := by
  obtain ⟨C,hC,hError⟩ := ramp_projection_error p hp
  refine ⟨C*(p/(p-2)),by positivity,?_⟩
  intro E V I _ _ _ _ _ _ _ src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  dsimp only
  let μ := paretoVectorLaw p g
  let H := 4*Real.log (Fintype.card V : ℝ)
  let N := (Fintype.card I : ℝ)
  let u := fun v : E → ℝ => fun e => dyadicRamp ℓ (v e)
  let U := aboveVariance p
  let T := p/(p-2)
  let q : ℝ := (2:ℝ)^(2-p)
  have hU : 0 < U := aboveVariance_pos p hp
  have hT : 0 < T := by dsimp [T]; positivity
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hq : 0 < q := by dsimp [q]; positivity
  have hH : 1 ≤ H := by
    have ht := log_nat_lower (Fintype.card V) hcard
    dsimp [H]; linarith
  let := paretoVectorLaw_probability p (by linarith) g
  let f : Option (Fin (2*ℓ)) → E → (E → ℝ) → ℝ := fun j e v =>
    match j with
    | none => dyadicRamp ℓ (v e)
    | some k => tailPart ((2:ℝ)^k.val) (v e)
  let B : Option (Fin (2*ℓ)) → ℝ := fun j =>
    match j with
    | none => U/N
    | some k => (T/N)*q^k.val
  have hB (j : Option (Fin (2*ℓ))) : 0 < B j := by cases j <;> dsimp [B] <;> positivity
  have hf (j : Option (Fin (2*ℓ))) (e : E) : MemLp (f j e) 2 μ := by
    cases j with
    | none =>
      apply (memLp_two_iff_integrable_sq (show Measurable (f none e) by dsimp [f]; fun_prop).aestronglyMeasurable).mpr
      simpa only [f,Real.rpow_two,sq_abs] using paretoVectorLaw_ramp_integrable p 2 (by linarith) (by norm_num) g ℓ e
    | some k =>
      exact (memLp_two_iff_integrable_sq (show Measurable (f (some k) e) by dsimp [f]; fun_prop).aestronglyMeasurable).mpr
        (paretoVectorLaw_tail_integrable p ((2:ℝ)^k.val) hp g hg e)
  have hbound (j : Option (Fin (2*ℓ))) (e : E) : (∫ v, (f j e v)^2 ∂μ) ≤ B j := by
    cases j with
    | none =>
      have he := paretoVectorLaw_ramp_moment p 2 (by linarith) (by norm_num) g hg ℓ e
      simp only [Real.rpow_two,sq_abs] at he
      dsimp [f,B]
      rw [he]
      exact div_le_div_of_nonneg_right (pareto_dyadicRamp_variance p hp ℓ) hN.le
    | some k =>
      dsimp [f,B,μ,T,N,q]
      rw [paretoVectorLaw_tail_moment p _ hp (one_le_pow₀ (by norm_num)) g hg e,dyadic_tail_power]
      exact le_of_eq (by ring)
  obtain ⟨P,hP,hr,hPE⟩ := controlled_retraction_integrals μ src dst δ w hδ hw hws hcard hinc hconn f hf B hB hbound
  have hraw (k : ℕ) (e : E) : (∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ) = (T/N)*q^k := by
    rw [paretoVectorLaw_tail_moment p _ hp (one_le_pow₀ (by norm_num)) g hg e,dyadic_tail_power]
    dsimp [T,N,q]; ring
  refine ⟨P,hP,hr,?_,?_,?_⟩
  · have hfix : ∀ᵐ v ∂μ, P.mulVec v=v := by
      filter_upwards [paretoVectorLaw_range p g (normalizedGradient src dst δ) hgr] with v hv
      exact retraction_fixes _ P hP v hv
    have hh := hError E μ P w (fun e => (hw e).le) hws H (T/N) hH (by positivity) ℓ hr hfix
      (fun k _ e => paretoVectorLaw_tail_integrable p ((2:ℝ)^k) hp g hg e)
      (fun k _ e => (hraw k e).le)
      (fun k hk => by simpa only [f,B,q,mul_assoc] using hPE (some ⟨k,hk⟩))
    convert hh using 1
    dsimp [T,N,H]
    ring
  · simpa only [f,B,mul_div_assoc] using hPE none
  · intro e
    have hh := matrix_integral_sq_bound μ P (f none) (hf none) (U/N) (by positivity) (hbound none) e
    have hr0 := matrixRowNorm_nonneg P e
    have hr2 := (sq_le_sq₀ hr0 (by linarith : 0 ≤ H)).mpr (hr e)
    have hmul := mul_le_mul_of_nonneg_right hr2 (by positivity : 0 ≤ U/N)
    exact hh.trans (by simpa only [mul_div_assoc] using hmul)

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

variable {E : Type uE}

def coordinateLaw (μ : Measure (E → ℝ)) (e : E) : Measure ℝ := μ.map (fun v => v e)

instance coordinateLaw_probability (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (e : E) :
    IsProbabilityMeasure (coordinateLaw μ e) := by
  unfold coordinateLaw
  exact Measure.isProbabilityMeasure_map (measurable_pi_apply e).aemeasurable

lemma coordinateLaw_integral (μ : Measure (E → ℝ)) (e : E) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂coordinateLaw μ e) = ∫ v, f (v e) ∂μ :=
  integral_map (measurable_pi_apply e).aemeasurable hf.aestronglyMeasurable

lemma coordinateLaw_abs_moment (μ : Measure (E → ℝ)) (e : E) (p : ℝ) :
    (∫ x, |x|^p ∂coordinateLaw μ e) = ∫ v, |v e|^p ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_sq_moment (μ : Measure (E → ℝ)) (e : E) :
    (∫ x, x^2 ∂coordinateLaw μ e) = ∫ v, (v e)^2 ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_exp_moment (μ : Measure (E → ℝ)) (e : E) (s J : ℝ) :
    (∫ x, Real.exp (s*x/J) ∂coordinateLaw μ e) = ∫ v, Real.exp (s*v e/J) ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_integrable (μ : Measure (E → ℝ)) (e : E) (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable f (coordinateLaw μ e) ↔ Integrable (fun v => f (v e)) μ :=
  integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply e).aemeasurable

lemma coordinateLaw_ae (μ : Measure (E → ℝ)) (e : E) (P : ℝ → Prop)
    (hP : MeasurableSet {x | P x}) : (∀ᵐ x ∂coordinateLaw μ e, P x) ↔ ∀ᵐ v ∂μ, P (v e) :=
  ae_map_iff (measurable_pi_apply e).aemeasurable hP

lemma coordinateLaw_symmetric (μ : Measure (E → ℝ))
    (hs : μ.map (fun v => -v)=μ) (e : E) : (coordinateLaw μ e).map (fun x => -x)=coordinateLaw μ e := by
  rw [coordinateLaw,Measure.map_map (by fun_prop) (by fun_prop)]
  have hh := congrArg (fun ν : Measure (E → ℝ) => ν.map (fun v => v e)) hs
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh

lemma coordinateLaw_convolutionPower (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (e : E) (n : ℕ) :
    coordinateLaw (convolutionPower μ n) e = convolutionPower (coordinateLaw μ e) n := by
  let L : (E → ℝ) →+ ℝ := { toFun := fun v => v e, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact convolutionPower_map μ L (measurable_pi_apply e) n

lemma convolutionPower_submodule [Fintype E] (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (V : Submodule ℝ (E → ℝ)) (hμ : ∀ᵐ v ∂μ, v ∈ V) (n : ℕ) :
    ∀ᵐ v ∂convolutionPower μ n, v ∈ V := by
  have hV : MeasurableSet (V : Set (E → ℝ)) := V.closed_of_finiteDimensional.measurableSet
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    rw [convolutionPower,Measure.conv]
    apply (ae_map_iff (show AEMeasurable (fun x : (E → ℝ) × (E → ℝ) => x.1+x.2) _ by fun_prop)
      (show MeasurableSet {v : E → ℝ | v ∈ V} from hV)).mpr
    apply (Measure.ae_prod_iff_ae_ae (p := fun z : (E → ℝ) × (E → ℝ) => z.1+z.2 ∈ V)
      (hV.preimage (by fun_prop))).mpr
    exact ih.mono (fun x hx => hμ.mono (fun y hy => V.add_mem hx hy))

lemma bounded_coordinate_power_integrable (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (e : E) (p B : ℝ) (hp : 0 ≤ p) (hB : ∀ᵐ v ∂μ, |v e| ≤ B) :
    Integrable (fun v => |v e|^p) μ := by
  apply Integrable.of_bound (show Measurable (fun v : E → ℝ => |v e|^p) by fun_prop).aestronglyMeasurable (|B|^p)
  filter_upwards [hB] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (hv.trans (le_abs_self B)) hp

lemma bounded_symmetric_coordinate_exp (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (hs : μ.map (fun v => -v)=μ) (e : E) (J : ℝ) (hJ : 0 < J)
    (hB : ∀ᵐ v ∂μ, |v e| ≤ J) (s : ℝ) (hs1 : |s|=1) :
    Integrable (fun v => Real.exp (s*v e/J)) μ ∧
    (∫ v, Real.exp (s*v e/J) ∂μ) ≤ 1+(∫ v, (v e)^2 ∂μ)/J^2 := by
  let ν := coordinateLaw μ e
  have hν : ∀ᵐ x ∂ν, |x| ≤ J := (coordinateLaw_ae μ e _ (measurableSet_le (by fun_prop) measurable_const)).mpr hB
  have hi := bounded_exp_integrable ν J hν (s/J)
  have hn := bounded_exp_integrable ν J hν (-(s/J))
  have hsν := coordinateLaw_symmetric μ hs e
  have he := symmetric_integral ν hsν (fun x => Real.exp ((s/J)*x)) hi.aestronglyMeasurable
  have hsq : Integrable (fun x : ℝ => x^2) ν := by
    simpa only [Real.rpow_two,sq_abs] using bounded_abs_moment_integrable ν J 2 hν (by norm_num)
  have hineq : (∫ x, (Real.exp ((s/J)*x)+Real.exp (-((s/J)*x)))/2 ∂ν) ≤
      (∫ x, 1+x^2/J^2 ∂ν) := by
    apply integral_mono_ae ((hi.add (by simpa only [neg_mul] using hn)).div_const 2)
      ((integrable_const 1).add (hsq.div_const _))
    filter_upwards [hν] with x hx
    have hx1 : |(s/J)*x| ≤ 1 := by
      rw [abs_mul,abs_div,hs1,abs_of_pos hJ]
      simpa only [one_div,inv_mul_eq_div] using (div_le_one hJ).mpr hx
    have hh := symmetric_exp_quadratic ((s/J)*x) hx1
    have hs2 : s^2=1 := by nlinarith [sq_abs s,congrArg (fun t : ℝ => t^2) hs1]
    simpa only [Pi.add_apply,mul_pow,div_pow,hs2,one_div,inv_mul_eq_div] using hh
  have he' : (∫ x, Real.exp (-((s/J)*x)) ∂ν) = ∫ x, Real.exp ((s/J)*x) ∂ν := by
    simpa only [mul_neg] using he
  rw [integral_div,integral_add hi (by simpa only [neg_mul] using hn),he',
    integral_add (integrable_const 1) (hsq.div_const _),integral_const,probReal_univ,
    one_smul,integral_div] at hineq
  have hsimp : (fun x : ℝ => Real.exp ((s/J)*x)) = fun x => Real.exp (s*x/J) := by funext x; congr 1; ring
  rw [hsimp] at hi hineq
  refine ⟨(coordinateLaw_integrable μ e _ (by fun_prop)).mp hi,?_⟩
  rw [coordinateLaw_integral μ e _ (by fun_prop),coordinateLaw_integral μ e _ (by fun_prop)] at hineq
  linarith

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma integrated_power_perturbation {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p ε C b : ℝ)
    (hp : 0 < p) (hScalar : ∀ a t : ℝ, abs (|a+t|^p-|a|^p) ≤ ε*|a|^p+C*|t|^p)
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |X x| ≤ B ∧ |Y x| ≤ B)
    (hYb : (∫ x, |Y x|^p ∂μ)=b) :
    |(∫ x, |X x|^p ∂μ)-b| ≤ ε*b+C*(∫ x, |X x-Y x|^p ∂μ) := by
  have hXi := bounded_power_integrable μ X hX p B hp hB0 (fun x => (hB x).1)
  have hYi := bounded_power_integrable μ Y hY p B hp hB0 (fun x => (hB x).2)
  have hDi := bounded_power_integrable μ (fun x => X x-Y x) (hX.sub hY) p (2*B) hp
    (by positivity) (fun x => (abs_sub _ _).trans (by linarith [(hB x).1,(hB x).2]))
  calc
    _ = |∫ x, |X x|^p-|Y x|^p ∂μ| := by rw [integral_sub hXi hYi,hYb]
    _ ≤ ∫ x, abs (|X x|^p-|Y x|^p) ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ε*|Y x|^p+C*|X x-Y x|^p ∂μ := by
      apply integral_mono (hXi.sub hYi).abs ((hYi.const_mul ε).add (hDi.const_mul C))
      intro x
      simpa only [Pi.sub_apply,Pi.add_apply,add_sub_cancel_left,add_sub_cancel_right,add_sub_cancel] using hScalar (Y x) (X x-Y x)
    _ = _ := by rw [integral_add (hYi.const_mul ε) (hDi.const_mul C),integral_const_mul,integral_const_mul,hYb]

variable {E : Type uE} [Fintype E]

def projectedRampLaw (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) : Measure (E → ℝ) :=
  symmetricLaw (μ.map (fun v => P.mulVec (fun e => dyadicRamp ℓ (v e))))

instance projectedRampLaw_probability (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (P : Matrix E E ℝ) (ℓ : ℕ) : IsProbabilityMeasure (projectedRampLaw μ P ℓ) := by
  have : IsProbabilityMeasure (μ.map (fun v => P.mulVec (fun e => dyadicRamp ℓ (v e)))) :=
    Measure.isProbabilityMeasure_map
      (Measurable.aemeasurable (by unfold Matrix.mulVec dotProduct; fun_prop))
  unfold projectedRampLaw
  infer_instance

lemma projectedRampLaw_symmetry (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) :
    (projectedRampLaw μ P ℓ).map (fun v => -v)=projectedRampLaw μ P ℓ := symmetricLaw_symmetry _

lemma projectedRampLaw_bounded (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ)
    (H : ℝ) (hr : ∀ e, matrixRowNorm P e ≤ H) :
    ∀ᵐ z ∂projectedRampLaw μ P ℓ, ∀ e, |z e| ≤ H*2^(2*ℓ) := by
  apply ae_all_iff.mpr
  intro e
  apply symmetricLaw_ae
  · apply (ae_map_iff (show Measurable (fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))) by change Measurable (fun v : E → ℝ => fun e => ∑ a, P e a*dyadicRamp ℓ (v a)); fun_prop).aemeasurable
      (measurableSet_le (show Measurable (fun z : E → ℝ => |z e|) by fun_prop) measurable_const)).mpr
    apply ae_of_all
    intro v
    exact (matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e).trans
      (mul_le_mul_of_nonneg_right (hr e) (by positivity))
  · intro z hz
    simpa only [Pi.neg_apply,abs_neg] using hz

lemma projectedRampLaw_range {V : Type uV} [Fintype V]
    (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) (A : Matrix E V ℝ)
    (hP : P ∈ retractions A) :
    ∀ᵐ z ∂projectedRampLaw μ P ℓ, ∃ x, A.mulVec x=z := by
  classical
  have hm : MeasurableSet {z : E → ℝ | ∃ x, A.mulVec x=z} :=
    (LinearMap.range (Matrix.toLin' A)).closed_of_finiteDimensional.measurableSet
  apply symmetricLaw_ae
  · apply (ae_map_iff (show Measurable (fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))) by change Measurable (fun v : E → ℝ => fun e => ∑ a, P e a*dyadicRamp ℓ (v a)); fun_prop).aemeasurable hm).mpr
    exact ae_of_all _ (fun v => retraction_range A P hP _)
  · rintro z ⟨x,hx⟩
    exact ⟨-x,by rw [Matrix.mulVec_neg,hx]⟩

lemma projectedRampLaw_moment (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (P : Matrix E E ℝ) (ℓ : ℕ) (q : ℝ) (hq : 0 < q) (e : E) :
    (∫ z, |z e|^q ∂projectedRampLaw μ P ℓ) =
      ∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e|^q ∂μ := by
  let F := fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))
  have hF : Measurable F := by dsimp [F,Matrix.mulVec,dotProduct]; fun_prop
  have hi : Integrable (fun z : E → ℝ => |z e|^q) (μ.map F) := by
    rw [integrable_map_measure (show Measurable (fun z : E → ℝ => |z e|^q) by fun_prop).aestronglyMeasurable hF.aemeasurable]
    exact bounded_power_integrable μ (fun v => F v e) (by fun_prop) q
      (matrixRowNorm P e*2^(2*ℓ)) hq (by positivity [matrixRowNorm_nonneg P e])
      (fun v => matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e)
  rw [projectedRampLaw,symmetricLaw_even_integral _ _ (by fun_prop) hi
    (fun z => by simp only [Pi.neg_apply,abs_neg]),integral_map hF.aemeasurable (show Measurable (fun z : E → ℝ => |z e|^q) by fun_prop).aestronglyMeasurable]

lemma ramp_jump_law (p ε : ℝ) (hp : 2 < p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) (V : Type uV) (I : Type uI) [Fintype E] [Fintype V] [Fintype I]
      [DecidableEq E] [DecidableEq V] [Nonempty E] [Nonempty I]
      (src dst : E → V) (δ w : E → ℝ) (_hδ : ∀ e, 0 < δ e)
      (_hw : ∀ e, 0 < w e) (_hws : ∑ e, w e=1)
      (_hcard : 2 ≤ Fintype.card V)
      (_hinc : ∀ i : V, ∃ e, src e=i ∨ dst e=i)
      (_hconn : ∀ i j : V, i ≠ j → ∃ e,
        (src e=i ∧ dst e=j) ∨ (src e=j ∧ dst e=i))
      (g : I → E → ℝ) (_hg : ∀ e, ∑ i, |g i e|^p=1)
      (_hgr : ∀ i, ∃ x, (normalizedGradient src dst δ).mulVec x=g i)
      (ℓ : ℕ),
      let H := 4*Real.log (Fintype.card V : ℝ)
      let N := (Fintype.card I : ℝ)
      let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
      ∃ ν : Measure (E → ℝ), IsProbabilityMeasure ν ∧ ν.map (fun v => -v)=ν ∧
        (∀ᵐ z ∂ν, ∃ x, (normalizedGradient src dst δ).mulVec x=z) ∧
        (∀ᵐ z ∂ν, ∀ e, |z e| ≤ H*2^(2*ℓ)) ∧
        (∑ e, w e*|N*(∫ z, |z e|^p ∂ν)-b|) ≤ ε*b+C*H^(p-2)*(ℓ:ℝ) ∧
        (∑ e, w e*(N*(∫ z, (z e)^2 ∂ν))) ≤ 4*aboveVariance p ∧
        (∀ e, N*(∫ z, (z e)^2 ∂ν) ≤ H^2*aboveVariance p) := by
  obtain ⟨C₁,hC₁,hScalar⟩ := power_difference_epsilon p ε (by linarith) hε
  obtain ⟨C₂,hC₂,hRet⟩ := ramp_retraction p hp
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro E V I _ _ _ _ _ _ _ src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  dsimp only
  let μ := paretoVectorLaw p g
  let H := 4*Real.log (Fintype.card V : ℝ)
  let N := (Fintype.card I : ℝ)
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hH : 1 ≤ H := by have ht := log_nat_lower (Fintype.card V) hcard; dsimp [H]; linarith
  let : IsProbabilityMeasure μ := paretoVectorLaw_probability p (by linarith) g
  obtain ⟨P,hP,hr,hErr,hVar,hVarE⟩ := hRet E V I src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  change _ ≤ C₂*H^(p-2)*(ℓ:ℝ)/N at hErr
  change _ ≤ 4*aboveVariance p/N at hVar
  change ∀ e, _ ≤ H^2*aboveVariance p/N at hVarE
  let ν := projectedRampLaw μ P ℓ
  have hMoment (q : ℝ) (hq : 0 < q) (e : E) := projectedRampLaw_moment μ P ℓ q hq e
  have hSq (e : E) : (∫ z, (z e)^2 ∂ν)=∫ v, (P.mulVec (fun a => dyadicRamp ℓ (v a)) e)^2 ∂μ := by
    simpa only [Real.rpow_two,sq_abs] using hMoment 2 (by norm_num) e
  refine ⟨ν,inferInstance,projectedRampLaw_symmetry _ _ _,projectedRampLaw_range _ _ _ _ hP,
    projectedRampLaw_bounded _ _ _ H hr,?_,?_,?_⟩
  · have hPert (e : E) : |(∫ z, |z e|^p ∂ν)-b/N| ≤ ε*(b/N)+
        C₁*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ) := by
      rw [hMoment p (by linarith) e]
      apply integrated_power_perturbation μ p ε C₁ (b/N) (by linarith) hScalar
        (fun v => P.mulVec (fun a => dyadicRamp ℓ (v a)) e) (fun v => dyadicRamp ℓ (v e))
        (by dsimp [Matrix.mulVec,dotProduct]; fun_prop) (by fun_prop) (H*2^(2*ℓ)) (by positivity)
      · intro v
        constructor
        · exact (matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e).trans
            (mul_le_mul_of_nonneg_right (hr e) (by positivity))
        · exact (abs_dyadicRamp_le ℓ (v e)).trans (by nlinarith [show (0:ℝ) ≤ 2^(2*ℓ) by positivity])
      · exact paretoVectorLaw_ramp_moment p p (by linarith) (by linarith) g hg ℓ e
    have hSum : (∑ e, w e*|(∫ z, |z e|^p ∂ν)-b/N|) ≤
        ε*(b/N)+C₁*(C₂*H^(p-2)*(ℓ:ℝ)/N) := by
      calc
        _ ≤ ∑ e, w e*(ε*(b/N)+C₁*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ)) :=
          Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hPert e) (hw e).le)
        _ = ε*(b/N)+C₁*(∑ e, w e*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ)) := by
          simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,Finset.mul_sum,hws,one_mul]
          congr 1; apply Finset.sum_congr rfl; intros; ring
        _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hErr hC₁.le) _
    have hh := mul_le_mul_of_nonneg_left hSum hN.le
    have he (e : E) : |N*(∫ z, |z e|^p ∂ν)-b|=N*|(∫ z, |z e|^p ∂ν)-b/N| := by
      rw [show N*(∫ z, |z e|^p ∂ν)-b = N*((∫ z, |z e|^p ∂ν)-b/N) by field_simp,abs_mul,abs_of_pos hN]
    change (∑ e, w e*|N*(∫ z, |z e|^p ∂ν)-b|) ≤ ε*b+(C₁*C₂)*H^(p-2)*(ℓ:ℝ)
    simp_rw [he]
    calc
      _ = N*(∑ e, w e*|(∫ z, |z e|^p ∂ν)-b/N|) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ _ := hh.trans_eq (by field_simp)
  · simp_rw [hSq]
    have hh := mul_le_mul_of_nonneg_left hVar hN.le
    calc
      _ = N*(∑ e, w e*(∫ v, (P.mulVec (fun a => dyadicRamp ℓ (v a)) e)^2 ∂μ)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ N*(4*aboveVariance p/N) := hh
      _ = _ := by field_simp
  · intro e
    rw [hSq]
    exact (mul_le_mul_of_nonneg_left (hVarE e) hN.le).trans_eq (by dsimp [H]; field_simp)

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma interval_moment_error (a M b α T : ℝ) (hb : 0 ≤ b) (hα : 1 ≤ α)
    (hT : 0 ≤ T) (hlo : a ≤ M) (hhi : M ≤ α*a+T) :
    |M-b| ≤ α*|a-b|+(α-1)*b+T := by
  have ha := abs_le.mp (le_refl |a-b|)
  have he : 0 ≤ (α-1)*|a-b| := mul_nonneg (by linarith) (abs_nonneg _)
  have he' : 0 ≤ (α-1)*b := mul_nonneg (by linarith) hb
  apply abs_le.mpr
  constructor <;> nlinarith

lemma weighted_variance_power {E : Type uE} [Fintype E] (w a : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (ha : ∀ e, 0 ≤ a e) (r B T : ℝ)
    (hr : 1 < r) (hB0 : 0 ≤ B) (hB : ∀ e, a e ≤ B) (hT : ∑ e, w e*a e ≤ T) :
    (∑ e, w e*(a e)^r) ≤ B^(r-1)*T := by
  have he (e : E) : (a e)^r ≤ B^(r-1)*a e := by
    calc
      _ = (a e)^(r-1)*a e := by rw [← Real.rpow_add_one' (ha e) (by linarith : r-1+1 ≠ 0)]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (ha e) (hB e) (by linarith)) (ha e)
  calc
    _ ≤ ∑ e, w e*(B^(r-1)*a e) := Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (he e) (hw e))
    _ = B^(r-1)*(∑ e, w e*a e) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hB0 _)

lemma variance_power_algebra (p H U : ℝ) (hH : 0 < H) (hU : 0 < U) :
    (H^2*U)^(p/2-1)*(4*U) = (4*U^(p/2))*H^(p-2) := by
  rw [Real.mul_rpow (sq_nonneg H) hU.le]
  have hHpow : (H^2)^(p/2-1)=H^(p-2) := by
    rw [← Real.rpow_natCast_mul hH.le]
    congr 1
    norm_num
    ring
  have hUpow : U^(p/2-1)*U=U^(p/2) := by
    rw [← Real.rpow_add_one hU.ne']
    congr 1
    ring
  rw [hHpow]
  calc
    _ = 4*(U^(p/2-1)*U)*H^(p-2) := by ring
    _ = _ := by rw [hUpow]

lemma convolutionLaw_weighted_error (p ε U : ℝ) (hp : 2 < p) (hε : 0 < ε) (hU : 0 < U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type uE) [Fintype E]
      (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
      (_hs : ν.map (fun v => -v)=ν) (w : E → ℝ) (_hw : ∀ e, 0 ≤ w e) (_hws : ∑ e, w e=1)
      (B H b err : ℝ) (_hH : 0 < H) (_hb : 0 ≤ b) (N : ℕ)
      (_hB : ∀ᵐ z ∂ν, ∀ e, |z e| ≤ B)
      (_hErr : (∑ e, w e*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|) ≤ err)
      (_hVar : (∑ e, w e*((N:ℝ)*(∫ z, (z e)^2 ∂ν))) ≤ 4*U)
      (_hVarE : ∀ e, (N:ℝ)*(∫ z, (z e)^2 ∂ν) ≤ H^2*U),
      (∑ e, w e*|(∫ z, |z e|^p ∂convolutionPower ν N)-b|) ≤
        (1+ε)^2*err+((1+ε)^2-1)*b+C*H^(p-2) := by
  obtain ⟨C,hC,hMoment⟩ := convolutionPower_near_moment p ε hp hε
  refine ⟨C*(4*U^(p/2)),by positivity,?_⟩
  intro E _ ν _ hs w hw hws B H b err hH hb N hB hErr hVar hVarE
  let a : E → ℝ := fun e => (N:ℝ)*(∫ z, (z e)^2 ∂ν)
  have ha (e : E) : 0 ≤ a e := mul_nonneg (by positivity) (integral_nonneg (fun z => sq_nonneg _))
  have hMomentE (e : E) :
      |(∫ z, |z e|^p ∂convolutionPower ν N)-b| ≤
        (1+ε)^2*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|+((1+ε)^2-1)*b+C*(a e)^(p/2) := by
    have hbnd : ∀ᵐ x ∂coordinateLaw ν e, |x| ≤ B :=
      (coordinateLaw_ae ν e _ (measurableSet_le (by fun_prop) measurable_const)).mpr (hB.mono (fun z hz => hz e))
    have hh := hMoment (coordinateLaw ν e) B hbnd (coordinateLaw_symmetric ν hs e) N
    rw [← coordinateLaw_convolutionPower] at hh
    simp only [coordinateLaw_abs_moment,coordinateLaw_sq_moment] at hh
    exact interval_moment_error _ _ b ((1+ε)^2) (C*(a e)^(p/2)) hb (by nlinarith)
      (by positivity) hh.1 (by simpa only [a,mul_assoc] using hh.2)
  have hVP := weighted_variance_power w a hw ha (p/2) (H^2*U) (4*U) (by linarith) (by positivity) hVarE hVar
  rw [variance_power_algebra p H U hH hU] at hVP
  calc
    _ ≤ ∑ e, w e*((1+ε)^2*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|+((1+ε)^2-1)*b+C*(a e)^(p/2)) :=
      Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hMomentE e) (hw e))
    _ = (1+ε)^2*(∑ e, w e*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|)+((1+ε)^2-1)*b+
        C*(∑ e, w e*(a e)^(p/2)) := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,Finset.mul_sum,hws,one_mul]
      congr 1
      · congr 1; apply Finset.sum_congr rfl; intros; ring
      · apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hErr (sq_nonneg (1+ε))
      have h₂ := mul_le_mul_of_nonneg_left hVP hC
      nlinarith

lemma convolutionLaw_exp_bound {E : Type uE} [Fintype E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (hs : ν.map (fun v => -v)=ν) (J : ℝ) (hJ : 0 < J) (N : ℕ)
    (hB : ∀ᵐ z ∂ν, ∀ e, |z e| ≤ J)
    (hVar : ∀ e, (N:ℝ)*(∫ z, (z e)^2 ∂ν) ≤ J^2) :
    ∀ e (s : ℝ), |s|=1 →
      Integrable (fun z => Real.exp (s*z e/J)) (convolutionPower ν N) ∧
      (∫ z, Real.exp (s*z e/J) ∂convolutionPower ν N) ≤ Real.exp 1 := by
  intro e s hs1
  obtain ⟨hi,hInt⟩ := bounded_symmetric_coordinate_exp ν hs e J hJ (hB.mono (fun z hz => hz e)) s hs1
  have hefun : (fun x : ℝ => Real.exp ((s/J)*x))=fun x => Real.exp (s*x/J) := by funext x; congr 1; ring
  have hi' : Integrable (fun x : ℝ => Real.exp ((s/J)*x)) (coordinateLaw ν e) := by
    rw [hefun,coordinateLaw_integrable _ _ _ (by fun_prop)]
    exact hi
  obtain ⟨hI,hEq⟩ := exp_convolutionPower (coordinateLaw ν e) (s/J) hi' N
  rw [← coordinateLaw_convolutionPower] at hI hEq
  rw [hefun,coordinateLaw_integrable _ _ _ (by fun_prop)] at hI
  simp only [hefun,coordinateLaw_exp_moment] at hEq
  refine ⟨hI,?_⟩
  rw [hEq]
  have hvar0 : 0 ≤ (∫ z, (z e)^2 ∂ν)/J^2 := by positivity
  have hex : 1+(∫ z, (z e)^2 ∂ν)/J^2 ≤ Real.exp ((∫ z, (z e)^2 ∂ν)/J^2) := by
    linarith [Real.add_one_le_exp ((∫ z, (z e)^2 ∂ν)/J^2)]
  have hp : (∫ z, Real.exp (s*z e/J) ∂ν)^N ≤ (Real.exp ((∫ z, (z e)^2 ∂ν)/J^2))^N :=
    pow_le_pow_left₀ (integral_nonneg (fun z => (Real.exp_pos _).le)) (hInt.trans hex) N
  rw [← Real.exp_nat_mul] at hp
  apply hp.trans (Real.exp_le_exp.mpr _)
  rw [← mul_div_assoc]
  exact (div_le_one (sq_pos_of_pos hJ)).mpr (hVar e)

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma exp_abs_le_pair (x : ℝ) : Real.exp |x| ≤ Real.exp x+Real.exp (-x) := by
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]
    linarith [Real.exp_pos x]

lemma mixed_exponential_tail (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J T a b : ℝ), 0 < J → T ≤ |b| →
      |a|^p ≤ C*(2*J)^p*Real.exp (-T/(2*J))*
        (Real.exp (a/J)+Real.exp (-a/J)+Real.exp (b/J)+Real.exp (-b/J)) := by
  obtain ⟨C,hC,hpow⟩ := rpow_le_constant_exp p hp
  refine ⟨C,hC,?_⟩
  intro J T a b hJ hT
  have hJ2 : 0 < 2*J := by positivity
  have hscale : |a|^p ≤ C*(2*J)^p*Real.exp (|a|/(2*J)) := by
    have hh := mul_le_mul_of_nonneg_right (hpow (|a|/(2*J)) (by positivity))
      (Real.rpow_nonneg hJ2.le p)
    rw [Real.div_rpow (abs_nonneg _) hJ2.le,div_mul_cancel₀ _ (Real.rpow_pos_of_pos hJ2 p).ne'] at hh
    nlinarith
  have hexp : Real.exp ((|a|+T)/(2*J)) ≤
      Real.exp (a/J)+Real.exp (-a/J)+Real.exp (b/J)+Real.exp (-b/J) := by
    rcases le_total |a| |b| with hab|hba
    · have hh : (|a|+T)/(2*J) ≤ |b/J| := by
        rw [abs_div,abs_of_pos hJ]
        apply (div_le_div_iff₀ hJ2 hJ).mpr
        nlinarith
      have hbexp := exp_abs_le_pair (b/J)
      rw [← neg_div] at hbexp
      exact (Real.exp_le_exp.mpr hh).trans (by linarith [Real.exp_pos (a/J),Real.exp_pos (-a/J)])
    · have hh : (|a|+T)/(2*J) ≤ |a/J| := by
        rw [abs_div,abs_of_pos hJ]
        apply (div_le_div_iff₀ hJ2 hJ).mpr
        nlinarith
      have haexp := exp_abs_le_pair (a/J)
      rw [← neg_div] at haexp
      exact (Real.exp_le_exp.mpr hh).trans (by linarith [Real.exp_pos (b/J),Real.exp_pos (-b/J)])
  calc
    _ ≤ C*(2*J)^p*Real.exp (|a|/(2*J)) := hscale
    _ = C*(2*J)^p*Real.exp (-T/(2*J))*Real.exp ((|a|+T)/(2*J)) := by
      rw [mul_assoc (C*(2*J)^p),← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

variable {E : Type uE} [Fintype E]

def globalCut (T : ℝ) (z : E → ℝ) : E → ℝ := if ∀ e, |z e| ≤ T then z else 0

lemma measurable_globalCut (T : ℝ) : Measurable (globalCut (E := E) T) := by
  classical
  unfold globalCut
  apply Measurable.ite _ measurable_id measurable_const
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => measurableSet_le (by fun_prop) measurable_const)

lemma globalCut_bound (T : ℝ) (hT : 0 ≤ T) (z : E → ℝ) (e : E) :
    |globalCut T z e| ≤ T := by
  classical
  unfold globalCut
  split_ifs with h
  · exact h e
  · simpa only [Pi.zero_apply,abs_zero] using hT

lemma globalCut_submodule (T : ℝ) (z : E → ℝ) (V : Submodule ℝ (E → ℝ)) (hz : z ∈ V) :
    globalCut T z ∈ V := by
  classical
  unfold globalCut
  split_ifs
  · exact hz
  · exact V.zero_mem

lemma globalCut_power_le (T p : ℝ) (hp : 0 < p) (z : E → ℝ) (e : E) :
    |globalCut T z e|^p ≤ |z e|^p := by
  classical
  unfold globalCut
  split_ifs
  · exact le_refl _
  · simp only [Pi.zero_apply,abs_zero,Real.zero_rpow hp.ne']
    positivity

lemma globalCut_moments (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) [Fintype E]
      (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (J T : ℝ) (_hJ : 0 < J) (_hT : 0 ≤ T)
      (_hI : ∀ e, Integrable (fun z => |z e|^p) μ)
      (_hExp : ∀ e (s : ℝ), |s|=1 → Integrable (fun z => Real.exp (s*z e/J)) μ ∧
        (∫ z, Real.exp (s*z e/J) ∂μ) ≤ Real.exp 1),
      ∀ e, |(∫ z, |globalCut T z e|^p ∂μ)-(∫ z, |z e|^p ∂μ)| ≤
        C*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
  classical
  obtain ⟨C,hC,hScalar⟩ := mixed_exponential_tail p hp.le
  refine ⟨4*Real.exp 1*C,by positivity,?_⟩
  intro E _ μ _ J T hJ hT hI hExp e
  let L := C*(2*J)^p*Real.exp (-T/(2*J))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let Q : (E → ℝ) → E → ℝ := fun z a => Real.exp (z a/J)+Real.exp (-z a/J)
  have hQI (a : E) : Integrable (fun z => Q z a) μ := by
    have h₁ := (hExp a 1 (by norm_num)).1
    have h₂ := (hExp a (-1) (by norm_num)).1
    simp only [one_mul,neg_one_mul] at h₁ h₂
    exact h₁.add h₂
  have hQb (a : E) : (∫ z, Q z a ∂μ) ≤ 2*Real.exp 1 := by
    have h₁ := hExp a 1 (by norm_num)
    have h₂ := hExp a (-1) (by norm_num)
    simp only [one_mul,neg_one_mul] at h₁ h₂
    rw [show (fun z => Q z a)=(fun z => Real.exp (z a/J)+Real.exp (-z a/J)) from rfl, integral_add h₁.1 h₂.1]
    linarith [h₁.2,h₂.2]
  have hCutI : Integrable (fun z => |globalCut T z e|^p) μ :=
    bounded_power_integrable μ (fun z => globalCut T z e) ((measurable_pi_apply e).comp (measurable_globalCut T))
      p T hp hT (fun z => globalCut_bound T hT z e)
  have hpoint (z : E → ℝ) : |z e|^p-|globalCut T z e|^p ≤ L*(∑ a, (Q z e+Q z a)) := by
    by_cases hz : ∀ a, |z a| ≤ T
    · simp only [globalCut,ite_eq_left hz,sub_self]
      exact mul_nonneg hL (Finset.sum_nonneg (fun a _ => by dsimp [Q]; positivity))
    · obtain ⟨a,ha⟩ := not_forall.mp hz
      have hh := hScalar J T (z e) (z a) hJ (le_of_not_ge ha)
      have hsum : Q z e+Q z a ≤ ∑ a, (Q z e+Q z a) :=
        Finset.single_le_sum (f := fun b => Q z e+Q z b) (fun b _ => by dsimp [Q]; positivity) (Finset.mem_univ a)
      simp only [globalCut,ite_eq_right hz,Pi.zero_apply,abs_zero,Real.zero_rpow hp.ne',sub_zero]
      apply hh.trans
      simpa only [L,Q,add_assoc] using mul_le_mul_of_nonneg_left hsum hL
  have hbound : (∫ z, |z e|^p-|globalCut T z e|^p ∂μ) ≤
      L*(4*Real.exp 1*(Fintype.card E : ℝ)) := by
    calc
      _ ≤ ∫ z, L*(∑ a, (Q z e+Q z a)) ∂μ :=
        integral_mono ((hI e).sub hCutI) ((integrable_finsetSum _ (fun a _ => (hQI e).add (hQI a))).const_mul L) hpoint
      _ = L*(∑ a, ((∫ z, Q z e ∂μ)+(∫ z, Q z a ∂μ))) := by
        rw [integral_const_mul,integral_finsetSum]
        · congr 1; apply Finset.sum_congr rfl; intro a _; exact integral_add (hQI e) (hQI a)
        · intro a _; exact (hQI e).add (hQI a)
      _ ≤ L*(∑ _a : E, 4*Real.exp 1) := by
        apply mul_le_mul_of_nonneg_left _ hL
        apply Finset.sum_le_sum
        intro a _
        linarith [hQb e,hQb a]
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hnonneg : (∫ z, |globalCut T z e|^p ∂μ) ≤ ∫ z, |z e|^p ∂μ :=
    integral_mono hCutI (hI e) (fun z => globalCut_power_le T p hp z e)
  rw [integral_sub (hI e) hCutI] at hbound
  rw [abs_of_nonpos (sub_nonpos.mpr hnonneg)]
  dsimp [L] at hbound
  nlinarith

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma weighted_gradient_measure_samples {E : Type uE} {V : Type uV}
    [Fintype E] [Fintype V] [Nonempty E]
    (A : Matrix E V ℝ) (p K b ε : ℝ) (hp : 0 < p) (hK : 0 ≤ K) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ μ : Measure (E → ℝ), IsProbabilityMeasure μ ∧
        (∀ᵐ z ∂μ, ∃ x, A.mulVec x=z) ∧ (∀ᵐ z ∂μ, ∀ e, |z e| ≤ K) ∧
        (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤ ε)
    (d : ℕ) (hd : 0 < d)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1) :
    ∃ z : Fin d → V → ℝ, ∀ e,
      |(∑ a, |A.mulVec (z a) e|^p)/(d:ℝ)-b| < 3*ε := by
  classical
  let S : Set (E → ℝ) := {m | ∃ z : V → ℝ,
    (∀ e, |A.mulVec z e| ≤ K) ∧ ∀ e, m e = |A.mulVec z e|^p}
  have hS : ∀ m ∈ S, ∀ e, m e ∈ Set.Icc 0 (K^p) := by
    rintro m ⟨z,hz,rflz⟩ e
    rw [rflz e]
    exact ⟨Real.rpow_nonneg (abs_nonneg _) _,Real.rpow_le_rpow (abs_nonneg _) (hz e) hp.le⟩
  have hw' : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ m ∈ closedConvexHull ℝ S, (∑ e, w e*|m e-b|) ≤ ε := by
    intro w hw0 hws
    obtain ⟨μ,hμ,hR,hB,hErr⟩ := hw w hw0 hws
    let : IsProbabilityMeasure μ := hμ
    let F : (E → ℝ) → E → ℝ := fun z e => |z e|^p
    have hi (e : E) : Integrable (fun z => F z e) μ :=
      bounded_coordinate_power_integrable μ e p K hp.le (hB.mono (fun z hz => hz e))
    have hIV : Integrable F μ := integrable_pi_iff.mpr hi
    have hFS : ∀ᵐ z ∂μ, F z ∈ S := by
      filter_upwards [hR,hB] with z hz hBz
      obtain ⟨x,hx⟩ := hz
      exact ⟨x,by simpa only [hx] using hBz,fun e => by dsimp [F]; rw [hx]⟩
    have hh := convex_closedConvexHull.integral_mem (isClosed_closedConvexHull (𝕜 := ℝ) (s := S))
      (hFS.mono (fun z hz => subset_closedConvexHull hz)) hIV
    have he : (∫ z, F z ∂μ)=fun e => ∫ z, |z e|^p ∂μ := by
      ext e
      exact ((ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).integral_comp_comm hIV).symm
    rw [he] at hh
    exact ⟨_,hh,hErr⟩
  obtain ⟨m,hm,hme⟩ := weighted_moments_samples (S := S) (K^p)
    (Real.rpow_nonneg hK _) hS b ε hε hw' d hd hprob
  choose z hz hmz using hm
  refine ⟨z,fun e => ?_⟩
  simpa only [hmz] using hme e

variable {E : Type uE} [Fintype E]

def globalCutLaw (μ : Measure (E → ℝ)) (T : ℝ) : Measure (E → ℝ) := μ.map (globalCut T)

instance globalCutLaw_probability (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (T : ℝ) :
    IsProbabilityMeasure (globalCutLaw μ T) := by
  unfold globalCutLaw
  exact Measure.isProbabilityMeasure_map (measurable_globalCut T).aemeasurable

lemma globalCutLaw_moment (μ : Measure (E → ℝ)) (T p : ℝ) (e : E) :
    (∫ z, |z e|^p ∂globalCutLaw μ T)=∫ z, |globalCut T z e|^p ∂μ :=
  integral_map (measurable_globalCut T).aemeasurable (show Measurable (fun z : E → ℝ => |z e|^p) by fun_prop).aestronglyMeasurable

lemma globalCutLaw_bound (μ : Measure (E → ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ z ∂globalCutLaw μ T, ∀ e, |z e| ≤ T := by
  apply ae_all_iff.mpr
  intro e
  apply (ae_map_iff (measurable_globalCut T).aemeasurable (measurableSet_le (by fun_prop) measurable_const)).mpr
  exact ae_of_all _ (fun z => globalCut_bound T hT z e)

lemma globalCutLaw_submodule (μ : Measure (E → ℝ)) (T : ℝ) (V : Submodule ℝ (E → ℝ))
    (hV : ∀ᵐ z ∂μ, z ∈ V) : ∀ᵐ z ∂globalCutLaw μ T, z ∈ V := by
  apply (ae_map_iff (measurable_globalCut T).aemeasurable V.closed_of_finiteDimensional.measurableSet).mpr
  exact hV.mono (fun z hz => globalCut_submodule T z V hz)

omit [Fintype E] in
lemma convolutionPower_coordinate_integrable (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (B p : ℝ) (hp : 0 ≤ p) (hB : ∀ᵐ z ∂μ, ∀ e, |z e| ≤ B) (N : ℕ) (e : E) :
    Integrable (fun z => |z e|^p) (convolutionPower μ N) := by
  have hb : ∀ᵐ x ∂coordinateLaw μ e, |x| ≤ B :=
    (coordinateLaw_ae μ e _ (measurableSet_le (by fun_prop) measurable_const)).mpr (hB.mono (fun z hz => hz e))
  have hi := bounded_abs_moment_integrable (convolutionPower (coordinateLaw μ e) N) ((N:ℝ)*B) p
    (convolutionPower_bounded _ _ hb N) hp
  rw [← coordinateLaw_convolutionPower,coordinateLaw_integrable _ _ _ (by fun_prop)] at hi
  exact hi

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma ramp_sum_bounded_law (p ε : ℝ) (hp : 2 < p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) (V : Type uV) (I : Type uI) [Fintype E] [Fintype V] [Fintype I]
      [DecidableEq E] [DecidableEq V] [Nonempty E] [Nonempty I]
      (src dst : E → V) (δ w : E → ℝ) (_hδ : ∀ e, 0 < δ e)
      (_hw : ∀ e, 0 < w e) (_hws : ∑ e, w e=1)
      (_hcard : 2 ≤ Fintype.card V)
      (_hinc : ∀ i : V, ∃ e, src e=i ∨ dst e=i)
      (_hconn : ∀ i j : V, i ≠ j → ∃ e,
        (src e=i ∧ dst e=j) ∨ (src e=j ∧ dst e=i))
      (g : I → E → ℝ) (_hg : ∀ e, ∑ i, |g i e|^p=1)
      (_hgr : ∀ i, ∃ x, (normalizedGradient src dst δ).mulVec x=g i)
      (ℓ : ℕ) (T : ℝ) (_hT : 0 ≤ T),
      let H := 4*Real.log (Fintype.card V : ℝ)
      let J := (aboveVariance p+1)*H*2^(2*ℓ)
      let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
      ∃ μ : Measure (E → ℝ), IsProbabilityMeasure μ ∧
        (∀ᵐ z ∂μ, ∃ x, (normalizedGradient src dst δ).mulVec x=z) ∧
        (∀ᵐ z ∂μ, ∀ e, |z e| ≤ T) ∧
        (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤
          ((1+ε)^3-1)*b+C*H^(p-2)*((ℓ:ℝ)+1)+
            C*J^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
  classical
  let U := aboveVariance p
  have hU : 0 < U := aboveVariance_pos p hp
  obtain ⟨C₁,hC₁,hJump⟩ := ramp_jump_law p ε hp hε
  obtain ⟨C₂,hC₂,hSum⟩ := convolutionLaw_weighted_error p ε U hp hε hU
  obtain ⟨C₃,hC₃,hCut⟩ := globalCut_moments p (by linarith only [hp])
  let C := (1+ε)^2*C₁+C₂+C₃*2^p+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₁' : (1+ε)^2*C₁ ≤ C := by
    dsimp [C]
    have hh : 0 ≤ C₃*2^p := by positivity
    linarith only [hC₂,hh]
  have hC₂' : C₂ ≤ C := by
    dsimp [C]
    have hh : 0 ≤ (1+ε)^2*C₁+C₃*2^p := by positivity
    linarith only [hh]
  have hC₃' : C₃*2^p ≤ C := by
    dsimp [C]
    have hh : 0 ≤ (1+ε)^2*C₁ := by positivity
    linarith only [hC₂,hh]
  refine ⟨C,hC,?_⟩
  intro E V I _ _ _ _ _ _ _ src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ T hT
  dsimp only
  let H := 4*Real.log (Fintype.card V : ℝ)
  let J := (U+1)*H*2^(2*ℓ)
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  have hH : 1 ≤ H := by have hh := log_nat_lower (Fintype.card V) hcard; dsimp [H]; linarith only [hh]
  have hH0 : 0 < H := by linarith only [hH]
  have hJ : 0 < J := by dsimp [J]; positivity
  have hL : (1:ℝ) ≤ 2^(2*ℓ) := one_le_pow₀ (by norm_num)
  have hB : H*2^(2*ℓ) ≤ J := by
    calc
      _ ≤ (U+1)*(H*2^(2*ℓ)) := le_mul_of_one_le_left (by positivity) (by linarith only [hU])
      _ = _ := by dsimp [J]; ring
  have hVarB : H^2*U ≤ J^2 := by
    have hj : (U+1)*H ≤ J := by dsimp [J]; exact le_mul_of_one_le_right (by positivity) hL
    have hj0 : 0 ≤ (U+1)*H := by positivity
    have hsq := (sq_le_sq₀ hj0 hJ.le).mpr hj
    have hu : U ≤ (U+1)^2 := by nlinarith [sq_nonneg U]
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg H)
    nlinarith only [hsq,hh]
  obtain ⟨ν,hν,hs,hRange,hBound,hErr,hVar,hVarE⟩ :=
    hJump E V I src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  let : IsProbabilityMeasure ν := hν
  let N := Fintype.card I
  let W := convolutionPower ν N
  have hBoundJ : ∀ᵐ z ∂ν, ∀ e, |z e| ≤ J := hBound.mono (fun z hz e => (hz e).trans hB)
  have hExp := convolutionLaw_exp_bound ν hs J hJ N hBoundJ (fun e => (hVarE e).trans hVarB)
  have hWi (e : E) : Integrable (fun z => |z e|^p) W :=
    convolutionPower_coordinate_integrable ν J p (by linarith only [hp]) hBoundJ N e
  have hWErr := hSum E ν hs w (fun e => (hw e).le) hws (H*2^(2*ℓ)) H b
    (ε*b+C₁*H^(p-2)*(ℓ:ℝ)) hH0 (integral_nonneg (fun r => Real.rpow_nonneg (abs_nonneg _) _))
    N hBound hErr hVar hVarE
  let μ := globalCutLaw W T
  have hRangeW : ∀ᵐ z ∂W, z ∈ LinearMap.range (Matrix.toLin' (normalizedGradient src dst δ)) :=
    convolutionPower_submodule ν _ hRange N
  have hRangeμ := globalCutLaw_submodule W T _ hRangeW
  refine ⟨μ,inferInstance,hRangeμ,globalCutLaw_bound W T hT,?_⟩
  have hCutE (e : E) : |(∫ z, |z e|^p ∂μ)-(∫ z, |z e|^p ∂W)| ≤
      C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
    rw [globalCutLaw_moment]
    exact hCut E W J T hJ hT hWi hExp e
  have hCutSum : (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤
      (∑ e, w e*|(∫ z, |z e|^p ∂W)-b|)+C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
    calc
      _ ≤ ∑ e, w e*(|(∫ z, |z e|^p ∂W)-b|+
          C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ)) := by
        apply Finset.sum_le_sum
        intro e _
        apply mul_le_mul_of_nonneg_left _ (hw e).le
        exact (abs_sub_le _ _ _).trans (by
          calc
            _ ≤ C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ)+
                |(∫ z, |z e|^p ∂W)-b| := add_le_add (hCutE e) le_rfl
            _ = _ := add_comm _ _)
      _ = _ := by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hws,one_mul]
  have hCGe : (1+ε)^2*C₁*(ℓ:ℝ)+C₂ ≤ C*((ℓ:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_right hC₁' (show (0:ℝ) ≤ ℓ by positivity)
    nlinarith only [hh,hC₂']
  have hCore := mul_le_mul_of_nonneg_right hCGe (Real.rpow_nonneg hH0.le (p-2))
  have hTail : C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) ≤
      C*J^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith only [hC₃',Real.rpow_nonneg hJ.le p] : C₃*(2^p*J^p) ≤ C*J^p)
        (Real.exp_pos _).le) (by positivity)
  change _ ≤ ((1+ε)^3-1)*b+C*H^(p-2)*((ℓ:ℝ)+1)+C*J^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ)
  nlinarith only [hWErr,hCutSum,hCore,hTail]

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma global_cutoff_tail (p C J : ℝ) (hC : 0 < C) (hJ : 0 < J)
    (n : ℕ) (hn : 2 ≤ n) :
    let H := 4*Real.log (n:ℝ)
    let T := 2*J*(p*Real.log J+H+Real.log (C+1))
    C*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ 1 := by
  dsimp only
  let H := 4*Real.log (n:ℝ)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hnum : (n:ℝ)^2 ≤ Real.exp H := by
    calc
      _ = Real.exp (2*Real.log (n:ℝ)) := by
        simpa only [Nat.cast_ofNat, Real.exp_log hn0] using (Real.exp_nat_mul (Real.log (n:ℝ)) 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [H]; linarith)
  have he : J^p*Real.exp (-(2*J*(p*Real.log J+H+Real.log (C+1)))/(2*J)) = Real.exp (-H)/(C+1) := by
    rw [neg_div,mul_div_cancel_left₀ _ (show 2*J ≠ 0 by positivity),Real.rpow_def_of_pos hJ,← Real.exp_add]
    rw [show Real.log J*p+ -(p*Real.log J+H+Real.log (C+1)) = -H-Real.log (C+1) by ring,
      Real.exp_sub,Real.exp_log (by positivity : 0 < C+1)]
  have hE : Real.exp (-H)*(n:ℝ)^2 ≤ 1 := by
    calc
      _ ≤ Real.exp (-H)*Real.exp H := mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hfrac : 0 ≤ C/(C+1) := by positivity
  have hfrac1 : C/(C+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  calc
    _ = C*(J^p*Real.exp (-(2*J*(p*Real.log J+H+Real.log (C+1)))/(2*J)))*(n:ℝ)^2 := by ring
    _ = (C/(C+1))*(Real.exp (-H)*(n:ℝ)^2) := by rw [he]; ring
    _ ≤ C/(C+1) := by nlinarith
    _ ≤ 1 := hfrac1

lemma ramp_cutoff_envelope (p C U L r : ℝ) (hp : 0 < p) (hC : 0 < C)
    (hU : 0 < U) (hL : 1 ≤ L) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ H : ℝ, 1 ≤ H →
      let m := ⌈L*(H^r+1)⌉₊+1
      let J := (U+1)*H*2^(2*(2*m))
      let T := 2*J*(p*Real.log J+H+Real.log (C+1))
      1 ≤ J ∧ 0 ≤ T ∧ T ≤ H^2*Real.exp (A*(H^r+1)) := by
  let B := 4*Real.log 2*(L+2)
  have hB : 0 < B := by dsimp [B]; positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  let B₂ := p*(U+2+2*B)+C+2
  have hB₂ : 0 < B₂ := by dsimp [B₂]; positivity
  let M := 2*(U+1)*B₂
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨B+M+1,by positivity,fun H hH => ?_⟩
  dsimp only
  let m := ⌈L*(H^r+1)⌉₊+1
  let J := (U+1)*H*2^(2*(2*m))
  let T := 2*J*(p*Real.log J+H+Real.log (C+1))
  have hH0 : 0 < H := by linarith
  have hHr : 1 ≤ H^r := Real.one_le_rpow hH hr0.le
  have hHrH : H^r ≤ H := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH hr1.le
  have hm : (m:ℝ) ≤ (L+2)*(H^r+1) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ L*(H^r+1) by positivity)
    dsimp [m]
    push_cast
    nlinarith
  have hpow1 : (1:ℝ) ≤ 2^(2*(2*m)) := one_le_pow₀ (by norm_num)
  have hJ1 : 1 ≤ J := by
    have hHpow : H ≤ H*2^(2*(2*m)) := le_mul_of_one_le_right hH0.le hpow1
    dsimp [J]
    nlinarith [mul_nonneg hU.le (show 0 ≤ H*2^(2*(2*m)) by positivity)]
  have hJ : 0 < J := by linarith
  have hpow : (2:ℝ)^(2*(2*m)) ≤ Real.exp (B*(H^r+1)) := by
    calc
      _ = Real.exp ((2*(2*m):ℕ)*Real.log 2) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4*Real.log 2 by positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)])
        dsimp [B]
        push_cast
        nlinarith
  have hJbound : J ≤ (U+1)*H*Real.exp (B*(H^r+1)) := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hlogJ : Real.log J ≤ (U+2+2*B)*H := by
    have hh := Real.log_le_log hJ hJbound
    rw [Real.log_mul (by positivity : (U+1)*H ≠ 0) (Real.exp_ne_zero _),Real.log_exp,
      Real.log_mul (by positivity : U+1 ≠ 0) hH0.ne'] at hh
    have hu := Real.log_le_sub_one_of_pos (show 0 < U+1 by positivity)
    have hhlog := Real.log_le_sub_one_of_pos hH0
    have hr := mul_le_mul_of_nonneg_left hHrH hB.le
    have hb := mul_le_mul_of_nonneg_left hH hB.le
    have huH := mul_le_mul_of_nonneg_left hH (show 0 ≤ U+1 by positivity)
    nlinarith
  have hinside : p*Real.log J+H+Real.log (C+1) ≤ B₂*H := by
    have hpJ := mul_le_mul_of_nonneg_left hlogJ hp.le
    have hc := Real.log_le_sub_one_of_pos (show 0 < C+1 by positivity)
    have hcH := mul_le_mul_of_nonneg_left hH (show 0 ≤ C+1 by positivity)
    dsimp [B₂]
    nlinarith
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (by positivity) (by positivity [Real.log_nonneg hJ1,Real.log_nonneg (show 1 ≤ C+1 by linarith)])
  refine ⟨hJ1,hT0,?_⟩
  have hTbound : T ≤ M*H^2*Real.exp (B*(H^r+1)) := by
    calc
      _ ≤ (2*J)*(B₂*H) := mul_le_mul_of_nonneg_left hinside (by positivity)
      _ ≤ (2*((U+1)*H*Real.exp (B*(H^r+1))))*(B₂*H) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJbound (by norm_num)) (by positivity)
      _ = _ := by dsimp [M]; ring
  have hfactor : M*Real.exp (B*(H^r+1)) ≤ Real.exp ((B+M+1)*(H^r+1)) := by
    calc
      _ ≤ Real.exp M*Real.exp (B*(H^r+1)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp M]) (Real.exp_pos _).le
      _ = Real.exp (M+B*(H^r+1)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact hTbound.trans (by nlinarith [mul_le_mul_of_nonneg_left hfactor (sq_nonneg H)])

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma above_small_error (R : ℝ) (hR : 3 < R) :
    let ε := 1/(28*R)
    0 < ε ∧ ((1+ε)^3-1) ≤ 1/(2*R) := by
  let ε := 1/(28*R)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεR : ε*(28*R)=1 := div_mul_cancel₀ 1 (by positivity)
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hε2 : ε^2 ≤ ε := by nlinarith [mul_le_mul_of_nonneg_left hε1 hε.le]
  have hε3 : ε^3 ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left hε2 hε.le
    nlinarith
  refine ⟨hε,?_⟩
  calc
    _ ≤ 7*ε := by nlinarith
    _ ≤ 1/(2*R) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hεR])

lemma above_numeric_parameters (p R C β : ℝ) (hp : 2 < p) (hR : 3 < R)
    (hC : 0 < C) (hβ : β ≤ 1/(2*R)) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 2 ≤ n → ∃ (ℓ : ℕ) (T : ℝ),
      let H := 4*Real.log (n:ℝ)
      let J := (aboveVariance p+1)*H*2^(2*ℓ)
      let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
      0 ≤ T ∧ T ≤ H^2*Real.exp (A*(H^(1-2/p)+1)) ∧ 1 ≤ b/R ∧
      β*b+C*H^(p-2)*((ℓ:ℝ)+1)+C*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ b/R := by
  have hp0 : 0 < p := by linarith
  have hR0 : 0 < R := by linarith
  let c := p*Real.log 2
  have hc : 0 < c := by dsimp [c]; positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  let L := 2*R*(3*C+1)/c+1
  have hL : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_left (by positivity)
  have hcL : 2*R*(3*C+1) ≤ c*L := by
    have he : c*L=2*R*(3*C+1)+c := by dsimp [L]; field_simp
    rw [he]
    linarith
  have hr0 : 0 < 1-2/p := by apply sub_pos.mpr; exact (div_lt_one hp0).mpr hp
  have hr1 : 1-2/p < 1 := by
    have hh : 0 < 2/p := by positivity
    linarith
  have hU := aboveVariance_pos p hp
  obtain ⟨A,hA,hEnvelope⟩ := ramp_cutoff_envelope p C (aboveVariance p) L (1-2/p) hp0 hC hU hL hr0 hr1
  refine ⟨A,hA,fun n hn => ?_⟩
  let H := 4*Real.log (n:ℝ)
  have hH : 1 ≤ H := by have hh := log_nat_lower n hn; dsimp [H]; linarith
  have hH0 : 0 < H := by linarith
  let m := ⌈L*(H^(1-2/p)+1)⌉₊+1
  let ℓ := 2*m
  let J := (aboveVariance p+1)*H*2^(2*ℓ)
  let T := 2*J*(p*Real.log J+H+Real.log (C+1))
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hm1R : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0:ℝ) < m := by linarith
  have hmp : L*H^(p-2) ≤ (m:ℝ)^p := by
    have hmL : L*H^(1-2/p) ≤ (m:ℝ) := by
      have hh := Nat.le_ceil (L*(H^(1-2/p)+1))
      dsimp [m]
      push_cast
      nlinarith
    have hLp : L ≤ L^p := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by linarith : (1:ℝ) ≤ p)
    have hexp : (H^(1-2/p))^p=H^(p-2) := by
      rw [← Real.rpow_mul hH0.le]
      congr 1
      field_simp
    calc
      _ ≤ L^p*H^(p-2) := mul_le_mul_of_nonneg_right hLp (Real.rpow_nonneg hH0.le _)
      _ = (L*H^(1-2/p))^p := by rw [Real.mul_rpow (by linarith : 0 ≤ L) (Real.rpow_nonneg hH0.le _),hexp]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hmL hp0.le
  have hHp : 1 ≤ H^(p-2) := Real.one_le_rpow hH (by linarith)
  have hb0 : 0 ≤ b := integral_nonneg (fun r => Real.rpow_nonneg (abs_nonneg _) _)
  have henergy : c*(m:ℝ)^p*(m:ℝ) ≤ b := by
    have hh := pareto_dyadicRamp_energy_lower p hp0 m hm1
    rw [Real.rpow_add_one hm0.ne'] at hh
    change c*((m:ℝ)^p*(m:ℝ)) ≤ b at hh
    nlinarith only [hh]
  have hbBig : 2*R*(3*C+1)*(m:ℝ)*H^(p-2) ≤ b := by
    have h₁ := mul_le_mul_of_nonneg_right hcL (show 0 ≤ (m:ℝ)*H^(p-2) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hmp (show 0 ≤ c*(m:ℝ) by positivity)
    nlinarith only [h₁,h₂,henergy]
  have hrest : C*H^(p-2)*((ℓ:ℝ)+1)+1 ≤ b/(2*R) := by
    have hmh : 1 ≤ (m:ℝ)*H^(p-2) := by nlinarith
    have hm3 : (ℓ:ℝ)+1 ≤ 3*(m:ℝ) := by dsimp [ℓ]; push_cast; linarith
    have hcore := mul_le_mul_of_nonneg_left hm3 (show 0 ≤ C*H^(p-2) by positivity)
    have hh : C*H^(p-2)*((ℓ:ℝ)+1)+1 ≤ (3*C+1)*(m:ℝ)*H^(p-2) := by nlinarith only [hcore,hmh]
    apply (le_div_iff₀ (by positivity : 0 < 2*R)).mpr
    have hr := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*R by positivity)
    nlinarith only [hr,hbBig]
  have hbR : R ≤ b := by
    have hc0 : 0 ≤ C*H^(p-2)*((ℓ:ℝ)+1) := by positivity
    have hh := (le_div_iff₀ (by positivity : 0 < 2*R)).mp hrest
    nlinarith
  have hEnv := hEnvelope H hH
  change 1 ≤ J ∧ 0 ≤ T ∧ T ≤ H^2*Real.exp (A*(H^(1-2/p)+1)) at hEnv
  have hJ : 0 < J := by linarith [hEnv.1]
  have htail := global_cutoff_tail p C J hC hJ n hn
  change C*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ 1 at htail
  refine ⟨ℓ,T,hEnv.2.1,hEnv.2.2,(le_div_iff₀ hR0).mpr (by simpa only [one_mul] using hbR),?_⟩
  have hbet := mul_le_mul_of_nonneg_right hβ hb0
  have hhalf : (1/(2*R))*b+b/(2*R)=b/R := by ring
  calc
    _ ≤ (1/(2*R))*b+(C*H^(p-2)*((ℓ:ℝ)+1)+1) := by linarith
    _ ≤ (1/(2*R))*b+b/(2*R) := by linarith only [hrest]
    _ = _ := hhalf

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma above_main_upper (p D : ℝ) (hp : 2 < p) (hD : 1 < D) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C*(Real.log (n:ℝ))^(1-2/p)) := by
  classical
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  obtain ⟨R,hR,hRD⟩ := distortion_ratio p D hp0 hD
  let η := 1/(28*R)
  obtain ⟨hη,hηsmall⟩ := above_small_error R hR
  change 0 < η at hη
  change ((1+η)^3-1) ≤ 1/(2*R) at hηsmall
  obtain ⟨C₀,hC₀,hLaw⟩ := ramp_sum_bounded_law p η hp hη
  obtain ⟨A,hA,hParam⟩ := above_numeric_parameters p R C₀ ((1+η)^3-1) hp hR hC₀ hηsmall
  let C := (3+(4*p+1)/(1-2/p)+4*p*A)*4^(1-2/p)
  refine ⟨C,fun n hn => ?_⟩
  obtain ⟨ℓ,T,hT,hTK,hbR,hError⟩ := hParam n hn
  let H := 4*Real.log (n:ℝ)
  let J := (aboveVariance p+1)*H*2^(2*ℓ)
  let K := H^2*Real.exp (A*(H^(1-2/p)+1))
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  let ε := b/R
  change T ≤ K at hTK
  change 1 ≤ ε at hbR
  change ((1+η)^3-1)*b+C₀*H^(p-2)*((ℓ:ℝ)+1)+
    C₀*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ ε at hError
  have hH : 0 < H := by
    have hh := log_nat_lower n hn
    dsimp [H]
    linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity [aboveVariance_pos p hp]
  have hε : 0 < ε := zero_lt_one.trans_le hbR
  have hbε : R*ε ≤ b := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ (show R ≠ 0 by linarith)]
  obtain ⟨hb,hDb⟩ := hRD b ε hε hbε
  let d := ⌈(K^p)^2*(H+1)⌉₊+1
  have hd : 0 < d := by dsimp [d]; omega
  have hgood : GoodDimension.{u} p n D d := by
    intro Ω mΩ ν x hx
    let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1.le⟩
    let : Nonempty (PairIndex n) := pairIndex_nonempty n hn
    let : Nonempty (Fin (n.choose 2)) := Fin.pos_iff_nonempty.mp (Nat.choose_pos hn)
    obtain ⟨y,hy⟩ := exact_discretization p hp1 n hn ν x hx
    let δ : PairIndex n → ℝ := fun e => ‖x e.val.1-x e.val.2‖
    have hδ (e : PairIndex n) : 0 < δ e :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => (ne_of_lt e.2) (hx he)))
    let B := normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ
    let g : Fin (n.choose 2) → PairIndex n → ℝ := fun a => B.mulVec (fun i => y i a)
    have hg : ∀ e, ∑ a, |g a e|^p = 1 :=
      normalized_coordinate_gradient p hp0 y δ hδ (fun e => hy e.val.1 e.val.2)
    have hw : ∀ w : PairIndex n → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
        ∃ μ : Measure (PairIndex n → ℝ), IsProbabilityMeasure μ ∧
          (∀ᵐ z ∂μ, ∃ v, B.mulVec v=z) ∧ (∀ᵐ z ∂μ, ∀ e, |z e| ≤ K) ∧
          (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤ ε := by
      intro w hw0 hws
      obtain ⟨μ,hμ,hRange,hBound,hErr⟩ :=
        hLaw (PairIndex n) (Fin n) (Fin (n.choose 2))
          (fun e => e.val.1) (fun e => e.val.2) δ w hδ hw0 hws
          (by simpa using hn) (pairIndex_incident n hn) (pairIndex_connected n)
          g hg (fun a => ⟨fun i => y i a,rfl⟩) ℓ T hT
      have hHn : (4*Real.log (Fintype.card (Fin n):ℝ)) = H := by simp [H]
      rw [hHn] at hErr
      refine ⟨μ,hμ,hRange,hBound.mono (fun z hz e => (hz e).trans hTK),?_⟩
      have hcard : (Fintype.card (PairIndex n):ℝ) ≤ (n:ℝ)^2 := by
        exact_mod_cast pairIndex_card_le_square n
      have htail := mul_le_mul_of_nonneg_left hcard
        (show 0 ≤ C₀*J^p*Real.exp (-T/(2*J)) by positivity)
      exact hErr.trans ((by linarith only [htail] :
        ((1+η)^3-1)*b+C₀*H^(p-2)*((ℓ:ℝ)+1)+
          C₀*J^p*Real.exp (-T/(2*J))*(Fintype.card (PairIndex n):ℝ) ≤
        ((1+η)^3-1)*b+C₀*H^(p-2)*((ℓ:ℝ)+1)+
          C₀*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2).trans hError)
    have hprob : (2*Fintype.card (PairIndex n):ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1 :=
      sampling_probability_estimate (K^p) ε (Real.rpow_pos_of_pos hK _) hbR n _ hn
        Fintype.card_pos (pairIndex_card_le_square n)
    obtain ⟨z,hz⟩ := weighted_gradient_measure_samples B p K b ε hp0 hK.le hε hw d hd hprob
    obtain ⟨s,hs,hse⟩ := sampled_labels_embedding p D b ε hp0 (by linarith) hb hDb hd δ hδ z hz
    refine ⟨fun i a => z a i,s,hs,?_⟩
    exact all_pairs_of_edge_bounds p D s hp0 x (fun i a => z a i) hse
  have hdim : dimension.{u} p n D ≤ d := Nat.sInf_le hgood
  have hr : 0 < 1-2/p := by
    apply sub_pos.mpr
    exact (div_lt_one hp0).mpr hp
  have hnumer := sampling_dimension_estimate p (1-2/p) A hp0 hr hA.le n hn
  exact (show (dimension.{u} p n D:ℝ) ≤ d by exact_mod_cast hdim).trans hnumer

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

lemma subpower_log_limit (f : ℕ → ℕ) (C r : ℝ) (hr : r < 1)
    (hpos : ∀ᶠ n in atTop, 0 < f n)
    (hup : ∀ᶠ n in atTop, (f n : ℝ) ≤ Real.exp (C*Real.log (n:ℝ)^r)) :
    Tendsto (fun n : ℕ => Real.log (f n : ℝ)/Real.log (n:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ => C*Real.log (n:ℝ)^(r-1)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by linarith : 0 < 1-r)).comp hlog
    simpa only [neg_sub, mul_zero, Function.comp_def] using hh.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
  · exact Filter.Eventually.of_forall (fun n => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
  · filter_upwards [hpos, hup, Filter.eventually_ge_atTop 2] with n hn hu hn2
    have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hl := Real.log_pos hnR
    have hf : (0:ℝ) < f n := by exact_mod_cast hn
    have hh := Real.log_le_log hf hu
    rw [Real.log_exp] at hh
    rw [Real.rpow_sub hl, Real.rpow_one]
    calc
      _ ≤ (C*Real.log (n:ℝ)^r)/Real.log (n:ℝ) := div_le_div_of_nonneg_right hh hl.le
      _ = _ := by ring

end SubpolynomialLp

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

namespace SubpolynomialLp

/-- The universal coordinate dimension bounds and their logarithmic limits. -/
theorem source_main_oai (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) :
    (∀ D : ℝ, 1 < D → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      GoodDimension.{u} p n D (dimension.{u} p n D) ∧
      Real.log (n : ℝ) / Real.log (1 + 2 * D) ≤ (dimension.{u} p n D : ℝ) ∧
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C * Real.log (n : ℝ) ^ gamma p)) ∧
    (∀ n : ℕ, 9 ≤ n →
      GoodDimension.{u} p n 1 (dimension.{u} p n 1) ∧
      ((n - 1) / 4) ^ 2 ≤ dimension.{u} p n 1 ∧
      dimension.{u} p n 1 ≤ n.choose 2) ∧
    (∀ D : ℝ, 1 ≤ D →
      Tendsto (fun n : ℕ => Real.log (dimension.{u} p n D : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (if 1 < D then 0 else 2))) := by
  have hupper : ∀ D : ℝ, 1 < D → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C * Real.log (n : ℝ) ^ gamma p) := by
    intro D hD
    rcases lt_or_gt_of_ne hp2 with hlt|hgt
    · simpa only [gamma,ite_eq_left hlt] using below_main_upper.{u} p D hp hlt hD
    · simpa only [gamma,ite_eq_right (not_lt.mpr hgt.le)] using above_main_upper.{u} p D hgt hD
  refine ⟨?_,fun n hn => exact_dimension_bounds p hp hp2 n hn,?_⟩
  · intro D hD
    obtain ⟨C,hC⟩ := hupper D hD
    exact ⟨C,fun n hn => ⟨dimension_good p hp n hn D hD.le,
      dimension_packing_lower p hp n hn D hD.le,hC n hn⟩⟩
  · intro D hD
    by_cases hD1 : 1 < D
    · rw [ite_eq_left hD1]
      obtain ⟨C,hC⟩ := hupper D hD1
      have hγ : gamma p < 1 := by
        unfold gamma
        split_ifs
        · linarith
        · have hh : 0 < 2/p := by positivity
          linarith
      apply subpower_log_limit (fun n => dimension.{u} p n D) C (gamma p) hγ
      · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
        have hl := dimension_packing_lower.{u} p hp n hn D hD
        have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        have hdpos : (0:ℝ) < dimension.{u} p n D :=
          lt_of_lt_of_le (div_pos (Real.log_pos hn1) (Real.log_pos (by linarith))) hl
        exact_mod_cast hdpos
      · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
        exact hC n hn
    · have hDeq : D=1 := by linarith
      subst D
      simpa only [lt_self_iff_false,ite_false] using exact_dimension_log_limit.{u} p hp hp2

end SubpolynomialLp

end

end OAI
end
end

theorem solution : type_of% @OAI.SubpolynomialLp.source_main_oai := @OAI.SubpolynomialLp.source_main_oai
