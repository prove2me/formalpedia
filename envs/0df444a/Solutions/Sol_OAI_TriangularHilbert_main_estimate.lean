-- Prove2me | solution 1 for OAI.TriangularHilbert.main_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T16:28:13.601001+00:00
-- url     : https://prove2.me/submissions/a5229695-74f4-4c57-a269-9c8dd6899e6f

import Mathlib
import Definitions.Def_TriangularHilbert

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

universe uι uκ uX uμ uν uE uF uα

section
section
namespace OAI

section

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace TriangularHilbert

end TriangularHilbert
end
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma sq_le_cube_add_one {x : ℝ} (hx : 0 ≤ x) : x^2 ≤ x^3+1 := by
  by_cases h : x ≤ 1
  · have hs := pow_le_pow_left₀ hx h 2
    nlinarith [pow_nonneg hx 3]
  · have hm := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith

lemma mul_le_cube_add_cube_add_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x*y ≤ x^3+y^3+2 := by
  nlinarith [sq_nonneg (x-y),sq_le_cube_add_one hx,sq_le_cube_add_one hy,
    pow_nonneg hx 3,pow_nonneg hy 3]

lemma norm_product_kernel_le (f g : ℝ → ℂ) (K : ℝ → ℝ) {D E : ℝ → ℝ} {L : ℝ}
    (_hL : 0 ≤ L) {c : ℝ} (hf : ‖f c‖^3 ≤ D c) (hg : ‖g c‖^3 ≤ E c)
    (hk : |K c| ≤ L) : ‖f c*g c*(K c:ℂ)‖ ≤ (D c+E c+2)*L := by
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hp := mul_le_cube_add_cube_add_two (norm_nonneg (f c)) (norm_nonneg (g c))
  have hD : 0 ≤ D c := (pow_nonneg (norm_nonneg _) 3).trans hf
  have hE : 0 ≤ E c := (pow_nonneg (norm_nonneg _) 3).trans hg
  exact mul_le_mul (by linarith : ‖f c‖*‖g c‖ ≤ D c+E c+2) hk (abs_nonneg _) (by positivity)

lemma integrable_product_bounded_kernel (f g : ℝ → ℂ) (K : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) (hK : Measurable K)
    {D E : ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hbound : ∀ᵐ c : ℝ, ‖f c‖^3 ≤ D c ∧ ‖g c‖^3 ≤ E c)
    {s : Set ℝ} (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) {L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ c, |K c| ≤ L) (hzero : ∀ c ∉ s, K c = 0) :
    Integrable (fun c => f c*g c*(K c:ℂ)) := by
  have hb : Integrable (s.indicator (fun c => (D c+E c+2)*L)) :=
    IntegrableOn.integrable_indicator
      (((hD.integrableOn.add hE.integrableOn).add (integrableOn_const (C := (2:ℝ)) hμ)).mul_const L) hs
  apply hb.mono' ((hf.mul hg).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable))
  filter_upwards [hbound] with c hc
  by_cases hc' : c ∈ s
  · rw [Set.indicator_of_mem hc']
    exact norm_product_kernel_le f g K hL hc.1 hc.2 (hk c)
  · simp only [Pi.mul_apply,hzero c hc',Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem hc',le_refl]

lemma tendsto_integral_product_bounded_kernel (f g : ℝ → ℂ) (F G : ℕ → ℝ → ℂ) (K : ℝ → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) volume) (hG : ∀ n, AEStronglyMeasurable (G n) volume)
    (hK : Measurable K) {D E : ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hbound : ∀ᵐ c : ℝ, ∀ n, ‖F n c‖^3 ≤ D c ∧ ‖G n c‖^3 ≤ E c)
    (ht : ∀ᵐ c : ℝ, Tendsto (fun n => F n c) atTop (𝓝 (f c)) ∧ Tendsto (fun n => G n c) atTop (𝓝 (g c)))
    {s : Set ℝ} (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) {L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ c, |K c| ≤ L) (hzero : ∀ c ∉ s, K c = 0) :
    Tendsto (fun n => ∫ c : ℝ, F n c*G n c*(K c:ℂ)) atTop
      (𝓝 (∫ c : ℝ, f c*g c*(K c:ℂ))) := by
  apply tendsto_integral_of_dominated_convergence (s.indicator (fun c => (D c+E c+2)*L))
  · intro n
    exact ((hF n).mul (hG n)).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable)
  · exact IntegrableOn.integrable_indicator
      (((hD.integrableOn.add hE.integrableOn).add (integrableOn_const (C := (2:ℝ)) hμ)).mul_const L) hs
  · intro n
    filter_upwards [hbound] with c hc
    by_cases hc' : c ∈ s
    · rw [Set.indicator_of_mem hc']
      exact norm_product_kernel_le (F n) (G n) K hL (hc n).1 (hc n).2 (hk c)
    · simp only [hzero c hc',Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem hc',le_refl]
  · filter_upwards [ht] with c hc
    exact (hc.1.mul hc.2).mul tendsto_const_nhds
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

def density (σ t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t ^ 2 / (2 * σ))

def weight (h u p σ : ℝ) : ℝ := h * density σ (u - p)
def score (u p σ : ℝ) : ℝ := (u - p) / σ

theorem density_pos {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 < density σ t := by
  unfold density
  positivity

theorem density_nonneg {σ : ℝ} (_hσ : 0 ≤ σ) (t : ℝ) : 0 ≤ density σ t := by
  unfold density
  positivity

theorem density_eq_gaussianPDFReal {σ : ℝ} (hσ : 0 ≤ σ) :
    density σ = ProbabilityTheory.gaussianPDFReal 0 ⟨σ, hσ⟩ := by
  ext t
  change (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t^2 / (2*σ)) =
    (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-(t-0)^2 / (2*σ))
  rw [sub_zero]

theorem density_integrable {σ : ℝ} (hσ : 0 ≤ σ) : Integrable (density σ) := by
  rw [density_eq_gaussianPDFReal hσ]
  exact ProbabilityTheory.integrable_gaussianPDFReal 0 _

theorem weight_hasDerivAt_center (h u p σ : ℝ) (_hσ : 0 < σ) :
    HasDerivAt (fun q => weight h u q σ) (score u p σ * weight h u p σ) p := by
  have hexp : HasDerivAt (fun q : ℝ => -(u - q)^2 / (2 * σ)) ((u - p) / σ) p := by
    convert! ((((hasDerivAt_const p u).sub (hasDerivAt_id p)).pow 2).neg.div_const
      (2 * σ)) using 1
    dsimp
    ring
  have ht := ((Real.hasDerivAt_exp _).comp p hexp).const_mul
    (h * (Real.sqrt (2 * Real.pi * σ))⁻¹)
  convert! ht using 1
  · ext q
    simp only [weight, density, Function.comp_apply]
    ring
  · simp only [score, weight, density]
    ring

theorem score_hasDerivAt_center (u p σ : ℝ) :
    HasDerivAt (fun q => score u q σ) (-σ⁻¹) p := by
  convert! ((hasDerivAt_const p u).sub (hasDerivAt_id p)).div_const σ using 1
  simp [div_eq_mul_inv]

theorem weight_score_hasDerivAt_center (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun q => score u q σ * weight h u q σ)
      ((score u p σ ^ 2 - σ⁻¹) * weight h u p σ) p := by
  convert! (score_hasDerivAt_center u p σ).mul (weight_hasDerivAt_center h u p σ hσ) using 1
  ring

theorem density_normalization_hasDerivAt (σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => (Real.sqrt (2 * Real.pi * s))⁻¹)
      (-((Real.sqrt (2 * Real.pi * σ))⁻¹) / (2 * σ)) σ := by
  have hpos : 0 < 2 * Real.pi * σ := by positivity
  have hspos : 0 < Real.sqrt (2 * Real.pi * σ) := Real.sqrt_pos.2 hpos
  have ht := ((Real.hasDerivAt_sqrt hpos.ne').comp σ
    ((hasDerivAt_id σ).const_mul (2 * Real.pi))).inv hspos.ne'
  convert! ht using 1
  dsimp
  field_simp
  nlinarith [Real.sq_sqrt hpos.le]

theorem weight_hasDerivAt_variance (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => weight h u p s)
      ((1 / 2 : ℝ) * (score u p σ ^ 2 - σ⁻¹) * weight h u p σ) σ := by
  have hexp : HasDerivAt (fun s : ℝ => -(u-p)^2 / (2*s))
      ((u-p)^2 / (2*σ^2)) σ := by
    convert! (hasDerivAt_const σ (-(u-p)^2)).div
      ((hasDerivAt_id σ).const_mul 2) (by positivity : 2*σ ≠ 0) using 1
    dsimp
    ring
  have ht := ((density_normalization_hasDerivAt σ hσ).mul
    ((Real.hasDerivAt_exp _).comp σ hexp)).const_mul h
  convert! ht using 1
  unfold score weight density
  dsimp
  field_simp
  ring

end TriangularHilbert.Heat
end
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

lemma continuous_density (σ : ℝ) : Continuous (density σ) := by
  unfold density
  fun_prop

lemma integral_density {σ : ℝ} (hσ : 0 < σ) : (∫ t, density σ t) = 1 := by
  rw [density_eq_gaussianPDFReal hσ.le]
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  intro he
  have he' : σ = 0 := congrArg (fun r : NNReal => (r : ℝ)) he
  exact hσ.ne' he'

def meshMassConstant : ℝ := 2 * Real.exp (1/2)

lemma meshMassConstant_pos : 0 < meshMassConstant := by unfold meshMassConstant; positivity

lemma density_cell_le {σ a b : ℝ} (hσ : 0 < σ) (hab : (b-a)^2 ≤ σ) :
    density σ a ≤ meshMassConstant * density (2*σ) b := by
  have hA : 0 < 2*Real.pi*σ := by positivity
  have hB : 0 < 2*Real.pi*(2*σ) := by positivity
  have hsa := Real.sqrt_pos.mpr hA
  have hsb := Real.sqrt_pos.mpr hB
  have hn : Real.sqrt (2*Real.pi*(2*σ)) ≤ 2*Real.sqrt (2*Real.pi*σ) := by
    nlinarith [Real.sq_sqrt hA.le,Real.sq_sqrt hB.le]
  have hn' : (Real.sqrt (2*Real.pi*σ))⁻¹ ≤ 2 * (Real.sqrt (2*Real.pi*(2*σ)))⁻¹ := by
    have hh : 1 / Real.sqrt (2*Real.pi*σ) ≤ 2 / Real.sqrt (2*Real.pi*(2*σ)) :=
      (div_le_div_iff₀ hsa hsb).mpr (by simpa only [one_mul] using hn)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  have hquad : b^2 ≤ 2*a^2+2*σ := by nlinarith [sq_nonneg (b-2*a)]
  have hex : -a^2/(2*σ) ≤ 1/2 + (-b^2/(2*(2*σ))) := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < 4*σ by positivity)).mp
    field_simp
    nlinarith
  unfold density
  calc
    _ ≤ (2 * (Real.sqrt (2*Real.pi*(2*σ)))⁻¹) *
        (Real.exp (1/2) * Real.exp (-b^2/(2*(2*σ)))) :=
      mul_le_mul hn' (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hex)
        (Real.exp_nonneg _) (by positivity)
    _ = _ := by unfold meshMassConstant; ring

lemma mesh_cell_le {h σ : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (c : ℝ) (i : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (i:ℝ) (i+1)) :
    density σ (c+h*i) ≤ meshMassConstant * density (2*σ) (c+h*t) := by
  have hσ0 : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  apply density_cell_le hσ0
  have hti : 0 ≤ t-i := sub_nonneg.mpr ht.1
  have hti1 : t-i ≤ 1 := by linarith [ht.2]
  have he : c+h*t-(c+h*i) = h*(t-i) := by ring
  rw [he,mul_pow]
  have hs : (t-i)^2 ≤ 1 := by nlinarith
  exact (by nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg h)] : h^2*(t-i)^2 ≤ h^2).trans hσ

lemma mesh_mass_le {h σ : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (c : ℝ) (n : ℕ) :
    (∑ i : Fin n, h*density σ (c+h*i)) ≤ meshMassConstant := by
  have hs : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  let f : ℝ → ℝ := fun t => h*density (2*σ) (c+h*t)
  have hf : Continuous f := continuous_const.mul ((continuous_density _).comp
    (continuous_const.add (continuous_const.mul continuous_id)))
  have hc (i : ℕ) : h*density σ (c+h*(i:ℝ)) ≤ meshMassConstant * ∫ t in (i:ℝ)..(i+1), f t := by
    have hi := intervalIntegral.integral_mono_on (show (i:ℝ) ≤ i+1 by linarith)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => h*density σ (c+h*i)) volume i (i+1))
      ((continuous_const.mul hf : Continuous (fun t => meshMassConstant * f t)).intervalIntegrable i (i+1))
      (fun t ht => by
        have hb := mul_le_mul_of_nonneg_left (mesh_cell_le hh hσ c i ht) hh.le
        simpa only [Pi.mul_apply,f,mul_assoc,mul_left_comm h meshMassConstant] using hb)
    simpa only [Pi.mul_apply,intervalIntegral.integral_const,add_sub_cancel_left,one_smul,intervalIntegral.integral_const_mul] using hi
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => h*density σ (c+h*i)) n]
  calc
    _ ≤ ∑ i ∈ Finset.range n, meshMassConstant * ∫ t in (i:ℝ)..(i+1), f t := Finset.sum_le_sum (fun i _ => hc i)
    _ = meshMassConstant * ∫ t in (0:ℝ)..n, f t := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.cast_zero,Nat.cast_add,Nat.cast_one] using
        (intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k:ℝ)) (n := n) (fun i _ => hf.intervalIntegrable _ _))
    _ ≤ meshMassConstant := by
      have hval : (∫ t in (0:ℝ)..n, f t) = ∫ x in c..(c+h*n), density (2*σ) x := by
        unfold f
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left (fun y => density (2*σ) (c+y)) hh.ne']
        rw [intervalIntegral.integral_comp_add_left]
        simp [smul_eq_mul,hh.ne']
      rw [hval]
      have hi : (∫ x in c..(c+h*n), density (2*σ) x) ≤ 1 := by
        rw [intervalIntegral.integral_of_le (by nlinarith [show (0:ℝ) ≤ n by positivity] : c ≤ c+h*n)]
        rw [← integral_density (show 0 < 2*σ by positivity)]
        exact setIntegral_le_integral (density_integrable (by positivity))
          (ae_of_all _ (fun x => density_nonneg (by positivity) x))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hi meshMassConstant_pos.le
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_neg (σ x : ℝ) : density σ (-x) = density σ x := by
  simp [density]

lemma density_le_zero (σ x : ℝ) : density σ x ≤ density σ 0 := by
  by_cases hs : 0 < σ
  · unfold density
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    simp only [zero_pow (by decide : 2 ≠ 0),neg_zero,zero_div]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by positivity)
  · have he : Real.sqrt (2*Real.pi*σ) = 0 := Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hs))
    simp [density,he]

lemma density_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b p : ℝ) :
    density s (a-p)*density t (b-p) =
      density (s+t) (a-b)*density (s*t/(s+t)) (p-(t*a+s*b)/(s+t)) := by
  have hst : s+t ≠ 0 := (add_pos hs ht).ne'
  have hn : Real.sqrt (2*Real.pi*s)*Real.sqrt (2*Real.pi*t) =
      Real.sqrt (2*Real.pi*(s+t))*Real.sqrt (2*Real.pi*(s*t/(s+t))) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*s),← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*(s+t))]
    congr 1
    field_simp
  have he : -(a-p)^2/(2*s) + -(b-p)^2/(2*t) =
      -(a-b)^2/(2*(s+t)) + -(p-(t*a+s*b)/(s+t))^2/(2*(s*t/(s+t))) := by
    field_simp
    ring
  unfold density
  calc
    _ = (Real.sqrt (2*Real.pi*s)*Real.sqrt (2*Real.pi*t))⁻¹ *
        Real.exp (-(a-p)^2/(2*s) + -(b-p)^2/(2*t)) := by rw [mul_inv,Real.exp_add]; ring
    _ = _ := by rw [hn,he,mul_inv,Real.exp_add]; ring

lemma integral_density_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    (∫ p, density s (a-p)*density t (b-p)) = density (s+t) (a-b) := by
  simp_rw [density_product hs ht]
  rw [integral_const_mul,integral_sub_right_eq_self,integral_density (by positivity),mul_one]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open scoped NNReal
noncomputable section

lemma integrable_pow_density {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Integrable (fun x : ℝ => x^n*density s x) := by
  have hi : Integrable (fun x : ℝ => x^n*Real.exp (-(1/(2*s))*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 1/(2*s)) (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith : -1 < (n:ℝ)))
  convert hi.mul_const (Real.sqrt (2*Real.pi*s))⁻¹ using 1
  funext x
  unfold density
  rw [show -(1/(2*s))*x^2 = -x^2/(2*s) by ring]
  ring

lemma integral_density_first (s : ℝ) : (∫ x : ℝ, x*density s x) = 0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x*density s x) volume
  simp only [density_neg,neg_mul,integral_neg] at he
  linarith

lemma integral_density_third (s : ℝ) : (∫ x : ℝ, x^3*density s x) = 0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x^3*density s x) volume
  simp only [density_neg,neg_pow,show (-1:ℝ)^3 = -1 by norm_num,neg_mul,one_mul,integral_neg] at he
  linarith

lemma integral_density_second {s : ℝ} (hs : 0 < s) : (∫ x : ℝ, x^2*density s x) = s := by
  let v : ℝ≥0 := ⟨s,hs.le⟩
  have hv : v ≠ 0 := by
    intro he
    have h := congrArg (fun q : ℝ≥0 => (q:ℝ)) he
    exact hs.ne' h
  have hh := ProbabilityTheory.variance_fun_id_gaussianReal (μ:=0) (v:=v)
  rw [ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hh
  simp only [ProbabilityTheory.integral_id_gaussianReal,sub_zero] at hh
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at hh
  change (∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 v x * (x^2)) = s at hh
  change (∫ x : ℝ, x^2*density s x) = s
  convert hh using 1
  congr 1
  funext x
  change x^2*((Real.sqrt (2*Real.pi*s))⁻¹*Real.exp (-x^2/(2*s))) =
    ((Real.sqrt (2*Real.pi*s))⁻¹*Real.exp (-((x-0)^2)/(2*s)))*x^2
  simp only [sub_zero]
  ring

def cubic (c0 c1 c2 c3 x : ℝ) : ℝ := c0+c1*x+c2*x^2+c3*x^3

lemma integral_cubic_density {s : ℝ} (hs : 0 < s) (c0 c1 c2 c3 : ℝ) :
    (∫ x : ℝ, cubic c0 c1 c2 c3 x*density s x) = c0+c2*s := by
  have h0 := (density_integrable hs.le).const_mul c0
  have h1 : Integrable (fun x : ℝ => c1*(x*density s x)) := by simpa only [pow_one] using (integrable_pow_density hs 1).const_mul c1
  have h2 := (integrable_pow_density hs 2).const_mul c2
  have h3 := (integrable_pow_density hs 3).const_mul c3
  have he (x : ℝ) : cubic c0 c1 c2 c3 x*density s x =
      (c0*density s x+c1*(x*density s x))+c2*(x^2*density s x)+c3*(x^3*density s x) := by unfold cubic; ring
  simp_rw [he]
  have e3 := integral_add ((h0.add h1).add h2) h3
  have e2 := integral_add (h0.add h1) h2
  have e1 := integral_add h0 h1
  dsimp only [Pi.add_apply] at e1 e2 e3
  rw [e3,e2,e1]
  simp only [integral_const_mul,integral_density hs,integral_density_first,integral_density_second hs,integral_density_third,mul_one,mul_zero,add_zero]

lemma integral_shifted_cubic_density {s : ℝ} (hs : 0 < s) (c0 c1 c2 c3 m : ℝ) :
    (∫ x : ℝ, cubic c0 c1 c2 c3 (x-m)*density s (x-m)) = c0+c2*s := by
  rw [integral_sub_right_eq_self (fun x : ℝ => cubic c0 c1 c2 c3 x*density s x),integral_cubic_density hs]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def oddWindow (s t : ℝ) : ℝ := t / Real.sqrt s * density s t

def windowRatio (s t : ℝ) : ℝ := oddWindow s t / density ((11/10)*s) t

lemma density_dilation {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (t : ℝ) :
    density (q*s) t = (Real.sqrt s)⁻¹ * density q (t/Real.sqrt s) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  have he : -(t/Real.sqrt s)^2/(2*q) = -t^2/(2*(q*s)) := by
    field_simp
    nlinarith [hsq]
  unfold density
  rw [show 2*Real.pi*(q*s)=s*(2*Real.pi*q) by ring,Real.sqrt_mul hs.le,he]
  simp only [mul_inv_rev]
  ring

lemma density_one_lambda (z : ℝ) :
    density 1 z = Real.sqrt (11/10) * Real.exp (-z^2/22) * density (11/10) z := by
  have hr : Real.sqrt (11/10) ≠ 0 := by positivity
  have hp : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have hn : 2*Real.pi*(11/10) = (11/10)*(2*Real.pi) := by ring
  unfold density
  rw [hn,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 11/10)]
  simp only [mul_one,mul_inv_rev]
  have he : -z^2/22 + -z^2/(2*(11/10)) = -z^2/(2*1) := by ring
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-z^2/22 + -z^2/(2*(11/10))) := by rw [he]; simp
    _ = _ := by rw [Real.exp_add]; field_simp

lemma density_lambda_relation {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density s t = Real.sqrt (11/10) * Real.exp (-(t/Real.sqrt s)^2/22) * density ((11/10)*s) t := by
  have h1 := density_dilation hs (by norm_num : (0:ℝ)<1) t
  rw [one_mul] at h1
  rw [h1,density_dilation hs (by norm_num : (0:ℝ)<11/10),density_one_lambda]
  ring

lemma density_le_lambda {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density s t ≤ Real.sqrt (11/10)*density ((11/10)*s) t := by
  rw [density_lambda_relation hs t]
  have he : Real.exp (-(t/Real.sqrt s)^2/22) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)) (density_nonneg (by positivity) t)

lemma windowRatio_eq {s : ℝ} (hs : 0 < s) (t : ℝ) :
    windowRatio s t = Real.sqrt (11/10)*(t/Real.sqrt s)*Real.exp (-(t/Real.sqrt s)^2/22) := by
  unfold windowRatio oddWindow
  rw [density_lambda_relation hs t]
  have hn : density ((11/10)*s) t ≠ 0 := (density_pos (by positivity) t).ne'
  rw [← mul_assoc, mul_div_cancel_right₀ _ hn]
  ring

lemma abs_mul_exp_square_le (z : ℝ) : |z| *Real.exp (-z^2/22) ≤ 22 := by
  have h := Real.add_one_le_exp (z^2/22)
  have hp := Real.exp_pos (-z^2/22)
  have ha : |z| ≤ 22*(z^2/22+1) := by nlinarith [sq_nonneg (|z|-1),sq_abs z]
  have he : Real.exp (z^2/22) * Real.exp (-z^2/22) = 1 := by rw [← Real.exp_add,show z^2/22 + -z^2/22 = 0 by ring,Real.exp_zero]
  have hb := mul_le_mul_of_nonneg_right h hp.le
  rw [he] at hb
  have hc := mul_le_mul_of_nonneg_right ha hp.le
  nlinarith

lemma abs_windowRatio_le {s : ℝ} (hs : 0 < s) (t : ℝ) : |windowRatio s t| ≤ 44 := by
  rw [windowRatio_eq hs t,abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos (Real.exp_pos _)]
  have h := abs_mul_exp_square_le (t/Real.sqrt s)
  have hr : Real.sqrt (11/10) ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have hn := Real.sqrt_nonneg (11/10)
  nlinarith

lemma oddWindow_score {s : ℝ} (hs : 0 < s) (u p : ℝ) :
    oddWindow s (u-p) = Real.sqrt s*score u p s*density s (u-p) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  unfold oddWindow score
  congr 1
  field_simp
  rw [hsq]

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

theorem cyclic_sum_insert {ι : Type uι} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (f : ι → ι → ι → ℂ)
    (hf : ∀ i j k, f i j k = f j k i) :
    (∑ i ∈ insert a s, ∑ j ∈ insert a s, ∑ k ∈ insert a s, f i j k) =
      f a a a + 3 * (∑ j ∈ s, f a a j) +
        3 * (∑ j ∈ s, ∑ k ∈ s, f a j k) +
        (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k) := by
  simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
  have h1 : (∑ i ∈ s, f a i a) = ∑ i ∈ s, f a a i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hf a i a).trans (hf i a a)
  have h2 : (∑ i ∈ s, f i a a) = ∑ i ∈ s, f a a i := by
    apply Finset.sum_congr rfl
    intro i _
    exact hf i a a
  have h3 : (∑ i ∈ s, ∑ j ∈ s, f i a j) = ∑ i ∈ s, ∑ j ∈ s, f a i j := by
    simp_rw [hf _ a _]
    exact Finset.sum_comm
  have h4 : (∑ i ∈ s, ∑ j ∈ s, f i j a) = ∑ i ∈ s, ∑ j ∈ s, f a i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hf i j a).trans (hf j a i)
  rw [h1, h2, h3, h4]
  ring

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

theorem norm_quad_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (x : ι → ℂ) :
    ‖∑ j, ∑ k, star (x j) * D j k * x k‖ ≤
      ‖D‖ * ∑ j, ‖x j‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  have hform : (∑ j, ∑ k, star (x j) * D j k * x k) =
      ⟪v, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D v⟫_ℂ := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec,
      dotProduct, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, v]
  rw [hform]
  calc
    _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖D‖ * ‖v‖) := by
      gcongr
      exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D).le_opNorm v
    _ = ‖D‖ * ∑ j, ‖x j‖ ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq v]
      ring

theorem column_sq_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (i : ι) :
    (∑ j, ‖D j i‖ ^ 2) ≤ ‖D‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := EuclideanSpace.single i 1
  have hn : ‖v‖ = 1 := by simp [v]
  have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D).le_opNorm v
  rw [hn, Matrix.l2_opNorm_toEuclideanCLM, mul_one] at h
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h
  simpa [EuclideanSpace.norm_sq_eq, v, Matrix.mulVec, dotProduct] using hs

theorem row_sq_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (i : ι) :
    (∑ j, ‖D i j‖ ^ 2) ≤ ‖D‖ ^ 2 := by
  convert column_sq_sum_le D i using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← hD.apply i j, norm_star]

theorem hermitian_entry_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (i j : ι) :
    ‖D i j‖ ≤ ‖D‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖D i k‖)
    (Finset.mem_univ j)).trans (row_sq_sum_le D hD i)

theorem norm_cyclic_tail_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i‖ ≤
      ‖D‖ * ∑ j ∈ s, (m j) ^ 2 * ‖D i j‖ ^ 2 := by
  let x : ι → ℂ := fun j => if j ∈ s then (m j : ℂ) * D j i else 0
  have hf' (j k : ι) : star (x j) * D j k * x k =
      if j ∈ s then if k ∈ s then
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i else 0 else 0 := by
    by_cases hj : j ∈ s <;> by_cases hk : k ∈ s
    all_goals simp [x, hj, hk, hD.apply, mul_comm, mul_left_comm]
  have hf : (∑ j, ∑ k, star (x j) * D j k * x k) =
      ∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i := by
    simp_rw [hf']
    simp [Finset.sum_ite_mem]
  have hn' (j : ι) : ‖x j‖ ^ 2 =
      if j ∈ s then (m j) ^ 2 * ‖D i j‖ ^ 2 else 0 := by
    by_cases hj : j ∈ s
    · simp [x, hj, mul_pow, ← hD.apply i j]
    · simp [x, hj]
  have hn : (∑ j, ‖x j‖ ^ 2) = ∑ j ∈ s, (m j) ^ 2 * ‖D i j‖ ^ 2 := by
    simp_rw [hn']
    simp [Finset.sum_ite_mem]
  simpa only [hf, hn] using norm_quad_sum_le D x

theorem norm_weighted_row_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, (m j : ℂ) * D i j * D j i‖ ≤
      Real.sqrt (∑ j ∈ s, (m j)^2 * ‖D i j‖^2) * ‖D‖ := by
  have hs : (∑ j ∈ s, ‖D i j‖^2) ≤ ‖D‖^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg s.subset_univ
      (fun j _ _ => sq_nonneg ‖D i j‖)).trans (row_sq_sum_le D hD i)
  have hr : Real.sqrt (∑ j ∈ s, ‖D i j‖^2) ≤ ‖D‖ :=
    (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hs⟩
  calc
    _ ≤ ∑ j ∈ s, ‖(m j : ℂ) * D i j * D j i‖ := norm_sum_le _ _
    _ = ∑ j ∈ s, (|m j| * ‖D i j‖) * ‖D i j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [← hD.apply i j]
    _ ≤ Real.sqrt (∑ j ∈ s, (|m j| * ‖D i j‖)^2) *
        Real.sqrt (∑ j ∈ s, ‖D i j‖^2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ j ∈ s, (m j)^2 * ‖D i j‖^2) * ‖D‖ := by
      simp only [mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)

theorem norm_twice_tail_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖(m i : ℂ)^2 * D i i * (∑ j ∈ s, (m j : ℂ) * D i j * D j i)‖ ≤
      ‖D‖ / 2 * (|m i|^3 * ‖D i i‖^2 +
        |m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  let B := ∑ j ∈ s, (m j)^2 * ‖D i j‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hYoung : |m i|^2 * ‖D i i‖ * Real.sqrt B ≤
      (|m i|^3 * ‖D i i‖^2 + |m i| * B) / 2 := by
    have hsq := mul_nonneg (abs_nonneg (m i))
      (sq_nonneg (|m i| * ‖D i i‖ - Real.sqrt B))
    have hr := congrArg (fun z : ℝ => |m i| * z) (Real.sq_sqrt hB)
    nlinarith
  calc
    _ = |m i|^2 * ‖D i i‖ * ‖∑ j ∈ s, (m j : ℂ) * D i j * D j i‖ := by
      simp [norm_pow]
    _ ≤ |m i|^2 * ‖D i i‖ * (Real.sqrt B * ‖D‖) :=
      mul_le_mul_of_nonneg_left (norm_weighted_row_le D hD m i s) (by positivity)
    _ = ‖D‖ * (|m i|^2 * ‖D i i‖ * Real.sqrt B) := by ring
    _ ≤ ‖D‖ * ((|m i|^3 * ‖D i i‖^2 + |m i| * B) / 2) :=
      mul_le_mul_of_nonneg_left hYoung (norm_nonneg _)
    _ = _ := by dsimp [B]; ring

def spectralWeight {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j : ι) : ℝ :=
  |m i|^2 * |m j|^2 / (|m i| + |m j|) * ‖D i j‖^2

theorem spectralWeight_symm {ι : Type uι} (D : Matrix ι ι ℂ)
    (hD : D.IsHermitian) (m : ι → ℝ) (i j : ι) :
    spectralWeight D m i j = spectralWeight D m j i := by
  unfold spectralWeight
  rw [← hD.apply i j, norm_star]
  ring

theorem spectralWeight_diag {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i : ι) :
    spectralWeight D m i i = |m i|^3 * ‖D i i‖^2 / 2 := by
  unfold spectralWeight
  by_cases h : m i = 0
  · simp [h]
  · have h' : |m i| ≠ 0 := abs_ne_zero.mpr h
    field_simp
    ring

theorem spectralWeight_pair_ge {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ)
    (i j : ι) (hij : |m j| ≤ |m i|) :
    |m i| * (m j)^2 * ‖D i j‖^2 ≤ 2 * spectralWeight D m i j := by
  unfold spectralWeight
  by_cases hi : m i = 0
  · simp [hi]
  · have hp : 0 < |m i| + |m j| := add_pos_of_pos_of_nonneg (abs_pos.mpr hi) (abs_nonneg _)
    have hbase : |m i| * |m j|^2 ≤ 2 * (|m i|^2 * |m j|^2 / (|m i| + |m j|)) := by
      rw [← mul_div_assoc, le_div_iff₀ hp]
      have hmul := mul_nonneg (mul_nonneg (abs_nonneg (m i)) (sq_nonneg |m j|))
        (sub_nonneg.mpr hij)
      nlinarith
    simpa only [sq_abs, mul_assoc] using mul_le_mul_of_nonneg_right hbase (sq_nonneg ‖D i j‖)

def cubicTerm {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j k : ι) : ℂ :=
  (m i : ℂ) * (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i

theorem cubicTerm_cyclic {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j k : ι) :
    cubicTerm D m i j k = cubicTerm D m j k i := by unfold cubicTerm; ring

theorem norm_cubicTerm_diag_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) :
    ‖cubicTerm D m i i i‖ ≤ ‖D‖ * (|m i|^3 * ‖D i i‖^2) := by
  calc
    _ = (|m i|^3 * ‖D i i‖^2) * ‖D i i‖ := by
      simp only [cubicTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ (|m i|^3 * ‖D i i‖^2) * ‖D‖ := by
      gcongr
      exact hermitian_entry_le D hD i i
    _ = _ := by ring

theorem norm_cubicTerm_twice_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, cubicTerm D m i i j‖ ≤
      ‖D‖ / 2 * (|m i|^3 * ‖D i i‖^2 +
        |m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  convert norm_twice_tail_le D hD m i s using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold cubicTerm
  ring

theorem norm_cubicTerm_once_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ ≤
      ‖D‖ * (|m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  have heq : (∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k) =
      (m i : ℂ) * (∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    unfold cubicTerm
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |m i| * (‖D‖ * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) :=
      mul_le_mul_of_nonneg_left (norm_cyclic_tail_le D hD m i s) (abs_nonneg _)
    _ = _ := by ring

theorem spectralWeight_insert_ge {ι : Type uι} [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (s : Finset ι) (a : ι) (ha : a ∉ s) (hmax : ∀ j ∈ s, |m j| ≤ |m a|) :
    |m a|^3 * ‖D a a‖^2 / 2 +
      |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2 +
      (∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j) ≤
      ∑ i ∈ insert a s, ∑ j ∈ insert a s, spectralWeight D m i j := by
  have hrs : (∑ j ∈ s, spectralWeight D m j a) =
      ∑ j ∈ s, spectralWeight D m a j := by
    apply Finset.sum_congr rfl
    intro j _
    exact spectralWeight_symm D hD m j a
  have hp : |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2 ≤
      2 * ∑ j ∈ s, spectralWeight D m a j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_assoc] using spectralWeight_pair_ge D m a j (hmax j hj)
  simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
  rw [hrs, spectralWeight_diag]
  linarith

theorem norm_cubic_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (s : Finset ι) :
    ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ ≤
      5 * ‖D‖ * ∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j := by
  induction s using Finset.induction_on_max_value (fun i => |m i|) with
  | empty => simp
  | insert a s ha hmax ih =>
    rw [cyclic_sum_insert s a ha _ (cubicTerm_cyclic D m)]
    let A := |m a|^3 * ‖D a a‖^2
    let E := |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2
    let Q := ∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hdiag := norm_cubicTerm_diag_le D hD m a
    have htwice := norm_cubicTerm_twice_le D hD m a s
    have honce := norm_cubicTerm_once_le D hD m a s
    calc
      _ ≤ ‖cubicTerm D m a a a + 3 * ∑ j ∈ s, cubicTerm D m a a j +
          3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ +
          ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ := norm_add_le _ _
      _ ≤ (‖cubicTerm D m a a a‖ + 3 * ‖∑ j ∈ s, cubicTerm D m a a j‖ +
          3 * ‖∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖) +
          ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ := by
        gcongr
        calc
          _ ≤ ‖cubicTerm D m a a a + 3 * ∑ j ∈ s, cubicTerm D m a a j‖ +
              ‖3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ := norm_add_le _ _
          _ ≤ (‖cubicTerm D m a a a‖ + ‖3 * ∑ j ∈ s, cubicTerm D m a a j‖) +
              ‖3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ := by
            gcongr
            exact norm_add_le _ _
          _ = _ := by simp
      _ ≤ (‖D‖ * A + 3 * (‖D‖ / 2 * (A + E)) + 3 * (‖D‖ * E)) +
          5 * ‖D‖ * Q := by
        exact add_le_add (add_le_add (add_le_add hdiag
          (mul_le_mul_of_nonneg_left htwice (by norm_num)))
          (mul_le_mul_of_nonneg_left honce (by norm_num))) ih
      _ ≤ 5 * ‖D‖ * (A / 2 + E + Q) := by
        nlinarith [mul_nonneg (norm_nonneg D) hE]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (spectralWeight_insert_ge D hD m s a ha hmax) (by positivity)

theorem trace_cube_mul_diagonal {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (m : ι → ℝ) :
    Matrix.trace ((D * Matrix.diagonal (fun i => (m i : ℂ)))^3) =
      ∑ i, ∑ j, ∑ k, cubicTerm D m i j k := by
  have expand (A : Matrix ι ι ℂ) :
      Matrix.trace (A^3) = ∑ i, ∑ j, ∑ k, A i j * (A j k * A k i) := by
    have hp : A^3 = A * (A * A) := by noncomm_ring
    rw [hp]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  rw [expand]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  unfold cubicTerm
  ring

theorem norm_trace_cube_mul_diagonal_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) :
    ‖Matrix.trace ((D * Matrix.diagonal (fun i => (m i : ℂ)))^3)‖ ≤
      5 * ‖D‖ * ∑ i, ∑ j, spectralWeight D m i j := by
  rw [trace_cube_mul_diagonal]
  exact norm_cubic_sum_le D hD m Finset.univ

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

def traceReal (A : Matrix ι ι ℂ) : ℝ := A.trace.re

@[simp] theorem traceReal_add (A B : Matrix ι ι ℂ) :
    traceReal (A + B) = traceReal A + traceReal B := by simp [traceReal]
@[simp] theorem traceReal_sub (A B : Matrix ι ι ℂ) :
    traceReal (A - B) = traceReal A - traceReal B := by simp [traceReal]
@[simp] theorem traceReal_smul (c : ℝ) (A : Matrix ι ι ℂ) :
    traceReal (c • A) = c * traceReal A := by simp [traceReal]
@[simp] theorem traceReal_zero : traceReal (0 : Matrix ι ι ℂ) = 0 := by simp [traceReal]
@[simp] theorem traceReal_star (A : Matrix ι ι ℂ) : traceReal Aᴴ = traceReal A := by
  simp [traceReal]
theorem traceReal_mul_comm (A B : Matrix ι ι ℂ) : traceReal (A * B) = traceReal (B * A) := by
  unfold traceReal; rw [Matrix.trace_mul_comm]
theorem traceReal_mul_cycle (A B C : Matrix ι ι ℂ) :
    traceReal (A * B * C) = traceReal (C * A * B) := by
  unfold traceReal; rw [Matrix.trace_mul_cycle]
theorem traceReal_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ traceReal A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

def hsReal (X Y : Matrix ι ι ℂ) : ℝ := traceReal (Xᴴ * Y)

@[simp] theorem hsReal_add_left (X Y Z : Matrix ι ι ℂ) :
    hsReal (X + Y) Z = hsReal X Z + hsReal Y Z := by
  simp [hsReal, add_mul]
@[simp] theorem hsReal_add_right (X Y Z : Matrix ι ι ℂ) :
    hsReal X (Y + Z) = hsReal X Y + hsReal X Z := by
  simp [hsReal, mul_add]
@[simp] theorem hsReal_sub_left (X Y Z : Matrix ι ι ℂ) :
    hsReal (X - Y) Z = hsReal X Z - hsReal Y Z := by
  simp [hsReal, sub_mul]
@[simp] theorem hsReal_sub_right (X Y Z : Matrix ι ι ℂ) :
    hsReal X (Y - Z) = hsReal X Y - hsReal X Z := by
  simp [hsReal, mul_sub]
@[simp] theorem hsReal_smul_left (c : ℝ) (X Y : Matrix ι ι ℂ) :
    hsReal (c • X) Y = c * hsReal X Y := by
  simp [hsReal, Matrix.smul_mul]
@[simp] theorem hsReal_smul_right (c : ℝ) (X Y : Matrix ι ι ℂ) :
    hsReal X (c • Y) = c * hsReal X Y := by
  simp [hsReal, Matrix.mul_smul]
@[simp] theorem hsReal_zero_right (X : Matrix ι ι ℂ) : hsReal X 0 = 0 := by simp [hsReal]

theorem hsReal_symm (X Y : Matrix ι ι ℂ) : hsReal X Y = hsReal Y X := by
  unfold hsReal
  rw [← traceReal_star (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

def sylv (A X : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * X + X * A

@[simp] theorem sylv_add_right (A X Y : Matrix ι ι ℂ) :
    sylv A (X + Y) = sylv A X + sylv A Y := by unfold sylv; noncomm_ring
@[simp] theorem sylv_sub_right (A X Y : Matrix ι ι ℂ) :
    sylv A (X - Y) = sylv A X - sylv A Y := by unfold sylv; noncomm_ring
@[simp] theorem sylv_smul_right (c : ℝ) (A X : Matrix ι ι ℂ) :
    sylv A (c • X) = c • sylv A X := by simp [sylv, smul_add]
@[simp] theorem sylv_smul_left (c : ℝ) (A X : Matrix ι ι ℂ) :
    sylv (c • A) X = c • sylv A X := by simp [sylv, smul_add]
@[simp] theorem sylv_sub_left (A B X : Matrix ι ι ℂ) :
    sylv (A - B) X = sylv A X - sylv B X := by unfold sylv; noncomm_ring
@[simp] theorem sylv_zero_right (A : Matrix ι ι ℂ) : sylv A 0 = 0 := by simp [sylv]

theorem hsReal_sylv_symm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) : hsReal X (sylv A Y) = hsReal (sylv A X) Y := by
  simp only [hsReal, sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, mul_add, add_mul, traceReal_add]
  rw [← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A,
    traceReal_mul_cycle Xᴴ Y A]

def penalty (A X : Matrix ι ι ℂ) : ℝ := hsReal X (sylv A X)

theorem penalty_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (X : Matrix ι ι ℂ) : 0 ≤ penalty A X := by
  simp only [penalty, hsReal, sylv, mul_add, traceReal_add]
  have h₁ := traceReal_nonneg (hA.conjTranspose_mul_mul_same X)
  have h₂ := traceReal_nonneg (hA.mul_mul_conjTranspose_same X)
  rw [Matrix.mul_assoc] at h₁
  rw [← Matrix.mul_assoc Xᴴ X A, traceReal_mul_cycle Xᴴ X A,
    traceReal_mul_cycle A Xᴴ X]
  exact add_nonneg h₁ h₂

theorem penalty_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    penalty A (X - Y) = penalty A X + penalty A Y - 2 * hsReal (sylv A Y) X := by
  simp only [penalty, sylv_sub_right, hsReal_sub_left, hsReal_sub_right]
  rw [hsReal_symm Y (sylv A X), ← hsReal_sylv_symm hA, hsReal_symm X (sylv A Y)]
  ring

theorem penalty_mono {A B : Matrix ι ι ℂ} (hAB : A ≤ B) (X : Matrix ι ι ℂ) :
    penalty A X ≤ penalty B X := by
  have h := penalty_nonneg hAB X
  simpa only [penalty, sylv_sub_left, hsReal_sub_right, sub_nonneg] using h

def variation (A K X : Matrix ι ι ℂ) : ℝ := 2 * hsReal K X - penalty A X

def rootCost (A K : Matrix ι ι ℂ) : ℝ := (3 / 2 : ℝ) * sSup (Set.range (variation A K))

theorem variation_sylv {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    variation A (sylv A Y) X = penalty A Y - penalty A (X - Y) := by
  rw [variation, penalty_sub hA]
  ring

theorem rootCost_eq_of_solution {A K Y : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hY : sylv A Y = K) : rootCost A K = (3 / 2 : ℝ) * hsReal K Y := by
  subst K
  have heq : sSup (Set.range (variation A (sylv A Y))) = penalty A Y := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)
    · rintro _ ⟨X, rfl⟩
      rw [variation_sylv hA.isHermitian]
      exact sub_le_self _ (penalty_nonneg hA (X - Y))
    · intro w hw
      refine ⟨variation A (sylv A Y) Y, ⟨Y, rfl⟩, ?_⟩
      simpa [variation_sylv hA.isHermitian, penalty] using hw
  rw [rootCost, heq]
  congr 1
  exact hsReal_symm _ _

theorem variation_bddAbove {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) : BddAbove (Set.range (variation A K)) := by
  obtain ⟨Y, rfl⟩ := hsol
  refine ⟨penalty A Y, ?_⟩
  rintro _ ⟨X, rfl⟩
  rw [variation_sylv hA.isHermitian]
  exact sub_le_self _ (penalty_nonneg hA _)

theorem variation_le_rootCost {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) (X : Matrix ι ι ℂ) :
    (3 / 2 : ℝ) * variation A K X ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩

theorem rootCost_nonneg {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) : 0 ≤ rootCost A K := by
  simpa [variation, penalty] using variation_le_rootCost hA hsol 0

theorem rootCost_antitone {A B K : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    rootCost B K ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans
    (le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩)

theorem rootCost_scale {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) {c : ℝ} (hc : 0 < c) :
    rootCost (c • A) K = c⁻¹ * rootCost A K := by
  obtain ⟨Y, hY⟩ := hsol
  have hY' : sylv (c • A) (c⁻¹ • Y) = K := by
    simp [sylv_smul_left, sylv_smul_right, smul_smul, ne_of_gt hc, hY]
  rw [rootCost_eq_of_solution (hA.smul (le_of_lt hc)) hY',
    rootCost_eq_of_solution hA hY, hsReal_smul_right]
  ring

theorem hsReal_eq_sum (X Y : Matrix ι ι ℂ) :
    hsReal X Y = ∑ i, ∑ j, (star (X i j) * Y i j).re := by
  simp only [hsReal, traceReal, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  exact Finset.sum_comm

variable [DecidableEq ι]

theorem sylv_diagonal_apply (q : ι → ℝ) (X : Matrix ι ι ℂ) (i j : ι) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) X i j =
      ((q i + q j : ℝ) : ℂ) * X i j := by
  simp only [sylv, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Complex.ofReal_add]
  ring

def diagonalSolution (q : ι → ℝ) (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => K i j / ((q i + q j : ℝ) : ℂ)

theorem diagonalSolution_solves (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hsupp : ∀ i j, q i + q j = 0 → K i j = 0) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (diagonalSolution q K) = K := by
  ext i j
  rw [sylv_diagonal_apply]
  by_cases h : q i + q j = 0
  · simp [diagonalSolution, h, hsupp i j h]
  · exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr h)

theorem rootCost_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (K : Matrix ι ι ℂ) (hsupp : ∀ i j, q i + q j = 0 → K i j = 0) :
    rootCost (Matrix.diagonal (fun i => (q i : ℂ))) K =
      (3 / 2 : ℝ) * ∑ i, ∑ j, ‖K i j‖^2 / (q i + q j) := by
  have hq' : (Matrix.diagonal (fun i => (q i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hq i))
  rw [rootCost_eq_of_solution hq' (diagonalSolution_solves q K hsupp), hsReal_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [diagonalSolution, ← mul_div_assoc, RCLike.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.div_ofReal_re, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem hsReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X Y : Matrix ι ι ℂ) :
    hsReal (conjStarAlgAut ℂ _ U X) (conjStarAlgAut ℂ _ U Y) = hsReal X Y := by
  change traceReal (star (conjStarAlgAut ℂ _ U X) * conjStarAlgAut ℂ _ U Y) = _
  rw [← map_star, ← map_mul, traceReal_unitary_conj]
  rfl

theorem sylv_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A X : Matrix ι ι ℂ) :
    sylv (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U X) =
      conjStarAlgAut ℂ _ U (sylv A X) := by simp only [sylv, map_add, map_mul]

theorem variation_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K X : Matrix ι ι ℂ) :
    variation (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K)
      (conjStarAlgAut ℂ _ U X) = variation A K X := by
  simp only [variation, penalty, sylv_unitary_conj, hsReal_unitary_conj]

theorem rootCost_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K : Matrix ι ι ℂ) :
    rootCost (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K) = rootCost A K := by
  unfold rootCost
  congr 2
  ext z
  constructor
  · rintro ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := (conjStarAlgAut ℂ _ U).surjective X
    exact ⟨Y, (variation_unitary_conj U A K Y).symm⟩
  · rintro ⟨X, rfl⟩
    exact ⟨conjStarAlgAut ℂ _ U X, variation_unitary_conj U A K X⟩

def hessianCost (P K : Matrix ι ι ℂ) : ℝ := rootCost (CFC.sqrt P) K

theorem exists_sylv_solution {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hsupp : ∀ i j, hA.eigenvalues i + hA.eigenvalues j = 0 →
      conjStarAlgAut ℂ _ (star hA.eigenvectorUnitary) K i j = 0) :
    ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let K' := conjStarAlgAut ℂ _ (star U) K
  let Y := diagonalSolution hA.eigenvalues K'
  refine ⟨conjStarAlgAut ℂ _ U Y, ?_⟩
  have hy : sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y = K' :=
    diagonalSolution_solves _ _ hsupp
  have hh := congrArg (conjStarAlgAut ℂ _ U) hy
  rw [← sylv_unitary_conj] at hh
  have ha : conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) = A :=
    hA.spectral_theorem.symm
  rw [ha] at hh
  simpa only [K', ← conjStarAlgAut_mul_apply, Unitary.mul_star_self, map_one,
    StarAlgEquiv.one_apply] using hh

theorem exists_sylv_solution_posDef {A : Matrix ι ι ℂ} (hA : A.PosDef)
    (K : Matrix ι ι ℂ) : ∃ Y, sylv A Y = K := by
  apply exists_sylv_solution hA.isHermitian
  intro i j hij
  exact False.elim ((ne_of_gt (add_pos (hA.eigenvalues_pos i)
    (hA.eigenvalues_pos j))) hij)

theorem hessianCost_antitone {P Q K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (hPQ : P ≤ Q) :
    hessianCost Q K ≤ hessianCost P K := by
  exact rootCost_antitone (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol (CFC.monotone_sqrt hPQ)

def sylvLinear (A : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun := sylv A
  map_add' := sylv_add_right A
  map_smul' c X := sylv_smul_right c A X

def sylvEquiv {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ :=
  (LinearEquiv.ofBijective (sylvLinear A)
    (let hs : Function.Surjective (sylvLinear A) := exists_sylv_solution_posDef hA
     ⟨(LinearMap.injective_iff_surjective).mpr hs, hs⟩)).toContinuousLinearEquiv

theorem hasFDerivAt_square {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => X * X) (sylvEquiv hA : _ →L[ℝ] _) A := by
  convert! (hasFDerivAt_id A (𝕜 := ℝ)).mul' (hasFDerivAt_id A (𝕜 := ℝ)) using 1

theorem contDiff_square {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun X : Matrix ι ι ℂ => X * X) := contDiff_id.mul contDiff_id

theorem sqrt_smul {P : Matrix ι ι ℂ} (hP : P.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • P) = Real.sqrt c • CFC.sqrt P := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, Real.mul_self_sqrt hc, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · exact smul_nonneg (Real.sqrt_nonneg c) (CFC.sqrt_nonneg P)

theorem sqrt_smoothWithin_posDef {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ContDiffWithinAt ℝ ∞ CFC.sqrt {Q : Matrix ι ι ℂ | 0 ≤ Q} P ∧
    HasFDerivWithinAt CFC.sqrt
      ((sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
        (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).symm : _ →L[ℝ] _)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by
  let A := CFC.sqrt P
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive)
  let f : Matrix ι ι ℂ → Matrix ι ι ℂ := fun X => X * X
  have hc : ContDiffAt ℝ ∞ f A := contDiff_square.contDiffAt
  have hd : HasFDerivAt f (sylvEquiv hA : _ →L[ℝ] _) A := hasFDerivAt_square hA
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let g := hc.localInverse hd hn
  have hstrict := hc.hasStrictFDerivAt' hd hn
  have hAP : f A = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hgC : ContDiffAt ℝ ∞ g P := hAP ▸ hc.to_localInverse hd hn
  have hgD : HasFDerivAt g ((sylvEquiv hA).symm : _ →L[ℝ] _) P :=
    hAP ▸ hstrict.to_localInverse.hasFDerivAt
  have heq : g =ᶠ[nhdsWithin P {Q : Matrix ι ι ℂ | 0 ≤ Q}] CFC.sqrt := by
    have ht := (CFC.continuousOn_sqrt P hP.posSemidef.nonneg).eventually
      hstrict.eventually_left_inverse
    filter_upwards [ht, self_mem_nhdsWithin] with Q hQ hQpos
    change g (CFC.sqrt Q * CFC.sqrt Q) = CFC.sqrt Q at hQ
    rwa [CFC.sqrt_mul_sqrt_self Q hQpos] at hQ
  refine ⟨hgC.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq.symm
    hP.posSemidef.nonneg, ?_⟩
  exact hgD.hasFDerivWithinAt.congr_of_eventuallyEq heq.symm
    (heq.symm.self_of_nhdsWithin hP.posSemidef.nonneg)

def traceRealCLM : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (show Matrix ι ι ℂ →ₗ[ℝ] ℝ from
    { toFun := traceReal
      map_add' := traceReal_add
      map_smul' := traceReal_smul }).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] theorem traceRealCLM_apply (X : Matrix ι ι ℂ) :
    traceRealCLM X = traceReal X := rfl

def energy (P : Matrix ι ι ℂ) : ℝ := traceReal (P * CFC.sqrt P)

def energyGradient (P : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (3 / 2 : ℝ) • traceRealCLM.comp ((ContinuousLinearMap.mul ℝ _) (CFC.sqrt P))

@[simp] theorem energyGradient_apply (P K : Matrix ι ι ℂ) :
    energyGradient P K = (3 / 2 : ℝ) * traceReal (CFC.sqrt P * K) := rfl

theorem traceReal_mul_sylv (A Y : Matrix ι ι ℂ) :
    traceReal (A * sylv A Y) = 2 * traceReal (A * A * Y) := by
  simp only [sylv, mul_add, traceReal_add]
  simp only [← Matrix.mul_assoc]
  rw [traceReal_mul_cycle A Y A]
  ring

theorem energy_hasFDerivWithinAt {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    HasFDerivWithinAt energy (energyGradient P)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by
  let A := CFC.sqrt P
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive)
  let e := sylvEquiv hA
  have hd := (sqrt_smoothWithin_posDef hP).2
  change HasFDerivWithinAt CFC.sqrt (e.symm : _ →L[ℝ] _) _ P at hd
  have hmul := (hasFDerivWithinAt_id (s := {Q : Matrix ι ι ℂ | 0 ≤ Q})
    P (𝕜 := ℝ)).mul' hd
  have h := traceRealCLM.hasFDerivAt.comp_hasFDerivWithinAt P hmul
  apply h.congr_fderiv
  ext K
  change traceReal (P * e.symm K + K * A) =
    (3 / 2 : ℝ) * traceReal (A * K)
  have he : sylv A (e.symm K) = K := e.apply_symm_apply K
  have hp : A * A = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have ht := traceReal_mul_sylv A (e.symm K)
  rw [he, hp] at ht
  rw [traceReal_add, traceReal_mul_comm K A]
  linarith

theorem hsReal_single (K : Matrix ι ι ℂ) (i j : ι) (z : ℂ) :
    hsReal K (Matrix.single i j z) = (star (K i j) * z).re := by
  simp [hsReal_eq_sum, Matrix.single_apply, ite_and, apply_ite]

theorem sylv_diagonal_single (q : ι → ℝ) (i j : ι) (z : ℂ) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (Matrix.single i j z) =
      Matrix.single i j (((q i + q j : ℝ) : ℂ) * z) := by
  ext a b
  rw [sylv_diagonal_apply]
  by_cases ha : i = a
  · subst a
    by_cases hb : j = b
    · subst b; simp
    · simp [hb]
  · simp [ha]

theorem sylv_solvable_diagonal_of_bddAbove (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hb : BddAbove (Set.range (variation (Matrix.diagonal (fun i => (q i : ℂ))) K))) :
    ∃ Y, sylv (Matrix.diagonal (fun i => (q i : ℂ))) Y = K := by
  refine ⟨diagonalSolution q K, diagonalSolution_solves q K ?_⟩
  intro i j hij
  by_contra hK
  obtain ⟨b, hb⟩ := hb
  let X := Matrix.single i j (K i j)
  have hzero : sylv (Matrix.diagonal (fun i => (q i : ℂ))) X = 0 := by
    simp [X, sylv_diagonal_single, hij]
  have hhs : hsReal K X = ‖K i j‖^2 := by
    rw [hsReal_single]
    simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖K i j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hK)
  let t : ℝ := b / (2 * ‖K i j‖^2) + 1
  have ht := hb (Set.mem_range_self (t • X))
  change variation _ K (t • X) ≤ b at ht
  simp only [variation, penalty, sylv_smul_right, hzero, smul_zero,
    hsReal_zero_right, sub_zero, hsReal_smul_right, hhs] at ht
  have hcalc : 2 * (t * ‖K i j‖^2) = b + 2 * ‖K i j‖^2 := by
    dsimp [t]
    field_simp [ne_of_gt hpos]
  rw [hcalc] at ht
  linarith

theorem sylv_solvable_of_bddAbove {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hb : BddAbove (Set.range (variation A K))) : ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let K' := f K
  have hAd : f A = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb' : BddAbove (Set.range (variation (f A) K')) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b, ?_⟩
    rintro _ ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := f.surjective X
    change variation (f A) (f K) (f Y) ≤ b
    exact (variation_unitary_conj (star U) A K Y) ▸ hb (Set.mem_range_self Y)
  rw [hAd] at hb'
  obtain ⟨Y, hY⟩ := sylv_solvable_diagonal_of_bddAbove _ K' hb'
  refine ⟨f.symm Y, ?_⟩
  apply f.injective
  change f (sylv A (f.symm Y)) = f K
  calc
    _ = sylv (f A) (f (f.symm Y)) := (sylv_unitary_conj (star U) A (f.symm Y)).symm
    _ = sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y := by
      rw [f.apply_symm_apply, hAd]
    _ = _ := hY

theorem sylv_solvable_mono {A B K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.IsHermitian) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    ∃ Y, sylv B Y = K := by
  apply sylv_solvable_of_bddAbove hB
  obtain ⟨b, hb⟩ := variation_bddAbove hA hsol
  refine ⟨b, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans (hb (Set.mem_range_self X))

omit [DecidableEq ι] in
theorem rootCost_smul_direction {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) (c : ℝ) :
    rootCost A (c • K) = c^2 * rootCost A K := by
  obtain ⟨Y, hY⟩ := hsol
  have hc : sylv A (c • Y) = c • K := by rw [sylv_smul_right, hY]
  rw [rootCost_eq_of_solution hA hc, rootCost_eq_of_solution hA hY,
    hsReal_smul_left, hsReal_smul_right]
  ring

omit [DecidableEq ι] in
theorem penalty_three_identity (A X Y Z : Matrix ι ι ℂ) :
    3 * (penalty A X + penalty A Y + penalty A Z) - penalty A (X + Y + Z) =
      penalty A (X - Y) + penalty A (Y - Z) + penalty A (Z - X) := by
  simp only [penalty, sylv_add_right, sylv_sub_right, hsReal_add_left,
    hsReal_add_right, hsReal_sub_left, hsReal_sub_right]
  ring

omit [DecidableEq ι] in
theorem rootCost_three_le {A K L M : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hK : ∃ X, sylv A X = K) (hL : ∃ Y, sylv A Y = L)
    (hM : ∃ Z, sylv A Z = M) :
    rootCost A (K + L + M) ≤ 3 * (rootCost A K + rootCost A L + rootCost A M) := by
  obtain ⟨X, rfl⟩ := hK
  obtain ⟨Y, rfl⟩ := hL
  obtain ⟨Z, rfl⟩ := hM
  have hall : sylv A (X + Y + Z) = sylv A X + sylv A Y + sylv A Z := by simp
  rw [rootCost_eq_of_solution hA hall, rootCost_eq_of_solution hA rfl,
    rootCost_eq_of_solution hA rfl, rootCost_eq_of_solution hA rfl]
  rw [← hall]
  have hc := penalty_three_identity A X Y Z
  have hn := add_nonneg (add_nonneg (penalty_nonneg hA (X - Y))
    (penalty_nonneg hA (Y - Z))) (penalty_nonneg hA (Z - X))
  rw [hsReal_symm (sylv A _) _, hsReal_symm (sylv A _) _,
    hsReal_symm (sylv A _) _, hsReal_symm (sylv A _) _]
  change (3 / 2 : ℝ) * penalty A (X + Y + Z) ≤
    3 * ((3 / 2 : ℝ) * penalty A X + (3 / 2 : ℝ) * penalty A Y +
      (3 / 2 : ℝ) * penalty A Z)
  linarith

omit [Fintype ι] [DecidableEq ι] in

theorem gram_diag_eq_zero_iff {κ : Type uκ} [Fintype κ]
    (R : Matrix κ ι ℂ) (j : ι) :
    (Rᴴ * R) j j = 0 ↔ ∀ i, R i j = 0 := by
  change star (fun i => R i j) ⬝ᵥ (fun i => R i j) = 0 ↔ _
  rw [dotProduct_star_self_eq_zero]
  exact funext_iff

theorem sylv_solvable_inserted_gram {κ : Type uκ} [Fintype κ]
    (R : Matrix κ ι ℂ) (D : Matrix κ κ ℂ) :
    ∃ Y, sylv (CFC.sqrt (Rᴴ * R)) Y = Rᴴ * D * R := by
  let P := Rᴴ * R
  let A := CFC.sqrt P
  have hP : P.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self R
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  let U := hA.isHermitian.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let R' := R * (U : Matrix ι ι ℂ)
  let q := hA.isHermitian.eigenvalues
  have hAd : f A = Matrix.diagonal (fun i => (q i : ℂ)) :=
    hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hAp : A * A = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hGram : R'ᴴ * R' = f P := by
    simp only [R', f, P, conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hIns : f (Rᴴ * D * R) = R'ᴴ * D * R' := by
    simp only [R', f, conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  apply exists_sylv_solution hA.isHermitian
  intro i j hij
  have hj : q j = 0 :=
    ((add_eq_zero_iff_of_nonneg (hA.eigenvalues_nonneg i)
      (hA.eigenvalues_nonneg j)).mp hij).2
  have hdiag : (R'ᴴ * R') j j = 0 := by
    rw [hGram, ← hAp, map_mul, hAd, Matrix.diagonal_mul_diagonal]
    simp [hj]
  have hcol := (gram_diag_eq_zero_iff R' j).mp hdiag
  change f (Rᴴ * D * R) i j = 0
  rw [hIns]
  simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem trace_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    Matrix.trace (conjStarAlgAut ℂ _ U X) = Matrix.trace X := by
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem norm_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    ‖conjStarAlgAut ℂ _ U X‖ = ‖X‖ := by
  rw [conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem hermitian_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (conjStarAlgAut ℂ _ U X).IsHermitian := by
  change star (conjStarAlgAut ℂ _ U X) = conjStarAlgAut ℂ _ U X
  rw [← map_star]
  exact congrArg (conjStarAlgAut ℂ _ U) hX

theorem sqrt_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    CFC.sqrt (conjStarAlgAut ℂ _ U P) = conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
        (U : Matrix ι ι ℂ)).nonneg

theorem hessianCost_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) (K : Matrix ι ι ℂ) :
    hessianCost (conjStarAlgAut ℂ _ U P) (conjStarAlgAut ℂ _ U K) =
      hessianCost P K := by
  simp only [hessianCost, sqrt_unitary_conj U hP, rootCost_unitary_conj]

theorem sqrt_diagonal_square (m : ι → ℝ) :
    CFC.sqrt (Matrix.diagonal (fun i => (m i : ℂ)) *
      Matrix.diagonal (fun i => (m i : ℂ))) =
      Matrix.diagonal (fun i => ((|m i| : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    change ((|m i| : ℝ) : ℂ) * ((|m i| : ℝ) : ℂ) = (m i : ℂ) * (m i : ℂ)
    exact_mod_cast (show |m i| * |m i| = m i * m i by nlinarith [sq_abs (m i)])
  · exact (Matrix.PosSemidef.diagonal
      (fun i => RCLike.ofReal_nonneg.mpr (abs_nonneg (m i)))).nonneg

theorem hessianCost_diagonal_square (m : ι → ℝ) (D : Matrix ι ι ℂ) :
    hessianCost (Matrix.diagonal (fun i => (m i : ℂ)) *
      Matrix.diagonal (fun i => (m i : ℂ)))
      (Matrix.diagonal (fun i => (m i : ℂ)) * D *
       Matrix.diagonal (fun i => (m i : ℂ))) =
      (3 / 2 : ℝ) * ∑ i, ∑ j, spectralWeight D m i j := by
  unfold hessianCost
  rw [sqrt_diagonal_square]
  have hs : ∀ i j, |m i| + |m j| = 0 →
      (Matrix.diagonal (fun i => (m i : ℂ)) * D *
        Matrix.diagonal (fun i => (m i : ℂ))) i j = 0 := by
    intro i j hij
    have hi : m i = 0 := abs_eq_zero.mp
      ((add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)).mp hij).1
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hi]
  rw [rootCost_diagonal _ (fun i => abs_nonneg (m i)) _ hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [spectralWeight, Matrix.mul_diagonal, Matrix.diagonal_mul,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  ring

theorem norm_trace_cube_le_hessian (M D : Matrix ι ι ℂ)
    (hM : M.IsHermitian) (hD : D.IsHermitian) :
    ‖Matrix.trace ((D * M)^3)‖ ≤
      (10 / 3 : ℝ) * ‖D‖ * hessianCost (M * M) (M * D * M) := by
  let U := star hM.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let D' := f D
  let m := hM.eigenvalues
  have hM' : f M = Matrix.diagonal (fun i => (m i : ℂ)) :=
    hM.conjStarAlgAut_star_eigenvectorUnitary
  have hd : D'.IsHermitian := hermitian_unitary_conj U hD
  have hn : ‖D'‖ = ‖D‖ := norm_unitary_conj U D
  have ht : Matrix.trace ((D' * Matrix.diagonal (fun i => (m i : ℂ)))^3) =
      Matrix.trace ((D * M)^3) := by
    rw [← hM', ← map_mul, ← map_pow]
    exact trace_unitary_conj U _
  have hp : (M * M).PosSemidef := by
    simpa only [hM.eq] using Matrix.posSemidef_conjTranspose_mul_self M
  have hc := hessianCost_unitary_conj U hp (M * D * M)
  change hessianCost (f (M * M)) (f (M * D * M)) = _ at hc
  simp only [map_mul, hM'] at hc
  rw [hessianCost_diagonal_square] at hc
  have hb := norm_trace_cube_mul_diagonal_le D' hd m
  rw [ht, hn] at hb
  rw [← hc]
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

abbrev Three := Fin 3
abbrev BlockSpace (ι : Type uι) := Three × ι
abbrev blocks (A : Matrix Three Three (Matrix ι ι ℂ)) :
    Matrix (BlockSpace ι) (BlockSpace ι) ℂ := Matrix.comp _ _ _ _ _ A

omit [DecidableEq ι] in
theorem blocks_mul (A B : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks (A * B) = blocks A * blocks B := by
  exact (Matrix.compRingEquiv Three ι ℂ).map_mul A B

omit [Fintype ι] [DecidableEq ι] in
theorem blocks_star (A : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks Aᴴ = (blocks A)ᴴ := rfl

omit [DecidableEq ι] in
theorem blocks_trace (A : Matrix Three Three (Matrix ι ι ℂ)) :
    Matrix.trace (blocks A) = ∑ v, Matrix.trace (A v v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type]

def triangleBlocks (W : Three → Matrix ι ι ℂ) : Matrix Three Three (Matrix ι ι ℂ) :=
  fun i j => if i = 0 then (if j = 0 then 0 else if j = 1 then W 0 else (W 2)ᴴ)
    else if i = 1 then (if j = 0 then (W 0)ᴴ else if j = 1 then 0 else W 1)
    else (if j = 0 then W 2 else if j = 1 then (W 1)ᴴ else 0)

def triangle (W : Three → Matrix ι ι ℂ) := blocks (triangleBlocks W)
def blockD (D : Three → Matrix ι ι ℂ) := blocks (Matrix.diagonal D)

omit [Fintype ι] [DecidableEq ι] in
theorem triangle_hermitian (W : Three → Matrix ι ι ℂ) :
    (triangle W).IsHermitian := by
  change (blocks (triangleBlocks W))ᴴ = blocks (triangleBlocks W)
  rw [← blocks_star]
  congr 1
  ext v w i j
  fin_cases v <;> fin_cases w <;> simp [triangleBlocks, Matrix.conjTranspose_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem blockD_hermitian (D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) : (blockD D).IsHermitian := by
  unfold blockD
  change (blocks (Matrix.diagonal D))ᴴ = blocks (Matrix.diagonal D)
  rw [← blocks_star, Matrix.diagonal_conjTranspose]
  have hs : star D = D := funext hD
  rw [hs]

theorem triangle_trace_cube (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    Matrix.trace ((blockD D * triangle W)^3) =
      (6 : ℂ) * (Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)).re := by
  let τ := Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)
  have hreverse :
      Matrix.trace (D 0 * (W 2)ᴴ * D 2 * (W 1)ᴴ * D 1 * (W 0)ᴴ) = star τ := by
    simp only [τ, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (hD _).eq,
      Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hrot (A B C E F G : Matrix ι ι ℂ) :
      Matrix.trace (A * B * C * E * F * G) =
        Matrix.trace (F * G * A * B * C * E) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A * B) (C * E) (F * G)
  have hf1 := hrot (D 1) (W 1) (D 2) (W 2) (D 0) (W 0)
  have hf2 := (hrot (D 2) (W 2) (D 0) (W 0) (D 1) (W 1)).trans hf1
  have hr2 := hrot (D 2) (W 1)ᴴ (D 1) (W 0)ᴴ (D 0) (W 2)ᴴ
  have hr1 := (hrot (D 1) (W 0)ᴴ (D 0) (W 2)ᴴ (D 2) (W 1)ᴴ).trans hr2
  simp only [Matrix.mul_assoc] at hf1 hf2 hr1 hr2 hreverse
  unfold blockD triangle
  rw [← blocks_mul, pow_three, ← blocks_mul, ← blocks_mul, blocks_trace]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, triangleBlocks,
    zero_mul, mul_zero, add_zero, zero_add, ite_true, ite_false, Fin.reduceEq,
    mul_add, add_mul, Matrix.trace_add, Matrix.mul_assoc]
  simp only [Matrix.trace_zero, add_zero, zero_add]
  rw [hf1, hf2, hr1, hr2, hreverse]
  simp only [← Matrix.mul_assoc]
  change τ + star τ + (star τ + τ) + (τ + star τ) = (6 : ℂ) * (τ.re : ℂ)
  apply Complex.ext <;> simp [RCLike.star_def, Complex.mul_re, Complex.mul_im]
  ring

def vertexProj (v : Three) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  Matrix.diagonal (fun a => if a.1 = v then 1 else 0)

omit [Fintype ι] in
theorem vertexProj_hermitian (v : Three) : (vertexProj (ι := ι) v).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change star (if i.1 = v then (1 : ℂ) else 0) = _
  split_ifs <;> simp

theorem vertexProj_sq (v : Three) : vertexProj (ι := ι) v * vertexProj v = vertexProj v := by
  simp only [vertexProj, Matrix.diagonal_mul_diagonal]
  congr 1
  ext a
  split_ifs <;> simp

omit [Fintype ι] in
theorem sum_vertexProj : ∑ v, vertexProj (ι := ι) v = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [vertexProj, Matrix.sum_apply]
  · simp [vertexProj, Matrix.sum_apply, hab]

theorem vertexProj_commute_blockD (v : Three) (D : Three → Matrix ι ι ℂ) :
    vertexProj v * blockD D = blockD D * vertexProj v := by
  ext a b
  simp only [vertexProj, Matrix.diagonal_mul, Matrix.mul_diagonal, blockD,
    Matrix.comp_apply, Matrix.diagonal_apply]
  by_cases hab : a.1 = b.1
  · simp [hab]
  · simp [hab]

def rowStar (W : Three → Matrix ι ι ℂ) (v : Three) := vertexProj v * triangle W

def starGram (W : Three → Matrix ι ι ℂ) (v : Three) := (rowStar W v)ᴴ * rowStar W v

def starInsert (W D : Three → Matrix ι ι ℂ) (v : Three) :=
  (rowStar W v)ᴴ * blockD D * rowStar W v

theorem starGram_eq (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v = triangle W * vertexProj v * triangle W := by
  simp only [starGram, rowStar, Matrix.conjTranspose_mul,
    (vertexProj_hermitian v).eq, (triangle_hermitian W).eq]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (triangle W), vertexProj_sq]

theorem starInsert_eq (W D : Three → Matrix ι ι ℂ) (v : Three) :
    starInsert W D v = triangle W * vertexProj v * blockD D * triangle W := by
  simp only [starInsert, rowStar, Matrix.conjTranspose_mul,
    (vertexProj_hermitian v).eq, (triangle_hermitian W).eq]
  have hp := vertexProj_commute_blockD v D
  calc
    _ = triangle W * (vertexProj v * (blockD D * vertexProj v)) * triangle W := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hp, ← Matrix.mul_assoc (vertexProj v), vertexProj_sq];
                simp only [Matrix.mul_assoc]

theorem sum_starGram (W : Three → Matrix ι ι ℂ) :
    ∑ v, starGram W v = triangle W * triangle W := by
  simp_rw [starGram_eq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_vertexProj, mul_one]

theorem sum_starInsert (W D : Three → Matrix ι ι ℂ) :
    ∑ v, starInsert W D v = triangle W * blockD D * triangle W := by
  simp_rw [starInsert_eq]
  rw [← Matrix.sum_mul, ← Matrix.sum_mul, ← Matrix.mul_sum, sum_vertexProj, mul_one]

theorem starGram_le (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v ≤ triangle W * triangle W := by
  rw [← sum_starGram]
  exact Finset.single_le_sum (fun w _ =>
    (Matrix.posSemidef_conjTranspose_mul_self (rowStar W w)).nonneg) (Finset.mem_univ v)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem hessianCost_common_three (P K : Fin 3 → Matrix ι ι ℂ)
    {Q : Matrix ι ι ℂ} (hPQ : ∀ v, P v ≤ Q)
    (hsol : ∀ v, ∃ X, sylv (CFC.sqrt (P v)) X = K v) :
    hessianCost Q (∑ v, K v) ≤ 3 * ∑ v, hessianCost (P v) (K v) := by
  have hq : (CFC.sqrt Q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hsolQ (v : Fin 3) : ∃ X, sylv (CFC.sqrt Q) X = K v :=
    sylv_solvable_mono (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P v)))
      hq.isHermitian (hsol v) (CFC.monotone_sqrt (hPQ v))
  calc
    _ ≤ 3 * ∑ v, hessianCost Q (K v) := by
      simpa only [Fin.sum_univ_three, hessianCost] using
        rootCost_three_le hq (hsolQ 0) (hsolQ 1) (hsolQ 2)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum
      (fun v _ => hessianCost_antitone (hsol v) (hPQ v))) (by norm_num)

theorem triangle_common_metric (W D : Three → Matrix ι ι ℂ) :
    hessianCost (triangle W * triangle W) (triangle W * blockD D * triangle W) ≤
      3 * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  rw [← sum_starInsert]
  exact hessianCost_common_three (starGram W) (starInsert W D)
    (starGram_le W) (fun v => sylv_solvable_inserted_gram (rowStar W v) (blockD D))

theorem triangle_real_trace_le (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    |(Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)).re| ≤
      (5 / 3 : ℝ) * ‖blockD D‖ * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  have h := norm_trace_cube_le_hessian (triangle W) (blockD D)
    (triangle_hermitian W) (blockD_hermitian D hD)
  rw [triangle_trace_cube W D hD, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs] at h
  have hm := triangle_common_metric W D
  have hc := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (10 / 3 : ℝ) * ‖blockD D‖ by positivity)
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def diagonalUnitary (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) : unitary (Matrix ι ι ℂ) :=
  ⟨Matrix.diagonal c, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    have hci (i : ι) : star (c i) * c i = 1 := by
      simpa only [RCLike.star_def, mul_comm, hc, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (c i)
    ext i j
    by_cases hij : i = j
    · subst j; simpa using hci i
    · simp [hij]⟩

theorem insertedCost_right_unitary (R L : Matrix ι ι ℂ)
    (U : unitary (Matrix ι ι ℂ)) :
    hessianCost ((R * (U : Matrix ι ι ℂ))ᴴ * (R * (U : Matrix ι ι ℂ)))
      ((R * (U : Matrix ι ι ℂ))ᴴ * L * (R * (U : Matrix ι ι ℂ))) =
      hessianCost (Rᴴ * R) (Rᴴ * L * R) := by
  simpa only [conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      hessianCost_unitary_conj (star U) (Matrix.posSemidef_conjTranspose_mul_self R)
        (Rᴴ * L * R)

def phaseEdge (z : ℂ) (W : Three → Matrix ι ι ℂ) : Three → Matrix ι ι ℂ :=
  fun v => if v = 0 then z • W 0 else W v

def rowPhase (z : ℂ) (v : Three) : BlockSpace ι → ℂ := fun a =>
  if v = 0 then (if a.1 = 1 then z else 1)
  else if v = 1 then (if a.1 = 0 then star z else 1) else 1

omit [Fintype ι] [DecidableEq ι] in
theorem rowPhase_norm (z : ℂ) (hz : ‖z‖ = 1) (v : Three) (a : BlockSpace ι) :
    ‖rowPhase z v a‖ = 1 := by
  unfold rowPhase
  split_ifs <;> simp [hz]

theorem rowStar_phase (z : ℂ) (W : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar (phaseEdge z W) v = rowStar W v * Matrix.diagonal (rowPhase z v) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases v <;> fin_cases a <;> fin_cases b
  all_goals simp [rowStar, vertexProj, triangle, Matrix.comp_apply,
    triangleBlocks, phaseEdge, rowPhase, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, smul_eq_mul, mul_comm]

theorem starCost_phase (z : ℂ) (hz : ‖z‖ = 1)
    (W D : Three → Matrix ι ι ℂ) (v : Three) :
    hessianCost (starGram (phaseEdge z W) v) (starInsert (phaseEdge z W) D v) =
      hessianCost (starGram W v) (starInsert W D v) := by
  let U := diagonalUnitary (rowPhase (ι := ι) z v) (rowPhase_norm z hz v)
  have he : rowStar (phaseEdge z W) v = rowStar W v * (U : Matrix _ _ ℂ) :=
    rowStar_phase z W v
  simp only [starGram, starInsert, he]
  exact insertedCost_right_unitary (rowStar W v) (blockD D) U

omit [Fintype ι] [DecidableEq ι] in
theorem exists_phase_norm (τ : ℂ) : ∃ z : ℂ, ‖z‖ = 1 ∧ z * τ = (‖τ‖ : ℂ) := by
  by_cases hτ : τ = 0
  · exact ⟨1, norm_one, by simp [hτ]⟩
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.mpr hτ
  have hnc : (‖τ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  refine ⟨star τ / (‖τ‖ : ℂ), ?_, ?_⟩
  · simp [hn]
  · calc
      (star τ / (‖τ‖ : ℂ)) * τ = (τ * star τ) / (‖τ‖ : ℂ) := by ring
      _ = (‖τ‖ : ℂ)^2 / (‖τ‖ : ℂ) := by rw [RCLike.star_def, Complex.mul_conj']
      _ = _ := by field_simp

theorem mixed_trace_le (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    ‖Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)‖ ≤
      (5 / 3 : ℝ) * ‖blockD D‖ * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  let τ := Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)
  obtain ⟨z, hz, he⟩ := exists_phase_norm τ
  have ht : Matrix.trace (D 0 * phaseEdge z W 0 * D 1 *
      phaseEdge z W 1 * D 2 * phaseEdge z W 2) = z * τ := by
    simp [phaseEdge, τ]
  have h := triangle_real_trace_le (phaseEdge z W) D hD
  rw [ht, he] at h
  simp only [Complex.ofReal_re, abs_of_nonneg (norm_nonneg τ)] at h
  simpa only [starCost_phase z hz] using h

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def regularize (P : Matrix ι ι ℂ) (η : ℝ) : Matrix ι ι ℂ := P + η • 1

omit [Fintype ι] in
theorem regularize_posDef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 < η) : (regularize P η).PosDef :=
  Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul hη)

omit [Fintype ι] in
theorem regularize_posSemidef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 ≤ η) : (regularize P η).PosSemidef :=
  hP.add (Matrix.PosSemidef.one.smul hη)

theorem continuous_sqrt_matrix {X : Type uX} [TopologicalSpace X]
    {P : X → Matrix ι ι ℂ} (hP : _root_.Continuous P)
    (hn : ∀ x, (P x).PosSemidef) : _root_.Continuous (fun x => CFC.sqrt (P x)) :=
  CFC.continuousOn_sqrt.comp_continuous hP (fun x => (hn x).nonneg)

theorem continuous_energyGram : _root_.Continuous
    (fun R : Matrix ι ι ℂ => energy (Rᴴ * R)) := by
  unfold energy
  exact traceRealCLM.continuous.comp
    ((continuous_star.mul continuous_id).mul
      (continuous_sqrt_matrix (continuous_star.mul continuous_id)
        Matrix.posSemidef_conjTranspose_mul_self))

theorem energy_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy (conjStarAlgAut ℂ _ U P) = energy P := by
  have hs : CFC.sqrt (conjStarAlgAut ℂ _ U P) =
      conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
    · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
          (U : Matrix ι ι ℂ)).nonneg
  simp only [energy, hs, ← map_mul, traceReal_unitary_conj]

theorem sqrt_diagonal_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    CFC.sqrt (Matrix.diagonal (fun i => (q i : ℂ))) =
      Matrix.diagonal (fun i => ((Real.sqrt (q i) : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact_mod_cast (Real.mul_self_sqrt (hq i))
  · exact (Matrix.PosSemidef.diagonal (fun i =>
      RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))).nonneg

theorem energy_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    energy (Matrix.diagonal (fun i => (q i : ℂ))) = ∑ i, q i * Real.sqrt (q i) := by
  simp [energy, sqrt_diagonal_nonneg q hq, Matrix.diagonal_mul_diagonal, traceReal]

theorem energy_spectral {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy P = ∑ i, hP.isHermitian.eigenvalues i * Real.sqrt (hP.isHermitian.eigenvalues i) := by
  rw [← energy_unitary_conj (star hP.isHermitian.eigenvectorUnitary) hP,
    hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
  exact energy_diagonal _ hP.eigenvalues_nonneg

theorem energy_eq_of_charpoly_eq {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hPQ : P.charpoly = Q.charpoly) :
    energy P = energy Q := by
  rw [energy_spectral hP, energy_spectral hQ,
    (hP.isHermitian.eigenvalues_eq_eigenvalues_iff hQ.isHermitian).mpr hPQ]

theorem energy_gram_flip (R : Matrix ι ι ℂ) : energy (Rᴴ * R) = energy (R * Rᴴ) :=
  energy_eq_of_charpoly_eq (Matrix.posSemidef_conjTranspose_mul_self R)
    (Matrix.posSemidef_self_mul_conjTranspose R) (Matrix.charpoly_mul_comm _ _)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma gradient_gram (R D A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceReal (A * (Rᴴ * D + Dᴴ * R)) = 2 * hsReal (R * A) D := by
  have he : traceReal (A * (Dᴴ * R)) = traceReal (A * (Rᴴ * D)) := by
    rw [traceReal_mul_comm, ← traceReal_star (Dᴴ * R * A)]
    simp only [Matrix.conjTranspose_mul, hA.eq, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  simp only [hsReal, Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc,
    mul_add, traceReal_add, he]
  ring

lemma energyGradient_gram (P R D : Matrix ι ι ℂ) :
    energyGradient P (Rᴴ * D + Dᴴ * R) =
      3 * hsReal (R * CFC.sqrt P) D := by
  have hs : (CFC.sqrt P).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  rw [energyGradient_apply, gradient_gram R D (CFC.sqrt P) hs]
  ring

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hsReal_nonneg_of_posSemidef {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ hsReal X Y := by
  let B := CFC.sqrt Y
  have hB : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y)).isHermitian
  have hBB : B * B = Y := CFC.sqrt_mul_sqrt_self Y hY.nonneg
  have hn := traceReal_nonneg (hX.conjTranspose_mul_mul_same B)
  rw [hB.eq, traceReal_mul_cycle, hBB, traceReal_mul_comm] at hn
  simpa only [hsReal, hX.isHermitian.eq] using hn

omit [DecidableEq ι] in
lemma sylv_star {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (Y : Matrix ι ι ℂ) :
    sylv A Yᴴ = (sylv A Y)ᴴ := by
  simp only [sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA.eq]
  exact add_comm _ _

lemma sylv_solution_isHermitian {A K Y : Matrix ι ι ℂ} (hA : A.PosDef)
    (hK : K.IsHermitian) (hY : sylv A Y = K) : Y.IsHermitian := by
  change Yᴴ = Y
  apply (sylvEquiv hA).injective
  change sylv A Yᴴ = sylv A Y
  rw [sylv_star hA.isHermitian, hY, hK.eq]

lemma posSemidef_of_sylv_posSemidef {A Y : Matrix ι ι ℂ} (hA : A.PosDef)
    (hY : Y.IsHermitian) (hS : (sylv A Y).PosSemidef) : Y.PosSemidef := by
  apply hY.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hY.eigenvalues i
  let U := hY.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  have hD : f Y = Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ)) :=
    hY.conjStarAlgAut_star_eigenvectorUnitary
  have hAf : (f A).PosDef := by
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe (U := star U))).mpr hA
  have hSf : (f (sylv A Y)).PosSemidef := by
    exact hS.mul_mul_conjTranspose_same (star U : Matrix ι ι ℂ)
  have he : f (sylv A Y) = sylv (f A) (f Y) :=
    (sylv_unitary_conj (star U) A Y).symm
  rw [he, hD] at hSf
  have hn : 0 ≤ (sylv (f A) (Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ))) i i).re :=
    (RCLike.nonneg_iff.mp hSf.diag_nonneg).1
  have hp : 0 < (f A i i).re := (RCLike.pos_iff.mp hAf.diag_pos).1
  simp only [sylv, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero] at hn
  nlinarith

lemma rootCost_le_of_order_posDef {A K : Matrix ι ι ℂ} (hA : A.PosDef)
    (hK : K.IsHermitian) (c : ℝ)
    (hm : (c • (A * A) - K).PosSemidef)
    (hp : (c • (A * A) + K).PosSemidef) :
    rootCost A K ≤ (3 / 4 : ℝ) * c^2 * traceReal (A * A * A) := by
  let Y := (sylvEquiv hA).symm K
  have hY : sylv A Y = K := (sylvEquiv hA).apply_symm_apply K
  have hYh : Y.IsHermitian := sylv_solution_isHermitian hA hK hY
  let Z : Matrix ι ι ℂ := (c / 2) • A
  have hZ : sylv A Z = c • (A * A) := by
    change A * ((c / 2) • A) + ((c / 2) • A) * A = _
    rw [Matrix.mul_smul, Matrix.smul_mul, ← add_smul]
    congr 1
    ring
  have hYZ : (Z + Y).PosSemidef := by
    apply posSemidef_of_sylv_posSemidef hA
      ((hA.isHermitian.smul (show IsSelfAdjoint (c / 2) from rfl)).add hYh)
    rwa [sylv_add_right, hZ, hY]
  have hn := hsReal_nonneg_of_posSemidef hm hYZ
  have hc : hsReal (sylv A Z) Y = hsReal K Z := by
    rw [← hsReal_sylv_symm hA.isHermitian, hY, hsReal_symm]
  have hb : hsReal K Y ≤ hsReal (sylv A Z) Z := by
    rw [← hZ, hsReal_sub_left, hsReal_add_right, hsReal_add_right, hc] at hn
    linarith
  rw [rootCost_eq_of_solution hA.posSemidef hY]
  calc
    _ ≤ (3 / 2 : ℝ) * hsReal (sylv A Z) Z := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by
      rw [hZ]
      change (3 / 2 : ℝ) * hsReal (c • (A * A)) ((c / 2) • A) = _
      rw [hsReal_smul_left, hsReal_smul_right]
      simp only [hsReal, Matrix.conjTranspose_mul, hA.isHermitian.eq]
      ring

lemma regularize_square (A : Matrix ι ι ℂ) (δ : ℝ) :
    regularize A δ * regularize A δ = A * A + (2 * δ) • A + δ^2 • 1 := by
  simp only [regularize, add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
    one_mul, mul_one, smul_smul]
  module

lemma regularize_square_le {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ) : A * A ≤ regularize A δ * regularize A δ := by
  rw [regularize_square, add_assoc]
  exact le_add_of_nonneg_right
    (((hA.smul (mul_nonneg (by norm_num) hδ)).add
      (Matrix.PosSemidef.one.smul (sq_nonneg δ))).nonneg)

omit [DecidableEq ι] in
lemma continuous_variation_left (K X : Matrix ι ι ℂ) :
    Continuous (fun A : Matrix ι ι ℂ => variation A K X) := by
  exact continuous_const.sub (traceRealCLM.continuous.comp
    (continuous_const.mul ((continuous_id.mul continuous_const).add
      (continuous_const.mul continuous_id))))

theorem rootCost_le_of_order {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hK : K.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hm : (c • (A * A) - K).PosSemidef)
    (hp : (c • (A * A) + K).PosSemidef) :
    rootCost A K ≤ (3 / 4 : ℝ) * c^2 * traceReal (A * A * A) := by
  have hb (δ : ℝ) (hδ : 0 < δ) (X : Matrix ι ι ℂ) :
      (3 / 2 : ℝ) * variation (regularize A δ) K X ≤
        (3 / 4 : ℝ) * c^2 * traceReal (regularize A δ * regularize A δ * regularize A δ) := by
    have hd := regularize_posDef hA hδ
    have ho := smul_le_smul_of_nonneg_left (regularize_square_le hA hδ.le) hc
    have hmd : (c • (regularize A δ * regularize A δ) - K).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (hm.nonneg.trans (sub_le_sub_right ho K))
    have hpd : (c • (regularize A δ * regularize A δ) + K).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (hp.nonneg.trans (add_le_add ho le_rfl))
    exact (variation_le_rootCost hd.posSemidef (exists_sylv_solution_posDef hd K) X).trans
      (rootCost_le_of_order_posDef hd hK c hmd hpd)
  have hv (X : Matrix ι ι ℂ) : variation A K X ≤ (1 / 2 : ℝ) * c^2 * traceReal (A * A * A) := by
    have hAc : Continuous (regularize A) := by unfold regularize; fun_prop
    have hf : Continuous (fun δ => (3 / 2 : ℝ) * variation (regularize A δ) K X) :=
      continuous_const.mul ((continuous_variation_left K X).comp hAc)
    have hg : Continuous (fun δ => (3 / 4 : ℝ) * c^2 *
        traceReal (regularize A δ * regularize A δ * regularize A δ)) :=
      continuous_const.mul (traceRealCLM.continuous.comp ((hAc.mul hAc).mul hAc))
    have hl := le_of_tendsto_of_tendsto
      (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 _))
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), _ from by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact hb δ hδ X)
    simp only [regularize, zero_smul, add_zero] at hl
    linarith
  have hs : sSup (Set.range (variation A K)) ≤ (1 / 2 : ℝ) * c^2 * traceReal (A * A * A) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    exact hv X
  unfold rootCost
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem hessianCost_inserted_gram_le (R L : Matrix ι ι ℂ) (hL : L.IsHermitian) :
    hessianCost (Rᴴ * R) (Rᴴ * L * R) ≤
      (3 / 4 : ℝ) * ‖L‖^2 * energy (Rᴴ * R) := by
  have hP := Matrix.posSemidef_conjTranspose_mul_self R
  have hA : (CFC.sqrt (Rᴴ * R)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Rᴴ * R))
  have hAA : CFC.sqrt (Rᴴ * R) * CFC.sqrt (Rᴴ * R) = Rᴴ * R :=
    CFC.sqrt_mul_sqrt_self (Rᴴ * R) hP.nonneg
  have hb : L ≤ ‖L‖ • (1 : Matrix ι ι ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint L from hL).le_algebraMap_norm_self
  have ha : -(‖L‖ • (1 : Matrix ι ι ℂ)) ≤ L := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint L from hL).neg_algebraMap_norm_le_self
  have hm : (‖L‖ • (Rᴴ * R) - Rᴴ * L * R).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one] using
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hb)).conjTranspose_mul_mul_same R
  have hp : (‖L‖ • (Rᴴ * R) + Rᴴ * L * R).PosSemidef := by
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, add_comm] using
      (Matrix.nonneg_iff_posSemidef.mp (neg_le_iff_add_nonneg.mp ha)).conjTranspose_mul_mul_same R
  unfold hessianCost
  simpa only [hAA, energy] using rootCost_le_of_order hA
    (by
      change (Rᴴ * L * R)ᴴ = Rᴴ * L * R
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL.eq, Matrix.mul_assoc]) (norm_nonneg L) (by simpa [hAA] using hm)
      (by simpa [hAA] using hp)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma blockD_mul (A B : Three → Matrix ι ι ℂ) :
    blockD A * blockD B = blockD (fun v => A v * B v) := by
  unfold blockD
  rw [← blocks_mul, Matrix.diagonal_mul_diagonal]

omit [Fintype ι] [DecidableEq ι] in
lemma blockD_star (A : Three → Matrix ι ι ℂ) :
    (blockD A)ᴴ = blockD (fun v => (A v)ᴴ) := by
  unfold blockD
  rw [← blocks_star, Matrix.diagonal_conjTranspose]
  rfl

lemma blockD_posSemidef (A : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef) : (blockD A).PosSemidef := by
  have he : blockD A = (blockD (fun v => CFC.sqrt (A v)))ᴴ *
      blockD (fun v => CFC.sqrt (A v)) := by
    rw [blockD_star, blockD_mul]
    congr 1
    funext v
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A v))).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (A v) (hA v).nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma sqrt_blockD (A : Three → Matrix ι ι ℂ) (hA : ∀ v, (A v).PosSemidef) :
    CFC.sqrt (blockD A) = blockD (fun v => CFC.sqrt (A v)) := by
  apply CFC.sqrt_unique
  · rw [blockD_mul]
    congr 1
    funext v
    exact CFC.sqrt_mul_sqrt_self (A v) (hA v).nonneg
  · exact (blockD_posSemidef _ (fun v =>
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A v)))).nonneg

omit [DecidableEq ι] in
lemma hsReal_blocks_blockD (K : Matrix Three Three (Matrix ι ι ℂ))
    (Y : Three → Matrix ι ι ℂ) :
    hsReal (blocks K) (blockD Y) = ∑ v, hsReal (K v v) (Y v) := by
  simp only [hsReal, blockD, ← blocks_star, ← blocks_mul, traceReal, blocks_trace,
    Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Complex.re_sum]

omit [DecidableEq ι] in
lemma sylv_blockD (A Y : Three → Matrix ι ι ℂ) :
    sylv (blockD A) (blockD Y) = blockD (fun v => sylv (A v) (Y v)) := by
  unfold sylv
  rw [blockD_mul, blockD_mul]
  unfold blockD
  change (Matrix.compRingEquiv Three ι ℂ) _ + (Matrix.compRingEquiv Three ι ℂ) _ =
    (Matrix.compRingEquiv Three ι ℂ) _
  rw [← map_add, ← Matrix.diagonal_add]

lemma rootCost_blockD_ge_diagonal (A : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef) (K : Matrix Three Three (Matrix ι ι ℂ))
    (hsol : ∃ Y, sylv (blockD A) Y = blocks K)
    (hdiag : ∀ v, ∃ Y, sylv (A v) Y = K v v) :
    ∑ v, rootCost (A v) (K v v) ≤ rootCost (blockD A) (blocks K) := by
  choose Y hY using hdiag
  have hv := variation_le_rootCost (blockD_posSemidef A hA) hsol (blockD Y)
  have he : variation (blockD A) (blocks K) (blockD Y) =
      ∑ v, hsReal (K v v) (Y v) := by
    rw [variation, penalty, sylv_blockD]
    simp only [hY]
    rw [hsReal_blocks_blockD]
    change 2 * (∑ v, hsReal (K v v) (Y v)) -
      hsReal (blocks (Matrix.diagonal Y)) (blockD (fun v => K v v)) = _
    rw [hsReal_blocks_blockD, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [Matrix.diagonal_apply_eq]
    apply Finset.sum_congr rfl
    intro v _
    rw [hsReal_symm (Y v) (K v v)]
    ring
  rw [he] at hv
  simp_rw [rootCost_eq_of_solution (hA _) (hY _)]
  simpa only [Finset.mul_sum] using hv

theorem hessianCost_le_of_le_smul {P Q K : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K)
    {c : ℝ} (hc : 0 < c) (hPQ : P ≤ c • Q) :
    hessianCost Q K ≤ Real.sqrt c * hessianCost P K := by
  have hr : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hAs : (CFC.sqrt Q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hps : (CFC.sqrt P).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hsolc := sylv_solvable_mono hps
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (c • Q))).isHermitian hsol
      (CFC.monotone_sqrt hPQ)
  rw [sqrt_smul hQ hc.le] at hsolc
  have hsolQ : ∃ Y, sylv (CFC.sqrt Q) Y = K := by
    obtain ⟨Y, hY⟩ := hsolc
    refine ⟨Real.sqrt c • Y, ?_⟩
    rwa [sylv_smul_right, ← sylv_smul_left]
  have hm := hessianCost_antitone hsol hPQ
  change rootCost (CFC.sqrt (c • Q)) K ≤ rootCost (CFC.sqrt P) K at hm
  rw [sqrt_smul hQ hc.le, rootCost_scale hAs hsolQ hr] at hm
  have hx := mul_le_mul_of_nonneg_left hm hr.le
  simpa only [hessianCost, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hx

def wideRow (R : Three → Matrix ι ι ℂ) : Matrix ι (BlockSpace ι) ℂ :=
  fun i a => R a.1 i a.2

def gramRow (R : Three → Matrix ι ι ℂ) := blocks (fun i j => (R i)ᴴ * R j)
def insertRow (R : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) :=
  blocks (fun i j => (R i)ᴴ * L * R j)
def pinchedRow (R : Three → Matrix ι ι ℂ) := blockD (fun v => (R v)ᴴ * R v)

omit [DecidableEq ι] in
lemma gramRow_eq (R : Three → Matrix ι ι ℂ) : gramRow R = (wideRow R)ᴴ * wideRow R := by
  rfl

omit [DecidableEq ι] in
lemma insertRow_eq (R : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) :
    insertRow R L = (wideRow R)ᴴ * L * wideRow R := by
  rfl

omit [DecidableEq ι] in
lemma gramRow_posSemidef (R : Three → Matrix ι ι ℂ) : (gramRow R).PosSemidef := by
  rw [gramRow_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma pinchedRow_posSemidef (R : Three → Matrix ι ι ℂ) : (pinchedRow R).PosSemidef :=
  blockD_posSemidef _ (fun _ => Matrix.posSemidef_conjTranspose_mul_self _)

lemma gramRow_le_two_pinchedRow (R : Three → Matrix ι ι ℂ)
    (v : Three) (hR : R v = 0) : gramRow R ≤ (2 : ℝ) • pinchedRow R := by
  let R' : Three → Matrix ι ι ℂ := fun i => if i = v + 1 then R i else -(R i)
  have he : (2 : ℝ) • pinchedRow R - gramRow R = gramRow R' := by
    ext a b
    rcases a with ⟨a, i⟩
    rcases b with ⟨b, j⟩
    change (2 : ℝ) • (Matrix.diagonal (fun k => (R k)ᴴ * R k) a b i j) -
      ((R a)ᴴ * R b) i j = ((R' a)ᴴ * R' b) i j
    fin_cases v
    · change R 0 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
    · change R 1 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
    · change R 2 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
  rw [Matrix.le_iff, he]
  exact gramRow_posSemidef R'

theorem hessianCost_gramRow_ge_edges (R : Three → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (v : Three) (hR : R v = 0) :
    (∑ w, hessianCost ((R w)ᴴ * R w) ((R w)ᴴ * L * R w)) ≤
      Real.sqrt 2 * hessianCost (gramRow R) (insertRow R L) := by
  have hsol : ∃ Y, sylv (CFC.sqrt (gramRow R)) Y = insertRow R L := by
    rw [gramRow_eq, insertRow_eq]
    exact sylv_solvable_inserted_gram _ _
  have hQ := pinchedRow_posSemidef R
  have hle := gramRow_le_two_pinchedRow R v hR
  have hqs : (CFC.sqrt (pinchedRow R)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (pinchedRow R))
  have hsol2 := sylv_solvable_mono
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (gramRow R)))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((2 : ℝ) • pinchedRow R))).isHermitian
    hsol (CFC.monotone_sqrt hle)
  rw [sqrt_smul hQ (by norm_num : (0 : ℝ) ≤ 2)] at hsol2
  have hsolQ : ∃ Y, sylv (CFC.sqrt (pinchedRow R)) Y = insertRow R L := by
    obtain ⟨Y, hY⟩ := hsol2
    refine ⟨Real.sqrt 2 • Y, ?_⟩
    rwa [sylv_smul_right, ← sylv_smul_left]
  have hdiag (w : Three) := sylv_solvable_inserted_gram (R w) L
  have hs : CFC.sqrt (pinchedRow R) = blockD (fun w => CFC.sqrt ((R w)ᴴ * R w)) :=
    sqrt_blockD _ (fun _ => Matrix.posSemidef_conjTranspose_mul_self _)
  have hl := rootCost_blockD_ge_diagonal
    (fun w => CFC.sqrt ((R w)ᴴ * R w))
    (fun w => Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((R w)ᴴ * R w)))
    (fun i j => (R i)ᴴ * L * R j) (by simpa only [← hs, insertRow] using hsolQ) hdiag
  calc
    _ ≤ hessianCost (pinchedRow R) (insertRow R L) := by
      simpa only [hessianCost, hs, insertRow] using hl
    _ ≤ _ := hessianCost_le_of_le_smul hQ hsol (by norm_num : (0 : ℝ) < 2) hle

lemma rowStar_blocks (W : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar W v = blocks (fun a b => if a = v then triangleBlocks W a b else 0) := by
  ext a b
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  simp only [rowStar, vertexProj, Matrix.diagonal_mul, triangle, blocks, Matrix.comp_apply]
  change (if a = v then (1 : ℂ) else 0) * triangleBlocks W a b i j =
    (if a = v then triangleBlocks W a b else 0) i j
  split_ifs <;> simp

lemma starGram_eq_gramRow (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v = gramRow (triangleBlocks W v) := by
  unfold starGram
  rw [rowStar_blocks]
  let A : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change (blocks A)ᴴ * blocks A = _
  rw [← blocks_star, ← blocks_mul]
  unfold gramRow
  congr 1
  apply Matrix.ext
  intro a b
  change (∑ c, star (A c a) * A c b) = (triangleBlocks W v a)ᴴ * triangleBlocks W v b
  simp [A, apply_ite, Matrix.star_eq_conjTranspose]

lemma starInsert_eq_insertRow (W D : Three → Matrix ι ι ℂ) (v : Three) :
    starInsert W D v = insertRow (triangleBlocks W v) (D v) := by
  unfold starInsert blockD
  rw [rowStar_blocks]
  let A : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change (blocks A)ᴴ * blocks (Matrix.diagonal D) * blocks A = _
  rw [← blocks_star, ← blocks_mul, ← blocks_mul]
  unfold insertRow
  congr 1
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  change (∑ c, star (A c a) * D c * A c b) =
    (triangleBlocks W v a)ᴴ * D v * triangleBlocks W v b
  simp [A, apply_ite, Matrix.star_eq_conjTranspose]

def centerGram (W : Three → Matrix ι ι ℂ) (v : Three) : Matrix ι ι ℂ :=
  ∑ w, triangleBlocks W v w * (triangleBlocks W v w)ᴴ

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_adj (W : Three → Matrix ι ι ℂ) (v w : Three) :
    (triangleBlocks W v w)ᴴ = triangleBlocks W w v := by
  fin_cases v <;> fin_cases w <;> simp [triangleBlocks]

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_diag (W : Three → Matrix ι ι ℂ) (v : Three) :
    triangleBlocks W v v = 0 := by
  fin_cases v <;> simp [triangleBlocks]

omit [DecidableEq ι] in
lemma centerGram_posSemidef (W : Three → Matrix ι ι ℂ) (v : Three) :
    (centerGram W v).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun w _ => (Matrix.posSemidef_self_mul_conjTranspose _).nonneg)

omit [DecidableEq ι] in
lemma edgeGram_le_centerGram (W : Three → Matrix ι ι ℂ) (v w : Three) :
    (triangleBlocks W w v)ᴴ * triangleBlocks W w v ≤ centerGram W v := by
  rw [triangleBlocks_adj]
  rw [← triangleBlocks_adj W v w]
  exact Finset.single_le_sum (fun a _ =>
    (Matrix.posSemidef_self_mul_conjTranspose (triangleBlocks W v a)).nonneg)
    (Finset.mem_univ w)

theorem neighbor_comparison (W D : Three → Matrix ι ι ℂ) (w : Three) :
    (∑ v, hessianCost (centerGram W v)
      ((triangleBlocks W w v)ᴴ * D w * triangleBlocks W w v)) ≤
      Real.sqrt 2 * hessianCost (starGram W w) (starInsert W D w) := by
  rw [starGram_eq_gramRow, starInsert_eq_insertRow]
  calc
    _ ≤ ∑ v, hessianCost ((triangleBlocks W w v)ᴴ * triangleBlocks W w v)
        ((triangleBlocks W w v)ᴴ * D w * triangleBlocks W w v) := by
      apply Finset.sum_le_sum
      intro v _
      exact hessianCost_antitone (sylv_solvable_inserted_gram _ _)
        (edgeGram_le_centerGram W v w)
    _ ≤ _ := hessianCost_gramRow_ge_edges _ (D w) w (triangleBlocks_diag W w)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def sqrtInverse {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ :=
  (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).symm

lemma sqrtInverse_solves {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    sylv (CFC.sqrt P) (sqrtInverse hP K) = K := by
  exact (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).apply_symm_apply K

def hessianPairPD {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) : ℝ :=
  (3 / 2 : ℝ) * hsReal K (sqrtInverse hP L)

lemma hessianPairPD_symm {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    hessianPairPD hP K L = hessianPairPD hP L K := by
  have hs := hsReal_sylv_symm
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
    (sqrtInverse hP K) (sqrtInverse hP L)
  rw [sqrtInverse_solves, sqrtInverse_solves, hsReal_symm _ L] at hs
  exact congrArg ((3 / 2 : ℝ) * ·) hs.symm

lemma hessianPairPD_self {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    hessianPairPD hP K K = hessianCost P K := by
  exact (rootCost_eq_of_solution
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) (sqrtInverse_solves hP K)).symm

lemma two_hessianPairPD_le {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    2 * hessianPairPD hP K L ≤ hessianCost P K + hessianCost P L := by
  have hn := rootCost_nonneg (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P))
    (show ∃ Y, sylv (CFC.sqrt P) Y = K - L from ⟨_, sqrtInverse_solves hP (K - L)⟩)
  change 0 ≤ hessianCost P (K - L) at hn
  rw [← hessianPairPD_self hP] at hn
  have he : hessianPairPD hP (K - L) (K - L) =
      hessianPairPD hP K K + hessianPairPD hP L L - 2 * hessianPairPD hP K L := by
    have hs := hessianPairPD_symm hP K L
    simp only [hessianPairPD, map_sub, hsReal_sub_left, hsReal_sub_right] at *
    linarith
  rw [he, hessianPairPD_self, hessianPairPD_self] at hn
  linarith

lemma hessianPairPD_eq_trace {P K L : Matrix ι ι ℂ}
    (hP : P.PosDef) (hK : K.IsHermitian) :
    hessianPairPD hP K L = (3 / 2 : ℝ) * traceReal (sqrtInverse hP L * K) := by
  simp only [hessianPairPD, hsReal, hK.eq, traceReal_mul_comm K]

theorem energy_path_hasDerivAt {P : ℝ → Matrix ι ι ℂ} {U : Matrix ι ι ℂ} {x : ℝ}
    (hP : (P x).PosDef) (hn : ∀ᶠ t in 𝓝 x, 0 ≤ P t) (hd : HasDerivAt P U x) :
    HasDerivAt (fun t => energy (P t)) (energyGradient (P x) U) x := by
  exact (energy_hasFDerivWithinAt hP).comp_hasDerivAt x hd hn

theorem energyGradient_path_hasDerivAt {P K : ℝ → Matrix ι ι ℂ}
    {U V : Matrix ι ι ℂ} {x : ℝ}
    (hP : (P x).PosDef) (hn : ∀ᶠ t in 𝓝 x, 0 ≤ P t)
    (hK : (K x).IsHermitian) (hdP : HasDerivAt P U x) (hdK : HasDerivAt K V x) :
    HasDerivAt (fun t => energyGradient (P t) (K t))
      (hessianPairPD hP (K x) U + energyGradient (P x) V) x := by
  have hs : HasDerivAt (fun t => CFC.sqrt (P t)) (sqrtInverse hP U) x :=
    (sqrt_smoothWithin_posDef hP).2.comp_hasDerivAt x hdP hn
  have hm := hs.fun_mul hdK
  have ht := (traceRealCLM.hasFDerivAt.comp_hasDerivAt x hm).const_smul (3 / 2 : ℝ)
  convert! ht using 1
  simp only [hessianPairPD_eq_trace hP hK, energyGradient_apply,
    traceRealCLM_apply, traceReal_add, smul_eq_mul]
  ring

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

def rowNorm (R : Matrix ι κ ℂ) (i : ι) : ℝ := Real.sqrt (∑ j, ‖R i j‖^2)
def colNorm (R : Matrix ι κ ℂ) (j : κ) : ℝ := Real.sqrt (∑ i, ‖R i j‖^2)

omit [Fintype ι] [Fintype μ] in
theorem norm_mul_entry_le (R : Matrix ι κ ℂ) (S : Matrix κ μ ℂ) (i : ι) (j : μ) :
    ‖(R * S) i j‖ ≤ rowNorm R i * colNorm S j := by
  calc
    ‖(R * S) i j‖ ≤ ∑ k, ‖R i k * S k j‖ := norm_sum_le _ _
    _ = ∑ k, ‖R i k‖ * ‖S k j‖ := by simp only [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

omit [Fintype κ] in
theorem colNorm_sq (R : Matrix ι κ ℂ) (j : κ) :
    (colNorm R j)^2 = ((Rᴴ * R) j j).re := by
  rw [colNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable [DecidableEq κ]

theorem colNorm_sqrt_gram (R : Matrix ι κ ℂ) (j : κ) :
    colNorm (CFC.sqrt (Rᴴ * R)) j = colNorm R j := by
  have hsP := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Rᴴ * R))
  have he : (colNorm (CFC.sqrt (Rᴴ * R)) j)^2 = (colNorm R j)^2 := by
    rw [colNorm_sq, hsP.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (Rᴴ * R) (Matrix.posSemidef_conjTranspose_mul_self R).nonneg,
      colNorm_sq]
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp he

theorem entry_gradient_le (R : Matrix ι κ ℂ) (i : ι) (j : κ) :
    ‖(R * CFC.sqrt (Rᴴ * R)) i j‖ ≤ rowNorm R i * colNorm R j := by
  simpa only [colNorm_sqrt_gram] using norm_mul_entry_le R (CFC.sqrt (Rᴴ * R)) i j

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrt_mul_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hPQ : P * Q = 0) : CFC.sqrt P * Q = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  change (CFC.sqrt P * Q)ᴴ * (CFC.sqrt P * Q) = 0
  rw [Matrix.conjTranspose_mul, hs.eq, ← Matrix.mul_assoc,
    Matrix.mul_assoc Qᴴ, CFC.sqrt_mul_sqrt_self P hP.nonneg,
    Matrix.mul_assoc, hPQ, mul_zero]

lemma mul_sqrt_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQP : Q * P = 0) : Q * CFC.sqrt P = 0 := by
  have ht : P * Qᴴ = 0 := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hQP
  have hz := sqrt_mul_eq_zero_of_mul_eq_zero hP ht
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  simpa only [Matrix.conjTranspose_mul, hs.eq, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hz

lemma sqrt_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    CFC.sqrt (P + Q) = CFC.sqrt P + Q := by
  apply CFC.sqrt_unique
  · have hsQ := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
    have hQs := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
    simp only [add_mul, mul_add, hsQ, hQs, hQQ,
      CFC.sqrt_mul_sqrt_self P hP.nonneg, add_zero, zero_add]
  · exact add_nonneg (CFC.sqrt_nonneg P) hQ.nonneg

lemma energy_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    energy (P + Q) = energy P + traceReal Q := by
  rw [energy, sqrt_add_projection hP hQ hQQ hPQ hQP]
  simp only [add_mul, mul_add, hPQ, mul_sqrt_eq_zero_of_mul_eq_zero hP hQP,
    hQQ, add_zero, zero_add, traceReal_add, energy]

lemma energyGradient_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hQK : Q * K = 0) :
    energyGradient (P + Q) K = energyGradient P K := by
  simp only [energyGradient_apply, sqrt_add_projection hP hQ hQQ hPQ hQP,
    add_mul, hQK, add_zero]

lemma hessianCost_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hPD : (P + Q).PosDef) : hessianCost (P + Q) K = hessianCost P K := by
  let A := CFC.sqrt P
  let E := 1 - Q
  let Y := sqrtInverse hPD K
  let Z := E * Y * E
  have hAQ : A * Q = 0 := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
  have hQA : Q * A = 0 := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
  have hQE : Q * E = 0 := by simp [E, mul_sub, hQQ]
  have hEQ : E * Q = 0 := by simp [E, sub_mul, hQQ]
  have hAE : A * E = A := by simp [E, mul_sub, hAQ]
  have hEA : E * A = A := by simp [E, sub_mul, hQA]
  have hKE : K * E = K := by simp [E, mul_sub, hKQ]
  have hEK : E * K = K := by simp [E, sub_mul, hQK]
  have hY : sylv (A + Q) Y = K := by
    simpa only [sqrt_add_projection hP hQ hQQ hPQ hQP] using sqrtInverse_solves hPD K
  have hZ : sylv A Z = K := by
    have hm := congrArg (fun B => E * B * E) hY
    simp only [sylv, add_mul, mul_add, Matrix.mul_assoc] at hm ⊢
    simp only [← Matrix.mul_assoc E A, hEA, ← Matrix.mul_assoc E Q, hEQ,
      zero_mul, add_zero, hQE, mul_zero,
      hEK, hKE] at hm
    simpa only [Z, Matrix.mul_assoc, ← Matrix.mul_assoc A E, hAE,
      ← Matrix.mul_assoc E A, hEA] using hm
  have hQZ : Q * Z = 0 := by simp only [Z, ← Matrix.mul_assoc, hQE, zero_mul]
  have hZQ : Z * Q = 0 := by simp only [Z, Matrix.mul_assoc, hEQ, mul_zero]
  have hZ' : sylv (CFC.sqrt (P + Q)) Z = K := by
    rw [sqrt_add_projection hP hQ hQQ hPQ hQP]
    change sylv (A + Q) Z = K
    simpa [sylv, add_mul, mul_add, hQZ, hZQ] using hZ
  exact (rootCost_eq_of_solution
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P + Q))) hZ').trans
    (rootCost_eq_of_solution (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hZ).symm

lemma exists_kernel_projection {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    ∃ Q : Matrix ι ι ℂ, Q.PosSemidef ∧ Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧
      (P + Q).PosDef := by
  let ev := hP.isHermitian.eigenvalues
  let U := hP.isHermitian.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (ev i : ℂ))
  let q : Matrix ι ι ℂ := Matrix.diagonal (fun i => if ev i = 0 then 1 else 0)
  let Q := f q
  have hD : f D = P := hP.isHermitian.spectral_theorem.symm
  have hq : q.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ (if ev i = 0 then (1 : ℂ) else 0)
    split_ifs <;> simp
  have hQ : Q.PosSemidef := by
    simpa only [Q, f, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hq.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  have hqq : q * q = q := by
    simp only [q, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  have hQQ : Q * Q = Q := by exact (map_mul f q q).symm.trans (congrArg f hqq)
  have hDq : D * q = 0 := by
    simp only [D, q, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_zero]
    congr 1
    ext i
    split_ifs with hi <;> simp [hi]
  have hPQ : P * Q = 0 := by
    rw [← hD]
    change f D * f q = 0
    rw [← map_mul, hDq, map_zero]
  have hQP : Q * P = 0 := by
    simpa only [Matrix.conjTranspose_mul, hQ.isHermitian.eq, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hPQ
  have hpos : (D + q).PosDef := by
    simp only [D, q, Matrix.diagonal_add]
    apply Matrix.PosDef.diagonal
    intro i
    change 0 < (ev i : ℂ) + (if ev i = 0 then 1 else 0)
    by_cases hi : ev i = 0
    · simp [hi]
    · simp only [hi, ite_false, add_zero]
      exact_mod_cast lt_of_le_of_ne (hP.eigenvalues_nonneg i) (Ne.symm hi)
  have hu : IsUnit (P + Q) := by
    have hh := hpos.isUnit.map f.toMonoidHom
    change IsUnit (f (D + q)) at hh
    simpa only [map_add, hD] using hh
  exact ⟨Q, hQ, hQQ, hPQ, hQP, (hP.add hQ).posDef_iff_isUnit.mpr hu⟩

lemma deriv_mul_projection_eq_zero {P : ℝ → Matrix ι ι ℂ} {U Q : Matrix ι ι ℂ}
    {x : ℝ} (hd : HasDerivAt P U x) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0) : U * Q = 0 := by
  have hh := hd.mul_const Q
  have he : HasDerivAt (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (U * Q) x :=
    hh.congr_of_eventuallyEq (hz.mono fun _ ht => ht.symm)
  exact he.unique (hasDerivAt_const x 0)

lemma projection_mul_deriv_eq_zero {P : ℝ → Matrix ι ι ℂ} {U Q : Matrix ι ι ℂ}
    {x : ℝ} (hd : HasDerivAt P U x) (hz : ∀ᶠ t in 𝓝 x, Q * P t = 0) : Q * U = 0 := by
  have hh := hd.const_mul Q
  have he : HasDerivAt (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (Q * U) x :=
    hh.congr_of_eventuallyEq (hz.mono fun _ ht => ht.symm)
  exact he.unique (hasDerivAt_const x 0)

omit [DecidableEq ι] in
lemma hermitian_mul_zero_flip {P Q : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (h : P * Q = 0) : Q * P = 0 := by
  simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h

noncomputable def hessianPair (P K L : Matrix ι ι ℂ) : ℝ :=
  (hessianCost P (K + L) - hessianCost P (K - L)) / 4

lemma hessianPair_eq_PD {P : Matrix ι ι ℂ} (hP : P.PosDef)
    (K L : Matrix ι ι ℂ) : hessianPair P K L = hessianPairPD hP K L := by
  have hs := hessianPairPD_symm hP K L
  unfold hessianPair
  rw [← hessianPairPD_self hP, ← hessianPairPD_self hP]
  simp only [hessianPairPD, map_add, map_sub, hsReal_add_left, hsReal_add_right,
    hsReal_sub_left, hsReal_sub_right] at hs ⊢
  linarith

lemma hessianPair_add_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hKQ : K * Q = 0) (hQK : Q * K = 0) (hLQ : L * Q = 0) (hQL : Q * L = 0)
    (hPD : (P + Q).PosDef) : hessianPair (P + Q) K L = hessianPair P K L := by
  unfold hessianPair
  rw [hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [add_mul, hKQ, hLQ]) (by simp [mul_add, hQK, hQL]) hPD,
    hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [sub_mul, hKQ, hLQ]) (by simp [mul_sub, hQK, hQL]) hPD]

theorem energy_supported_path_hasDerivAt {P : ℝ → Matrix ι ι ℂ}
    {Q U : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hd : HasDerivAt P U x) :
    HasDerivAt (fun t => energy (P t)) (energyGradient (P x) U) x := by
  have hzl : ∀ᶠ t in 𝓝 x, Q * P t = 0 := by
    filter_upwards [hn, hz] with t ht htz
    exact hermitian_mul_zero_flip ht.isHermitian hQ.isHermitian htz
  have hQU := projection_mul_deriv_eq_zero hd hzl
  have hnonneg : ∀ᶠ t in 𝓝 x, 0 ≤ P t + Q := hn.mono fun _ ht => (ht.add hQ).nonneg
  have hh := (energy_path_hasDerivAt hPD hnonneg (hd.add_const Q)).sub_const (traceReal Q)
  rw [energyGradient_add_projection hn.self_of_nhds hQ hQQ hz.self_of_nhds
    hzl.self_of_nhds hQU] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hn, hz, hzl] with t ht hr hl
  rw [energy_add_projection ht hQ hQQ hr hl]
  ring

theorem energyGradient_supported_path_hasDerivAt {P K : ℝ → Matrix ι ι ℂ}
    {Q U V : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hK : ∀ᶠ t in 𝓝 x, (K t).IsHermitian) (hkz : ∀ᶠ t in 𝓝 x, K t * Q = 0)
    (hdP : HasDerivAt P U x) (hdK : HasDerivAt K V x) :
    HasDerivAt (fun t => energyGradient (P t) (K t))
      (hessianPair (P x) (K x) U + energyGradient (P x) V) x := by
  have hzl : ∀ᶠ t in 𝓝 x, Q * P t = 0 := by
    filter_upwards [hn, hz] with t ht htz
    exact hermitian_mul_zero_flip ht.isHermitian hQ.isHermitian htz
  have hkzl : ∀ᶠ t in 𝓝 x, Q * K t = 0 := by
    filter_upwards [hK, hkz] with t ht htz
    exact hermitian_mul_zero_flip ht hQ.isHermitian htz
  have hUQ := deriv_mul_projection_eq_zero hdP hz
  have hQU := projection_mul_deriv_eq_zero hdP hzl
  have hQV := projection_mul_deriv_eq_zero hdK hkzl
  have hnonneg : ∀ᶠ t in 𝓝 x, 0 ≤ P t + Q := hn.mono fun _ ht => (ht.add hQ).nonneg
  have hh := energyGradient_path_hasDerivAt hPD hnonneg hK.self_of_nhds
    (hdP.add_const Q) hdK
  rw [← hessianPair_eq_PD, hessianPair_add_projection hn.self_of_nhds hQ hQQ
    hz.self_of_nhds hzl.self_of_nhds hkz.self_of_nhds hkzl.self_of_nhds hUQ hQU hPD,
    energyGradient_add_projection hn.self_of_nhds hQ hQQ hz.self_of_nhds
      hzl.self_of_nhds hQV] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hn, hz, hzl, hkzl] with t ht hr hl hkl
  exact (energyGradient_add_projection ht hQ hQQ hr hl hkl).symm

end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def weightedGram (B : Matrix ι ι ℂ) (w : ι → ℝ) : Matrix ι ι ℂ :=
  Bᴴ * Matrix.diagonal (fun i => (w i : ℂ)) * B

lemma weightedGram_posSemidef (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) : (weightedGram B w).PosSemidef :=
  (Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hw i))).conjTranspose_mul_mul_same B

lemma weightedGram_isHermitian (B : Matrix ι ι ℂ) (w : ι → ℝ) :
    (weightedGram B w).IsHermitian := by
  have hd : (Matrix.diagonal (fun i => (w i : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    simp
  exact Matrix.isHermitian_conjTranspose_mul_mul B hd

lemma weightedGram_mul_zero {B Q : Matrix ι ι ℂ} {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hz : weightedGram B w * Q = 0) : B * Q = 0 := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (w i : ℂ))
  have hD : D.PosDef := Matrix.PosDef.diagonal (fun i => RCLike.ofReal_pos.mpr (hw i))
  have hs : (CFC.sqrt D).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).isHermitian
  have hunit : IsUnit (CFC.sqrt D) :=
    (Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.sqrt D hD.isStrictlyPositive)).isUnit
  have hgram : (CFC.sqrt D * B)ᴴ * (CFC.sqrt D * B) = weightedGram B w := by
    calc
      _ = Bᴴ * (CFC.sqrt D * CFC.sqrt D) * B := by
        rw [Matrix.conjTranspose_mul, hs.eq]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg]; rfl
  have hsq : (CFC.sqrt D * B * Q)ᴴ * (CFC.sqrt D * B * Q) = 0 := by
    calc
      _ = Qᴴ * ((CFC.sqrt D * B)ᴴ * (CFC.sqrt D * B)) * Q := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Qᴴ * (weightedGram B w * Q) := by rw [hgram, Matrix.mul_assoc]
      _ = 0 := by rw [hz, mul_zero]
  have hzero := (CStarRing.star_mul_self_eq_zero_iff _).mp hsq
  apply hunit.mul_left_cancel
  simpa only [Matrix.mul_assoc, mul_zero] using hzero

lemma weightedGram_kernel_projection (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) :
    ∃ Q : Matrix ι ι ℂ, Q.PosSemidef ∧ Q * Q = Q ∧ B * Q = 0 ∧
      (weightedGram B w + Q).PosDef := by
  obtain ⟨Q, hQ, hQQ, hPQ, _, hPD⟩ :=
    exists_kernel_projection (weightedGram_posSemidef B (fun i => (hw i).le))
  exact ⟨Q, hQ, hQQ, weightedGram_mul_zero hw hPQ, hPD⟩

lemma weightedGram_mul_eq_zero (B Q : Matrix ι ι ℂ) (w : ι → ℝ) (hz : B * Q = 0) :
    weightedGram B w * Q = 0 := by
  simp only [weightedGram, Matrix.mul_assoc, hz, mul_zero]

lemma diagonal_real_hasDerivAt {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => Matrix.diagonal (fun i => (w t i : ℂ)))
      (Matrix.diagonal (fun i => (w' i : ℂ))) x := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.diagonal_apply_eq] using (hd i).ofReal_comp
  · simpa only [Matrix.diagonal_apply_ne _ hij] using
      (hasDerivAt_const x (0 : ℂ))

lemma weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => weightedGram B (w t)) (weightedGram B w') x :=
  ((diagonal_real_hasDerivAt hd).const_mul Bᴴ).mul_const B

theorem energy_weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hw : ∀ᶠ t in 𝓝 x, ∀ i, 0 < w t i)
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => energy (weightedGram B (w t)))
      (energyGradient (weightedGram B (w x)) (weightedGram B w')) x := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw.self_of_nhds
  exact energy_supported_path_hasDerivAt hQ hQQ hPD
    (hw.mono fun t ht => weightedGram_posSemidef B (fun i => (ht i).le))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (w t) hBQ)
    (weightedGram_hasDerivAt B hd)

theorem energyGradient_weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w k : ℝ → ι → ℝ} {w' k' : ι → ℝ} {x : ℝ}
    (hw : ∀ᶠ t in 𝓝 x, ∀ i, 0 < w t i)
    (hdw : ∀ i, HasDerivAt (fun t => w t i) (w' i) x)
    (hdk : ∀ i, HasDerivAt (fun t => k t i) (k' i) x) :
    HasDerivAt (fun t => energyGradient (weightedGram B (w t)) (weightedGram B (k t)))
      (hessianPair (weightedGram B (w x)) (weightedGram B (k x)) (weightedGram B w') +
        energyGradient (weightedGram B (w x)) (weightedGram B k')) x := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw.self_of_nhds
  exact energyGradient_supported_path_hasDerivAt hQ hQQ hPD
    (hw.mono fun t ht => weightedGram_posSemidef B (fun i => (ht i).le))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (w t) hBQ)
    (Eventually.of_forall fun t => weightedGram_isHermitian B (k t))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (k t) hBQ)
    (weightedGram_hasDerivAt B hdw) (weightedGram_hasDerivAt B hdk)

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hessianPair_self_of_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hPD : (P + Q).PosDef) : hessianPair P K K = hessianCost P K := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hKQ hQK hPD,
    hessianPair_eq_PD hPD, hessianPairPD_self,
    hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD]

lemma two_hessianPair_le_of_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hKQ : K * Q = 0) (hQK : Q * K = 0) (hLQ : L * Q = 0) (hQL : Q * L = 0)
    (hPD : (P + Q).PosDef) :
    2 * hessianPair P K L ≤ hessianCost P K + hessianCost P L := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hLQ hQL hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hLQ hQL hPD,
    hessianPair_eq_PD hPD]
  exact two_hessianPairPD_le hPD K L

lemma hessianPair_weightedGram_self (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k : ι → ℝ) :
    hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B k) =
      hessianCost (weightedGram B w) (weightedGram B k) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  exact hessianPair_self_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hPD

lemma two_hessianPair_weightedGram_le (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k l : ι → ℝ) :
    2 * hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B l) ≤
      hessianCost (weightedGram B w) (weightedGram B k) +
      hessianCost (weightedGram B w) (weightedGram B l) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  have hLQ := weightedGram_mul_eq_zero B Q l hBQ
  exact two_hessianPair_le_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hLQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B l) hQ.isHermitian hLQ) hPD

omit [DecidableEq ι] in
lemma traceReal_blockD (P : Three → Matrix ι ι ℂ) :
    traceReal (blockD P) = ∑ v, traceReal (P v) := by
  simp [traceReal, Matrix.trace, blockD, Fintype.sum_prod_type]

omit [DecidableEq ι] in
lemma hsReal_blockD (A B : Three → Matrix ι ι ℂ) :
    hsReal (blockD A) (blockD B) = ∑ v, hsReal (A v) (B v) := by
  simp only [hsReal, blockD_star, blockD_mul, traceReal_blockD]

lemma rootCost_blockD (A K : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef)
    (hsol : ∀ v, ∃ Y, sylv (A v) Y = K v) :
    rootCost (blockD A) (blockD K) = ∑ v, rootCost (A v) (K v) := by
  choose Y hY using hsol
  have hsol' : sylv (blockD A) (blockD Y) = blockD K := by
    rw [sylv_blockD]
    congr 1
    funext v
    exact hY v
  rw [rootCost_eq_of_solution (blockD_posSemidef A hA) hsol',
    hsReal_blockD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact (rootCost_eq_of_solution (hA v) (hY v)).symm

lemma hessianCost_blockD (P K : Three → Matrix ι ι ℂ)
    (hP : ∀ v, (P v).PosSemidef)
    (hsol : ∀ v, ∃ Y, sylv (CFC.sqrt (P v)) Y = K v) :
    hessianCost (blockD P) (blockD K) = ∑ v, hessianCost (P v) (K v) := by
  change rootCost (CFC.sqrt (blockD P)) (blockD K) =
    ∑ v, rootCost (CFC.sqrt (P v)) (K v)
  rw [sqrt_blockD P hP]
  exact rootCost_blockD _ K
    (fun v => Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P v))) hsol

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

lemma weightedGram_smul (B : Matrix ι ι ℂ) (c : ℝ) (w : ι → ℝ) :
    weightedGram B (fun i => c * w i) = c • weightedGram B w := by
  have he : Matrix.diagonal (fun i => ((c * w i : ℝ) : ℂ)) =
      c • Matrix.diagonal (fun i => (w i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  unfold weightedGram
  rw [he, Matrix.mul_smul, Matrix.smul_mul]

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def vertexRoot (g : Three → ι → ℝ) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  Matrix.diagonal (fun a => (Real.sqrt (g a.1 a.2) : ℂ))

def weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) : Three → Matrix ι ι ℂ :=
  fun v i j => (Real.sqrt (g v i) : ℂ) * A v i j * (Real.sqrt (g (v+1) j) : ℂ)

omit [Fintype ι] in
lemma vertexRoot_star (g : Three → ι → ℝ) : (vertexRoot g)ᴴ = vertexRoot g := by
  unfold vertexRoot
  rw [Matrix.diagonal_conjTranspose]
  simp

lemma vertexRoot_sq (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * vertexRoot g = Matrix.diagonal (fun a => (g a.1 a.2 : ℂ)) := by
  rw [vertexRoot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg a.1 a.2)]

lemma vertexRoot_commute_vertexProj (g : Three → ι → ℝ) (v : Three) :
    vertexRoot g * vertexProj v = vertexProj v * vertexRoot g := by
  dsimp only [vertexRoot, vertexProj]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

lemma triangle_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    triangle (weightedArray A g) = vertexRoot g * triangle A * vertexRoot g := by
  ext ⟨v,i⟩ ⟨w,j⟩
  fin_cases v <;> fin_cases w <;>
    simp [triangle, triangleBlocks, blocks, weightedArray, vertexRoot,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      mul_comm, mul_left_comm, mul_assoc] <;> first | exact Or.inl (mul_comm _ _) | ring

lemma rowStar_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :
    rowStar (weightedArray A g) v = vertexRoot g * rowStar A v * vertexRoot g := by
  unfold rowStar
  rw [triangle_weightedArray]
  simp only [← Matrix.mul_assoc]
  rw [← vertexRoot_commute_vertexProj]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

lemma rowStar_eq_blocks (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v = blocks (fun a b => if a = v then triangleBlocks A a b else 0) := by
  exact rowStar_blocks A v

def rowBare (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :=
  rowStar A v * vertexRoot g

def colBare (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :=
  (rowStar A v)ᴴ * vertexRoot g

lemma starGram_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    starGram (weightedArray A g) v = weightedGram (rowBare A g v) (fun a => g a.1 a.2) := by
  have hr : rowStar (weightedArray A g) v = vertexRoot g * rowBare A g v := by
    rw [rowStar_weightedArray, rowBare, Matrix.mul_assoc]
  rw [starGram, hr, Matrix.conjTranspose_mul, vertexRoot_star]
  unfold weightedGram
  calc
    _ = (rowBare A g v)ᴴ * (vertexRoot g * vertexRoot g) * rowBare A g v := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [vertexRoot_sq g hg]

lemma centerGram_weightedArray_padded (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    rowStar (weightedArray A g) v * (rowStar (weightedArray A g) v)ᴴ =
      weightedGram (colBare A g v) (fun a => g a.1 a.2) := by
  rw [rowStar_weightedArray]
  unfold colBare weightedGram
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, vertexRoot_star]
  rw [← vertexRoot_sq g hg]
  simp only [Matrix.mul_assoc]

lemma rowBare_congr (A : Three → Matrix ι ι ℂ) (g g' : Three → ι → ℝ) (v : Three)
    (he : ∀ w, w ≠ v → ∀ i, g' w i = g w i) : rowBare A g' v = rowBare A g v := by
  ext a b
  dsimp only [rowBare, vertexRoot]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, rowStar_apply]
  by_cases ha : a.1 = v
  · rw [ite_eq_left ha]
    by_cases hb : b.1 = v
    · rw [ha, hb, triangleBlocks_diag, Matrix.zero_apply, zero_mul, zero_mul]
    · rw [he b.1 hb]
  · rw [ite_eq_right ha, zero_mul, zero_mul]

lemma colBare_congr (A : Three → Matrix ι ι ℂ) (g g' : Three → ι → ℝ) (v : Three)
    (he : ∀ i, g' v i = g v i) : colBare A g' v = colBare A g v := by
  ext a b
  dsimp only [colBare, vertexRoot]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp only [Matrix.conjTranspose_apply, rowStar_apply]
  by_cases hb : b.1 = v
  · rw [ite_eq_left hb, hb, he]
  · rw [ite_eq_right hb, star_zero, zero_mul, zero_mul]

lemma rowStar_mul_adjoint (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v * (rowStar A v)ᴴ =
      blockD (fun w => if w = v then centerGram A v else 0) := by
  rw [rowStar_eq_blocks]
  let R : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks A a b else 0
  change blocks R * (blocks R)ᴴ = _
  rw [← blocks_star, ← blocks_mul]
  unfold blockD
  congr 1
  apply Matrix.ext
  intro a b
  change (∑ c, R a c * (R b c)ᴴ) = Matrix.diagonal (fun w => if w = v then centerGram A v else 0) a b
  dsimp only [R]
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a
    subst b
    simp only [ite_true, Matrix.diagonal_apply_eq]
    rfl
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, hb]
  · simp only [ite_eq_right ha, zero_mul, Finset.sum_const_zero]
    by_cases hab : a = b
    · subst b
      rw [Matrix.diagonal_apply_eq, ite_eq_right ha]
    · rw [Matrix.diagonal_apply_ne _ hab]

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weightedGram_sub (B : Matrix ι ι ℂ) (f g : ι → ℝ) :
    weightedGram B (fun i => f i-g i) = weightedGram B f-weightedGram B g := by
  unfold weightedGram
  have hd : Matrix.diagonal (fun i => ((f i-g i:ℝ):ℂ)) =
      Matrix.diagonal (fun i => (f i:ℂ))-Matrix.diagonal (fun i => (g i:ℂ)) := by
    rw [Matrix.diagonal_sub]
    simp only [Complex.ofReal_sub]
  rw [hd,Matrix.mul_sub,Matrix.sub_mul]

lemma weightedGram_mono (B : Matrix ι ι ℂ) (f g : ι → ℝ) (hfg : ∀ i, f i ≤ g i) :
    weightedGram B f ≤ weightedGram B g := by
  rw [← sub_nonneg,← weightedGram_sub]
  exact (weightedGram_posSemidef B (fun i => sub_nonneg.mpr (hfg i))).nonneg

lemma rowBare_apply_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three)
    (a b : BlockSpace ι) (ha : a.1 ≠ v) : rowBare A g v a b = 0 := by
  simp [rowBare,vertexRoot,Matrix.mul_diagonal,rowStar_apply,ha]

lemma weightedGram_rowBare_congr (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (v : Three) (f f' : BlockSpace ι → ℝ) (he : ∀ i, f (v,i)=f' (v,i)) :
    weightedGram (rowBare A g v) f = weightedGram (rowBare A g v) f' := by
  ext a b
  unfold weightedGram
  conv_lhs => rw [Matrix.mul_apply]
  conv_rhs => rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.1 = v
  · obtain ⟨w,i⟩ := k
    change w = v at hk
    subst w
    rw [he i]
  · rw [rowBare_apply_zero A g v k b hk]
    simp

lemma hessianCost_smul_direction {P K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (c : ℝ) :
    hessianCost P (c • K) = c^2*hessianCost P K := by
  exact rootCost_smul_direction (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol c

omit [Fintype ι] in
lemma blockD_real_diagonal (d : Three → ι → ℝ) :
    blockD (fun v => Matrix.diagonal (fun i => (d v i:ℂ))) =
      Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2:ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v=w <;> by_cases hi : i=j <;>
    simp [blockD,blocks,Matrix.diagonal,hv,hi,Prod.mk.injEq]

lemma norm_blockD_real_diagonal_le (d : Three → ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ v i, |d v i| ≤ C) :
    ‖blockD (fun v => Matrix.diagonal (fun i => (d v i:ℂ)))‖ ≤ C := by
  rw [blockD_real_diagonal,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun a => by simpa using hd a.1 a.2)

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} {ν : Type uν} [Fintype ι] [DecidableEq ι] [DecidableEq ν]

def groupWeight (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (i : ι) : ℝ :=
  weight h (u i) (p (loc i)) (σ (loc i))

def groupFirst (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (v : ν) (i : ι) : ℝ :=
  if loc i = v then score (u i) (p v) (σ v) * weight h (u i) (p v) (σ v) else 0

def groupSecond (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (v : ν) (i : ι) : ℝ :=
  if loc i = v then (score (u i) (p v) (σ v)^2 - (σ v)⁻¹) *
    weight h (u i) (p v) (σ v) else 0

omit [Fintype ι] [DecidableEq ι] [DecidableEq ν] in
lemma groupWeight_pos {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (i : ι) :
    0 < groupWeight h u loc p σ i := weight_pos hh (hσ (loc i)) _ _

omit [Fintype ι] [DecidableEq ι] in
lemma groupWeight_hasDerivAt_center (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupWeight h u loc (Function.update p v q) σ i)
      (groupFirst h u loc p σ v i) (p v) := by
  by_cases hi : loc i = v
  · simpa [groupWeight, groupFirst, hi] using
      weight_hasDerivAt_center h (u i) (p v) (σ v) (hσ v)
  · simpa [groupWeight, groupFirst, hi] using
      hasDerivAt_const (p v) (weight h (u i) (p (loc i)) (σ (loc i)))

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_hasDerivAt_center (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupFirst h u loc (Function.update p v q) σ v i)
      (groupSecond h u loc p σ v i) (p v) := by
  by_cases hi : loc i = v
  · simpa [groupFirst, groupSecond, hi] using
      weight_score_hasDerivAt_center h (u i) (p v) (σ v) (hσ v)
  · simpa [groupFirst, groupSecond, hi] using hasDerivAt_const (p v) (0 : ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_hasDerivAt_other (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p σ : ν → ℝ) {v w : ν} (hvw : v ≠ w) (i : ι) :
    HasDerivAt (fun q => groupFirst h u loc (Function.update p w q) σ v i) 0 (p w) := by
  simpa [groupFirst, Function.update_of_ne hvw] using
    hasDerivAt_const (p w) (groupFirst h u loc p σ v i)

omit [Fintype ι] [DecidableEq ι] in
lemma groupWeight_hasDerivAt_variance (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupWeight h u loc p (Function.update σ v q) i)
      ((1/2 : ℝ) * groupSecond h u loc p σ v i) (σ v) := by
  by_cases hi : loc i = v
  · simpa [groupWeight, groupSecond, hi, mul_assoc] using
      weight_hasDerivAt_variance h (u i) (p v) (σ v) (hσ v)
  · simpa [groupWeight, groupSecond, hi] using
      hasDerivAt_const (σ v) (weight h (u i) (p (loc i)) (σ (loc i)))

lemma groupEnergy_hasDerivAt_center (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energy (weightedGram B (groupWeight h u loc (Function.update p v q) σ)))
      (energyGradient (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupFirst h u loc p σ v))) (p v) := by
  have hd := energy_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p v q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ v)
  simpa only [Function.update_eq_self] using hd

lemma groupEnergyFirst_hasDerivAt_center (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energyGradient
        (weightedGram B (groupWeight h u loc (Function.update p v q) σ))
        (weightedGram B (groupFirst h u loc (Function.update p v q) σ v)))
      (hessianCost (weightedGram B (groupWeight h u loc p σ))
          (weightedGram B (groupFirst h u loc p σ v)) +
        energyGradient (weightedGram B (groupWeight h u loc p σ))
          (weightedGram B (groupSecond h u loc p σ v))) (p v) := by
  have hd := energyGradient_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p v q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ v)
    (groupFirst_hasDerivAt_center h u loc p hσ v)
  simp only [Function.update_eq_self] at hd
  rw [hessianPair_weightedGram_self B (groupWeight_pos hh u loc p hσ)] at hd
  exact hd

lemma groupEnergyFirst_hasDerivAt_other (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v)
    {v w : ν} (hvw : v ≠ w) :
    HasDerivAt (fun q => energyGradient
        (weightedGram B (groupWeight h u loc (Function.update p w q) σ))
        (weightedGram B (groupFirst h u loc (Function.update p w q) σ v)))
      (hessianPair (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupFirst h u loc p σ v))
        (weightedGram B (groupFirst h u loc p σ w))) (p w) := by
  have hd := energyGradient_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p w q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ w)
    (groupFirst_hasDerivAt_other h u loc p σ hvw)
  simpa only [Function.update_eq_self, weightedGram, Complex.ofReal_zero,
    Matrix.diagonal_zero, mul_zero, zero_mul, map_zero, add_zero] using hd

lemma groupEnergy_hasDerivAt_variance (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energy (weightedGram B (groupWeight h u loc p (Function.update σ v q))))
      ((1/2 : ℝ) * energyGradient (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupSecond h u loc p σ v))) (σ v) := by
  have hw : ∀ᶠ q in 𝓝 (σ v), ∀ i, 0 < groupWeight h u loc p (Function.update σ v q) i := by
    filter_upwards [eventually_gt_nhds (hσ v)] with q hq
    apply groupWeight_pos hh u loc p
    intro w
    by_cases hw : w = v
    · simpa [hw] using hq
    · simpa [hw] using hσ w
  have hd := energy_weightedGram_hasDerivAt B hw (groupWeight_hasDerivAt_variance h u loc p hσ v)
  simpa only [Function.update_eq_self, weightedGram_smul, map_smul, smul_eq_mul] using hd

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatWeights (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) : Three → ι → ℝ :=
  fun v i => weight h (u i) (p v) (σ v)

def heatArray (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) :=
  weightedArray A (heatWeights h u p σ)

def heatEnergy (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v : Three) : ℝ :=
  energy (starGram (heatArray A h u p σ) v)

def fixedBase (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v w : Three) :=
  if w = v then rowBare A g v else colBare A g v

def localGram (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupWeight h (fun a : BlockSpace ι => u a.2) Prod.fst p σ)

def localFirst (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w)

def localSecond (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupSecond h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w)

def heatFirst (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  energyGradient (localGram A h u p σ v w) (localFirst A h u p σ v w)

def heatPure (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  hessianCost (localGram A h u p σ v w) (localFirst A h u p σ v w) +
    energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)

def heatVariance (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  (1/2 : ℝ) * energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)

lemma heatEnergy_eq_localGram (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    heatEnergy A h u p σ v = energy (localGram A h u p σ v w) := by
  have hg : ∀ w i, 0 ≤ heatWeights h u p σ w i := fun w i =>
    (weight_pos hh (hσ w) (u i) (p w)).le
  unfold heatEnergy localGram fixedBase
  split_ifs
  · rw [heatArray, starGram_weightedArray A _ hg]
    rfl
  · rw [starGram, energy_gram_flip, heatArray, centerGram_weightedArray_padded A _ hg]
    rfl

lemma fixedBase_update_center (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) (q : ℝ) :
    fixedBase A (heatWeights h u (Function.update p w q) σ) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  unfold fixedBase
  split_ifs with hw
  · subst w
    apply rowBare_congr
    intro w hw i
    simp only [heatWeights, Function.update_of_ne hw]
  · apply colBare_congr
    intro i
    simp only [heatWeights, Function.update_of_ne (Ne.symm hw)]

lemma fixedBase_update_variance (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) (q : ℝ) :
    fixedBase A (heatWeights h u p (Function.update σ w q)) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  unfold fixedBase
  split_ifs with hw
  · subst w
    apply rowBare_congr
    intro w hw i
    simp only [heatWeights, Function.update_of_ne hw]
  · apply colBare_congr
    intro i
    simp only [heatWeights, Function.update_of_ne (Ne.symm hw)]

lemma heatEnergy_hasDerivAt_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatEnergy A h u (Function.update p w q) σ v)
      (heatFirst A h u p σ v w) (p w) := by
  have hd := groupEnergy_hasDerivAt_center (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  rw [heatEnergy_eq_localGram A hh u _ hσ v w]
  unfold localGram
  rw [fixedBase_update_center]

lemma heatFirst_hasDerivAt_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatFirst A h u (Function.update p w q) σ v w)
      (heatPure A h u p σ v w) (p w) := by
  have hd := groupEnergyFirst_hasDerivAt_center (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  unfold heatFirst localGram localFirst
  rw [fixedBase_update_center]

lemma heatEnergy_hasDerivAt_variance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatEnergy A h u p (Function.update σ w q) v)
      (heatVariance A h u p σ v w) (σ w) := by
  have hd := groupEnergy_hasDerivAt_variance (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (hσ w)] with q hq
  have hσ' : ∀ a, 0 < Function.update σ w q a := by
    intro a
    by_cases ha : a = w
    · simpa [ha] using hq
    · simpa [ha] using hσ a
  rw [heatEnergy_eq_localGram A hh u _ hσ' v w]
  unfold localGram
  rw [fixedBase_update_variance]

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hessianCost_zero_direction (P : Matrix ι ι ℂ) : hessianCost P 0 = 0 := by
  unfold hessianCost
  rw [rootCost_eq_of_solution (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P))
    (show sylv (CFC.sqrt P) 0 = 0 by simp [sylv])]
  simp [hsReal]

lemma hessianCost_singleBlock (P K : Matrix ι ι ℂ) (hP : P.PosSemidef) (v : Three)
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) :
    hessianCost (blockD (fun w => if w = v then P else 0))
      (blockD (fun w => if w = v then K else 0)) = hessianCost P K := by
  rw [hessianCost_blockD _ _ (fun w => by split_ifs; exact hP; exact Matrix.PosSemidef.zero)
    (fun w => by split_ifs; exact hsol; exact ⟨0, by simp [sylv]⟩)]
  apply (Finset.sum_eq_single v _ _).trans
  · simp only [ite_true]
  · intro w _ hw
    simp only [ite_eq_right hw, hessianCost_zero_direction]
  · simp

lemma rowStar_blockD_adjoint (W D : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar W v * blockD D * (rowStar W v)ᴴ =
      blockD (fun a => if a = v then
        ∑ w, triangleBlocks W v w * D w * (triangleBlocks W v w)ᴴ else 0) := by
  rw [rowStar_blocks]
  let R : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change blocks R * blocks (Matrix.diagonal D) * (blocks R)ᴴ = _
  rw [← blocks_star, ← blocks_mul, ← blocks_mul]
  unfold blockD
  congr 1
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose]
  change (∑ c, R a c * D c * (R b c)ᴴ) = _
  dsimp only [R]
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a
    subst b
    simp only [ite_true, Matrix.diagonal_apply_eq]
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, hb]
  · simp only [ite_eq_right ha, zero_mul, Finset.sum_const_zero]
    by_cases hab : a = b
    · subst b
      rw [Matrix.diagonal_apply_eq, ite_eq_right ha]
    · rw [Matrix.diagonal_apply_ne _ hab]

lemma rowStar_singleBlock_adjoint (W : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (v w : Three) :
    rowStar W v * blockD (fun a => if a = w then L else 0) * (rowStar W v)ᴴ =
      blockD (fun a => if a = v then triangleBlocks W v w * L * (triangleBlocks W v w)ᴴ else 0) := by
  rw [rowStar_blockD_adjoint]
  congr 1
  funext a
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma hessianCost_rowStar_singleBlock (W : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (v w : Three) :
    hessianCost (rowStar W v * (rowStar W v)ᴴ)
      (rowStar W v * blockD (fun a => if a = w then L else 0) * (rowStar W v)ᴴ) =
      hessianCost (centerGram W v) ((triangleBlocks W w v)ᴴ * L * triangleBlocks W w v) := by
  rw [rowStar_mul_adjoint, rowStar_singleBlock_adjoint]
  have hsol := sylv_solvable_mono
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((triangleBlocks W w v)ᴴ * triangleBlocks W w v)))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (centerGram W v))).isHermitian
    (sylv_solvable_inserted_gram (triangleBlocks W w v) L)
    (CFC.sqrt_le_sqrt _ _ (edgeGram_le_centerGram W v w))
  rw [← triangleBlocks_adj W w v, Matrix.conjTranspose_conjTranspose]
  exact hessianCost_singleBlock _ _ (centerGram_posSemidef W v) v hsol

lemma vertexRoot_insert (g d : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) * vertexRoot g =
      Matrix.diagonal (fun a => (g a.1 a.2 * d a.1 a.2 : ℂ)) := by
  have hb : blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) =
      Matrix.diagonal (fun a => (d a.1 a.2 : ℂ)) := by
    ext ⟨v,i⟩ ⟨w,j⟩
    by_cases hv : v = w <;> by_cases hi : i = j <;> simp [blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]
  rw [hb, vertexRoot, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext ⟨v,i⟩
  rw [mul_comm (Real.sqrt _ : ℂ) (d v i), mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hg v i)]
  push_cast
  ring

lemma rowBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (rowBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      starInsert (weightedArray A g) (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) v := by
  unfold starInsert
  rw [rowStar_weightedArray]
  unfold weightedGram rowBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.mul_assoc]

lemma colBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (colBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      rowStar (weightedArray A g) v *
        blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) *
        (rowStar (weightedArray A g) v)ᴴ := by
  rw [rowStar_weightedArray]
  unfold weightedGram colBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatCost (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) : ℝ :=
  hessianCost (localGram A h u p σ v w) (localFirst A h u p σ v w)

def heatMixed (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w z : Three) : ℝ :=
  hessianPair (localGram A h u p σ v w) (localFirst A h u p σ v w)
    (localFirst A h u p σ v z)

def heatScores (u : ι → ℝ) (p σ : Three → ℝ) : Three → Matrix ι ι ℂ :=
  fun w => Matrix.diagonal (fun i => (score (u i) (p w) (σ w) : ℂ))

lemma fixedBase_update_other (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (q : ℝ) :
    fixedBase A (heatWeights h u (Function.update p z q) σ) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  simp only [fixedBase, ite_eq_right hw]
  apply colBare_congr
  intro i
  simp only [heatWeights, Function.update_of_ne (Ne.symm hz)]

lemma heatFirst_hasDerivAt_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    HasDerivAt (fun q => heatFirst A h u (Function.update p z q) σ v w)
      (heatMixed A h u p σ v w z) (p z) := by
  have hd := groupEnergyFirst_hasDerivAt_other (colBare A (heatWeights h u p σ) v)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ hwz
  simp only [heatMixed, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  unfold heatFirst localGram localFirst
  rw [fixedBase_update_other A h u p σ hw hz q]
  simp only [fixedBase, ite_eq_right hw]

lemma two_heatMixed_le (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) :
    2 * heatMixed A h u p σ v w z ≤ heatCost A h u p σ v w + heatCost A h u p σ v z := by
  simp only [heatMixed, heatCost, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  exact two_hessianPair_weightedGram_le _ (groupWeight_pos hh _ _ p hσ) _ _

lemma localGram_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localGram A h u p σ v v = starGram (heatArray A h u p σ) v := by
  simp only [localGram, fixedBase, ite_true]
  exact (starGram_weightedArray A _ (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

lemma localGram_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    localGram A h u p σ v w = rowStar (heatArray A h u p σ) v *
      (rowStar (heatArray A h u p σ) v)ᴴ := by
  simp only [localGram, fixedBase, ite_eq_right hw]
  exact (centerGram_weightedArray_padded A _
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1) else 0) := by
  funext a
  simp only [groupFirst, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

lemma localFirst_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localFirst A h u p σ v v =
      starInsert (heatArray A h u p σ) (heatScores u p σ) v := by
  simp only [localFirst, fixedBase, ite_true, groupFirst_eq_insert]
  rw [rowBare_insert A (heatWeights h u p σ)
    (fun w i => if w = v then score (u i) (p w) (σ w) else 0)
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v]
  rw [starInsert_eq_insertRow, starInsert_eq_insertRow]
  simp only [heatArray, heatScores, ite_true]

lemma localFirst_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    localFirst A h u p σ v w = rowStar (heatArray A h u p σ) v *
      blockD (fun a => if a = w then heatScores u p σ w else 0) *
      (rowStar (heatArray A h u p σ) v)ᴴ := by
  simp only [localFirst, fixedBase, ite_eq_right hw, groupFirst_eq_insert]
  rw [colBare_insert A (heatWeights h u p σ)
    (fun a i => if a = w then score (u i) (p a) (σ a) else 0)
    (fun a i => (weight_pos hh (hσ a) (u i) (p a)).le) v]
  congr 2
  congr 1
  funext a
  by_cases ha : a = w
  · subst a
    simp [heatScores]
  · simp [ha]

lemma heatCost_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    heatCost A h u p σ v v = hessianCost (starGram (heatArray A h u p σ) v)
      (starInsert (heatArray A h u p σ) (heatScores u p σ) v) := by
  rw [heatCost, localGram_center A hh u p hσ, localFirst_center A hh u p hσ]

lemma heatCost_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    heatCost A h u p σ v w = hessianCost (centerGram (heatArray A h u p σ) v)
      ((triangleBlocks (heatArray A h u p σ) w v)ᴴ * heatScores u p σ w *
        triangleBlocks (heatArray A h u p σ) w v) := by
  rw [heatCost, localGram_other A hh u p hσ hw, localFirst_other A hh u p hσ hw]
  exact hessianCost_rowStar_singleBlock _ _ v w

lemma heatCost_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ)
    (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :
    0 ≤ heatCost A h u p σ v w := by
  unfold heatCost hessianCost rootCost
  apply mul_nonneg (by norm_num)
  by_cases hb : BddAbove (Set.range (variation (CFC.sqrt (localGram A h u p σ v w))
      (localFirst A h u p σ v w)))
  · apply le_csSup hb
    exact ⟨0, by simp [variation, penalty]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

lemma heatCost_neighbors (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (w : Three) :
    (∑ v, if v = w then 0 else heatCost A h u p σ v w) ≤
      Real.sqrt 2 * heatCost A h u p σ w w := by
  rw [heatCost_center A hh u p hσ]
  convert neighbor_comparison (heatArray A h u p σ) (heatScores u p σ) w using 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = w
  · subst v
    simp [triangleBlocks_diag, hessianCost_zero_direction]
  · rw [ite_eq_right hv, heatCost_other A hh u p hσ (Ne.symm hv)]

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma norm_sqrt_gram (R : Matrix ι ι ℂ) : ‖CFC.sqrt (Rᴴ * R)‖ = ‖R‖ := by
  rw [CFC.norm_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self R).nonneg]
  rw [show ‖Rᴴ * R‖ = ‖R‖ * ‖R‖ from CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg R)]

lemma norm_traceReal_le (X : Matrix ι ι ℂ) :
    ‖traceReal X‖ ≤ ‖traceRealCLM (ι := ι)‖ * ‖X‖ := by
  exact (traceRealCLM (ι := ι)).le_opNorm X

lemma norm_energy_gram_le (R : Matrix ι ι ℂ) :
    ‖energy (Rᴴ * R)‖ ≤ ‖traceRealCLM (ι := ι)‖ * ‖R‖^3 := by
  calc
    _ ≤ ‖traceRealCLM (ι := ι)‖ * ‖Rᴴ * R * CFC.sqrt (Rᴴ * R)‖ :=
      norm_traceReal_le _
    _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖Rᴴ * R‖ * ‖CFC.sqrt (Rᴴ * R)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_sqrt_gram,
        show ‖Rᴴ * R‖ = ‖R‖ * ‖R‖ from CStarRing.norm_star_mul_self]
      ring

lemma energy_gram_nonneg (R : Matrix ι ι ℂ) : 0 ≤ energy (Rᴴ * R) := by
  rw [energy_spectral (Matrix.posSemidef_conjTranspose_mul_self R)]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg ((Matrix.posSemidef_conjTranspose_mul_self R).eigenvalues_nonneg i)
    (Real.sqrt_nonneg _)

lemma norm_energyGradient_inserted_gram_le (R L : Matrix ι ι ℂ) :
    ‖energyGradient (Rᴴ * R) (Rᴴ * L * R)‖ ≤
      (3/2 : ℝ) * ‖traceRealCLM (ι := ι)‖ * ‖L‖ * ‖R‖^3 := by
  rw [energyGradient_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)]
  have hh : ‖traceReal (CFC.sqrt (Rᴴ * R) * (Rᴴ * L * R))‖ ≤
      ‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖)) := by
    calc
      _ ≤ ‖traceRealCLM (ι := ι)‖ * ‖CFC.sqrt (Rᴴ * R) * (Rᴴ * L * R)‖ :=
        norm_traceReal_le _
      _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖CFC.sqrt (Rᴴ * R)‖ * ‖Rᴴ * L * R‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖)) := by
        rw [norm_sqrt_gram]
        gcongr
        calc
          _ ≤ ‖Rᴴ * L‖ * ‖R‖ := norm_mul_le _ _
          _ ≤ (‖Rᴴ‖ * ‖L‖) * ‖R‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ = _ := by rw [show ‖Rᴴ‖ = ‖R‖ from norm_star R]
  calc
    _ ≤ (3/2 : ℝ) * (‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖))) := by gcongr
    _ = _ := by ring

lemma hessianCost_nonneg (P K : Matrix ι ι ℂ) : 0 ≤ hessianCost P K := by
  unfold hessianCost rootCost
  apply mul_nonneg (by norm_num)
  by_cases hb : BddAbove (Set.range (variation (CFC.sqrt P) K))
  · apply le_csSup hb
    exact ⟨0, by simp [variation, penalty]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

lemma norm_hessianCost_inserted_gram_le (R L : Matrix ι ι ℂ) (hL : L.IsHermitian) :
    ‖hessianCost (Rᴴ * R) (Rᴴ * L * R)‖ ≤
      (3/4 : ℝ) * ‖traceRealCLM (ι := ι)‖ * ‖L‖^2 * ‖R‖^3 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hessianCost_nonneg _ _)]
  calc
    _ ≤ (3/4 : ℝ) * ‖L‖^2 * energy (Rᴴ * R) := hessianCost_inserted_gram_le R L hL
    _ ≤ (3/4 : ℝ) * ‖L‖^2 * (‖traceRealCLM (ι := ι)‖ * ‖R‖^3) := by
      gcongr
      exact (le_abs_self _).trans (norm_energy_gram_le R)
    _ = _ := by ring

def entryNormConstant (ι : Type uι) [Fintype ι] [DecidableEq ι] : ℝ :=
  ∑ i : ι, ∑ j : ι, ‖(Matrix.single i j (1 : ℂ))‖

lemma entryNormConstant_nonneg : 0 ≤ entryNormConstant ι := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))

lemma norm_matrix_le_entries (R : Matrix ι ι ℂ) {M : ℝ} (hM : ∀ i j, ‖R i j‖ ≤ M) :
    ‖R‖ ≤ entryNormConstant ι * M := by
  calc
    _ = ‖∑ i, ∑ j, Matrix.single i j (R i j)‖ := congrArg norm (Matrix.matrix_eq_sum_single R)
    _ ≤ ∑ i, ‖∑ j, Matrix.single i j (R i j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖Matrix.single i j (R i j)‖ := Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i : ι, ∑ j : ι, ‖Matrix.single i j (1 : ℂ)‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [show Matrix.single i j (R i j) = (R i j) • Matrix.single i j (1 : ℂ) by
        rw [Matrix.smul_single]; simp, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)
    _ = _ := by simp [entryNormConstant, Finset.sum_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatCarrier (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) :=
  if w = v then rowStar (heatArray A h u p σ) v else (rowStar (heatArray A h u p σ) v)ᴴ

def heatMask (d : Three → ι → ℝ) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  blockD (fun w => Matrix.diagonal (fun i => (d w i : ℂ)))

omit [Fintype ι] in
lemma heatMask_eq_diagonal (d : Three → ι → ℝ) :
    heatMask d = Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2 : ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v = w <;> by_cases hi : i = j <;>
    simp [heatMask, blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]

omit [Fintype ι] in
lemma heatMask_isHermitian (d : Three → ι → ℝ) : (heatMask d).IsHermitian := by
  rw [heatMask_eq_diagonal]
  exact Matrix.isHermitian_diagonal_iff.mpr (fun a => by change star (d a.1 a.2 : ℂ) = _; exact Complex.conj_ofReal _)

lemma heatCarrier_norm (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) :
    ‖heatCarrier A h u p σ v w‖ = ‖rowStar (heatArray A h u p σ) v‖ := by
  unfold heatCarrier
  split_ifs
  · rfl
  · exact norm_star (rowStar (heatArray A h u p σ) v)

lemma localGram_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localGram A h u p σ v w =
      (heatCarrier A h u p σ v w)ᴴ * heatCarrier A h u p σ v w := by
  unfold heatCarrier
  split_ifs with hw
  · subst w
    exact localGram_center A hh u p hσ v
  · rw [Matrix.conjTranspose_conjTranspose]
    exact localGram_other A hh u p hσ hw

lemma localInsert_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    (v w : Three) (d : Three → ι → ℝ) :
    weightedGram (fixedBase A (heatWeights h u p σ) v w)
      (fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 * d a.1 a.2) =
        (heatCarrier A h u p σ v w)ᴴ * heatMask d * heatCarrier A h u p σ v w := by
  simp only [fixedBase, heatCarrier]
  split_ifs
  · exact rowBare_insert A _ d (fun a j => (weight_pos hh (hσ a) (u j) (p a)).le) v
  · rw [Matrix.conjTranspose_conjTranspose]
    exact colBare_insert A _ d (fun a j => (weight_pos hh (hσ a) (u j) (p a)).le) v

lemma localFirst_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localFirst A h u p σ v w = (heatCarrier A h u p σ v w)ᴴ *
      heatMask (fun a i => if a = w then score (u i) (p a) (σ a) else 0) *
        heatCarrier A h u p σ v w := by
  rw [localFirst, groupFirst_eq_insert]
  exact localInsert_eq_carrier A hh u p hσ v w
    (fun a i => if a = w then score (u i) (p a) (σ a) else 0)

omit [Fintype ι] [DecidableEq ι] in
lemma groupSecond_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupSecond h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1)^2 - (σ a.1)⁻¹ else 0) := by
  funext a
  simp only [groupSecond, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

lemma localSecond_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localSecond A h u p σ v w = (heatCarrier A h u p σ v w)ᴴ *
      heatMask (fun a i => if a = w then score (u i) (p a) (σ a)^2 - (σ a)⁻¹ else 0) *
        heatCarrier A h u p σ v w := by
  rw [localSecond, groupSecond_eq_insert]
  exact localInsert_eq_carrier A hh u p hσ v w
    (fun a i => if a = w then score (u i) (p a) (σ a)^2 - (σ a)⁻¹ else 0)

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section

namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma gaussian_exponent_le {σ b : ℝ} (hσ : 0 < σ) (hσb : σ ≤ b) (u p : ℝ) :
    -(u-p)^2 / (2*σ) ≤ u^2/(2*b) - p^2/(4*b) := by
  have hb : 0 < b := hσ.trans_le hσb
  calc
    _ ≤ -(u-p)^2 / (2*b) := by
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))
    _ = (-2*(u-p)^2)/(4*b) := by field_simp; ring
    _ ≤ (2*u^2-p^2)/(4*b) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (p - 2*u)]
    _ = _ := by field_simp; ring

lemma weight_le_gaussian {h a σ b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (haσ : a ≤ σ) (hσb : σ ≤ b) (u p : ℝ) :
    weight h u p σ ≤
      (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b))) *
        Real.exp (-p^2/(4*b)) := by
  have hσ := ha.trans_le haσ
  have hn : (Real.sqrt (2*Real.pi*σ))⁻¹ ≤ (Real.sqrt (2*Real.pi*a))⁻¹ := by
    simp only [← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    exact Real.sqrt_le_sqrt (by gcongr)
  have he := Real.exp_le_exp.mpr (gaussian_exponent_le hσ hσb u p)
  unfold weight density
  calc
    _ ≤ h * ((Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b)-p^2/(4*b))) := by
      gcongr
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf

lemma rootWeight_le_gaussian {h a σ b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (haσ : a ≤ σ) (hσb : σ ≤ b) (u p : ℝ) :
    Real.sqrt (weight h u p σ) ≤
      Real.sqrt (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b))) *
        Real.exp (-p^2/(8*b)) := by
  have hh' := Real.sqrt_le_sqrt (weight_le_gaussian hh ha haσ hσb u p)
  rw [Real.sqrt_mul (by positivity), ← Real.exp_half] at hh'
  convert! hh' using 1
  congr 2
  field_simp
  ring

lemma score_le_linear {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ) (u p : ℝ) :
    |score u p σ| ≤ (|u|+|p|)/a := by
  unfold score
  rw [abs_div, abs_of_pos (ha.trans_le haσ)]
  exact (div_le_div_of_nonneg_right (by simpa using abs_sub_le u 0 p) (ha.trans_le haσ).le).trans
    (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) ha haσ)

lemma integrable_one_add_sq_sq_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (1+x^2)^2 * Real.exp (-b*x^2)) := by
  have h0 : Integrable (fun x : ℝ => Real.exp (-b*x^2)) := by
    simpa using (integrable_rpow_mul_exp_neg_mul_sq hb (s := 0) (by norm_num))
  have h2 : Integrable (fun x : ℝ => x^2 * Real.exp (-b*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (s := (2:ℕ)) (by norm_num))
  have h4 : Integrable (fun x : ℝ => x^4 * Real.exp (-b*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (s := (4:ℕ)) (by norm_num))
  convert! h0.add ((h2.const_mul 2).add h4) using 1
  ext x
  dsimp
  ring

def planeGaussian (b : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-b*(z.1^2 + z.2^2))

def planePoly (z : ℝ × ℝ) : ℝ := (1+z.1^2) * (1+z.2^2)

lemma planeGaussian_pos (b : ℝ) (z : ℝ × ℝ) : 0 < planeGaussian b z := Real.exp_pos _
lemma planeGaussian_le_one {b : ℝ} (hb : 0 ≤ b) (z : ℝ × ℝ) : planeGaussian b z ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma one_le_planePoly (z : ℝ × ℝ) : 1 ≤ planePoly z := by
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]
lemma planePoly_nonneg (z : ℝ × ℝ) : 0 ≤ planePoly z := (by norm_num : (0:ℝ) ≤ 1).trans (one_le_planePoly z)

lemma integrable_planePoly_sq_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun z => planePoly z ^2 * planeGaussian b z) := by
  have hh := (integrable_one_add_sq_sq_gaussian hb).mul_prod (integrable_one_add_sq_sq_gaussian hb)
  convert! hh using 1
  ext z
  simp only [planePoly, planeGaussian]
  rw [show -b * (z.1^2+z.2^2) = -b*z.1^2 + -b*z.2^2 by ring, Real.exp_add]
  ring

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

def chart (i : Three) (d : ℝ) (z : ℝ × ℝ) : Three → ℝ :=
  if i = 0 then ![d-z.1-z.2, z.1, z.2]
  else if i = 1 then ![z.1, d-z.1-z.2, z.2]
  else ![z.1, z.2, d-z.1-z.2]

lemma chart_continuous (i : Three) : Continuous (fun q : ℝ × (ℝ × ℝ) => chart i q.1 q.2) := by
  unfold chart
  split_ifs <;> fun_prop

lemma chart_hasDerivAt (i : Three) (d : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun e => chart i e z i) 1 d := by
  have he : (fun e => chart i e z i) = (fun e => e-z.1-z.2) := by
    funext e
    fin_cases i <;> simp [chart]
  rw [he]
  exact ((hasDerivAt_id d).sub_const z.1).sub_const z.2

def chartReflection (d : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1, d-z.1-z.2)
  invFun z := (z.1, d-z.1-z.2)
  left_inv z := by exact Prod.ext rfl (by dsimp; ring)
  right_inv z := by exact Prod.ext rfl (by dsimp; ring)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma chartReflection_preserving (d : ℝ) : MeasurePreserving (chartReflection d) := by
  exact (MeasurePreserving.id volume).skew_product
    (g := fun x y : ℝ => d-x-y) (by fun_prop)
    (Filter.Eventually.of_forall (fun x => (volume.measurePreserving_sub_left (d-x)).map_eq))

lemma swap_preserving : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
  ⟨measurable_swap, Measure.prod_swap⟩

def chartChange (i : Three) (d : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  if i = 0 then (chartReflection d).trans (Homeomorph.prodComm ℝ ℝ)
  else if i = 1 then chartReflection d
  else Homeomorph.refl _

lemma chartChange_preserving (i : Three) (d : ℝ) : MeasurePreserving (chartChange i d) := by
  unfold chartChange
  split_ifs
  · exact swap_preserving.comp (chartReflection_preserving d)
  · exact chartReflection_preserving d
  · exact MeasurePreserving.id volume

lemma chartChange_eq (i : Three) (d : ℝ) (z : ℝ × ℝ) :
    chart i d z = chart 2 d (chartChange i d z) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [chart, chartChange, chartReflection]
  all_goals ring

lemma integral_chart_eq (i j : Three) (d : ℝ) (f : (Three → ℝ) → ℝ) :
    (∫ z : ℝ × ℝ, f (chart i d z)) = ∫ z : ℝ × ℝ, f (chart j d z) := by
  have hi k : (∫ z : ℝ × ℝ, f (chart k d z)) = ∫ z : ℝ × ℝ, f (chart 2 d z) := by
    simp_rw [chartChange_eq k d]
    exact (chartChange_preserving k d).integral_comp (chartChange k d).measurableEmbedding
      (fun z : ℝ × ℝ => f (chart 2 d z))
  exact (hi i).trans (hi j).symm

lemma chart_pair_bound {D : ℝ} {d : ℝ} (hd : |d| ≤ D) (i j k : Three) (hjk : j ≠ k)
    (z : ℝ × ℝ) : z.1^2+z.2^2 ≤ 4*((chart i d z j)^2+(chart i d z k)^2)+3*D^2 := by
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hd2 : d^2 ≤ D^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).2 hd
  have hgen (x y : ℝ) : x^2+y^2+(d-x-y)^2 ≤ 4*(x^2+y^2)+3*D^2 := by
    nlinarith [sq_nonneg (x-y), sq_nonneg (d+x), sq_nonneg (d+y)]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hjk
  all_goals norm_num [chart]
  all_goals nlinarith [hgen z.1 z.2, hgen (d-z.1-z.2) z.1, hgen (d-z.1-z.2) z.2,
    sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (d-z.1-z.2)]

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma abs_le_one_add_sq (x : ℝ) : |x| ≤ 1+x^2 := by
  nlinarith [sq_nonneg (|x|-1), sq_abs x]

lemma planePoly_ge_first (z : ℝ × ℝ) : |z.1| ≤ planePoly z := by
  have := abs_le_one_add_sq z.1
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]

lemma planePoly_ge_second (z : ℝ × ℝ) : |z.2| ≤ planePoly z := by
  have := abs_le_one_add_sq z.2
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]

lemma chart_abs_bound {D d : ℝ} (hd : |d| ≤ D) (i w : Three) (z : ℝ × ℝ) :
    |chart i d z w| ≤ (D+2) * planePoly z := by
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hP := one_le_planePoly z
  have hx := planePoly_ge_first z
  have hy := planePoly_ge_second z
  have hDP : D ≤ D * planePoly z := by nlinarith
  have hab : |d-z.1-z.2| ≤ |d|+|z.1|+|z.2| := by
    calc
      _ ≤ |d-z.1| + |z.2| := by simpa using abs_sub_le (d-z.1) 0 z.2
      _ ≤ _ := by simpa using add_le_add_right (abs_sub_le d 0 z.1) (abs z.2)
  fin_cases i <;> fin_cases w <;> simp [chart] <;> nlinarith

lemma endpoint_gaussian_bound {D d b : ℝ} (hb : 0 < b) (hd : |d| ≤ D)
    (i j k : Three) (hjk : j ≠ k) (z : ℝ × ℝ) :
    Real.exp (-((chart i d z j)^2+(chart i d z k)^2)/(8*b)) ≤
      Real.exp (3*D^2/(32*b)) * planeGaussian (1/(32*b)) z := by
  have hh := chart_pair_bound hd i j k hjk z
  rw [planeGaussian, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : -((chart i d z j)^2+(chart i d z k)^2)/(8*b) ≤
      (3*D^2-(z.1^2+z.2^2))/(32*b) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 8*b) (by positivity : 0 < 32*b)]
    nlinarith
  convert! he using 1
  ring

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def rootCoefficient (h a b u : ℝ) : ℝ :=
  Real.sqrt (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b)))

omit [DecidableEq ι] in
lemma exists_heatArray_gaussian_bound (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (_hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Three → ℝ) (i : Three) (d : ℝ) (z : ℝ × ℝ),
      |d| ≤ D → p = chart i d z → ∀ (σ : Three → ℝ),
      (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → ∀ v k l,
      ‖heatArray A h u p σ v k l‖ ≤ C * planeGaussian (1/(32*b)) z := by
  let K : Three × ι × ι → ℝ := fun t => rootCoefficient h a b (u t.2.1) *
    ‖A t.1 t.2.1 t.2.2‖ * rootCoefficient h a b (u t.2.2)
  have hK t : 0 ≤ K t := by dsimp [K, rootCoefficient]; positivity
  let C := (∑ t, K t) * Real.exp (3*D^2/(32*b))
  refine ⟨C, mul_nonneg (Finset.sum_nonneg (fun t _ => hK t)) (Real.exp_pos _).le, ?_⟩
  intro p i d z hd hp σ hσa hσb v k l
  subst p
  have hb := ha.trans_le hab
  have hv : v ≠ v+1 := by fin_cases v <;> decide
  have hleft := rootWeight_le_gaussian hh.le ha (hσa v) (hσb v) (u k) (chart i d z v)
  have hright := rootWeight_le_gaussian hh.le ha (hσa (v+1)) (hσb (v+1)) (u l) (chart i d z (v+1))
  have hc : K (v,k,l) ≤ ∑ t, K t := Finset.single_le_sum (fun t _ => hK t) (Finset.mem_univ _)
  calc
    _ = Real.sqrt (weight h (u k) (chart i d z v) (σ v)) * ‖A v k l‖ *
        Real.sqrt (weight h (u l) (chart i d z (v+1)) (σ (v+1))) := by
      simp only [heatArray, weightedArray, heatWeights, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ (rootCoefficient h a b (u k) * Real.exp (-(chart i d z v)^2/(8*b))) * ‖A v k l‖ *
        (rootCoefficient h a b (u l) * Real.exp (-(chart i d z (v+1))^2/(8*b))) := by
      dsimp only [rootCoefficient]
      gcongr
    _ = K (v,k,l) * Real.exp (-((chart i d z v)^2+(chart i d z (v+1))^2)/(8*b)) := by
      dsimp [K]
      rw [show -((chart i d z v)^2+(chart i d z (v+1))^2)/(8*b) =
        -(chart i d z v)^2/(8*b) + -(chart i d z (v+1))^2/(8*b) by ring, Real.exp_add]
      ring
    _ ≤ (∑ t, K t) * (Real.exp (3*D^2/(32*b)) * planeGaussian (1/(32*b)) z) := by
      exact mul_le_mul hc (endpoint_gaussian_bound hb hd i v (v+1) hv z)
        (Real.exp_pos _).le (Finset.sum_nonneg (fun t _ => hK t))
    _ = _ := by dsimp [C]; ring

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_entry_bound (W : Three → Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hW : ∀ v i j, ‖W v i j‖ ≤ M) (a b : Three) (i j : ι) :
    ‖triangleBlocks W a b i j‖ ≤ M := by
  fin_cases a <;> fin_cases b <;> simp [triangleBlocks, Matrix.conjTranspose_apply]
  all_goals first | exact hM | exact hW _ _ _

lemma norm_rowStar_le_bound (W : Three → Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hW : ∀ v i j, ‖W v i j‖ ≤ M) (v : Three) :
    ‖rowStar W v‖ ≤ entryNormConstant (BlockSpace ι) * M := by
  apply norm_matrix_le_entries
  intro a b
  rw [rowStar_apply]
  split_ifs
  · exact triangleBlocks_entry_bound W hM hW _ _ _ _
  · simpa using hM

lemma exists_heatCarrier_gaussian_bound (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D →
      ∀ (σ : Three → ℝ), (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → ∀ v w,
      ‖heatCarrier A h u (chart i d z) σ v w‖ ≤ C * planeGaussian (1/(32*b)) z := by
  obtain ⟨C,hC,hbound⟩ := exists_heatArray_gaussian_bound A hh ha hab hD u
  refine ⟨entryNormConstant (BlockSpace ι) * C, mul_nonneg entryNormConstant_nonneg hC, ?_⟩
  intro i d z hd σ hσa hσb v w
  rw [heatCarrier_norm]
  calc
    _ ≤ entryNormConstant (BlockSpace ι) * (C * planeGaussian (1/(32*b)) z) :=
      norm_rowStar_le_bound _ (mul_nonneg hC (planeGaussian_pos _ _).le)
        (hbound _ i d z hd rfl σ hσa hσb) v
    _ = _ := by ring

lemma norm_heatMask_le (r : Three → ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hr : ∀ w j, |r w j| ≤ M) : ‖heatMask r‖ ≤ entryNormConstant (BlockSpace ι) * M := by
  apply norm_matrix_le_entries
  intro a b
  rw [heatMask_eq_diagonal]
  by_cases hab : a = b
  · subst b
    simpa only [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs] using hr a.1 a.2
  · simpa only [Matrix.diagonal_apply_ne _ hab, norm_zero] using hM

omit [DecidableEq ι] in
lemma exists_score_polynomial_bound (u : ι → ℝ) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D →
      ∀ (σ : Three → ℝ), (∀ w, a ≤ σ w) → ∀ w j,
        |score (u j) (chart i d z w) (σ w)| ≤ C * planePoly z ∧
        |score (u j) (chart i d z w) (σ w)^2 - (σ w)⁻¹| ≤ (C^2+a⁻¹) * planePoly z^2 := by
  let U := ∑ j, |u j|
  have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => abs_nonneg (u j))
  have hu j : |u j| ≤ U := Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ j)
  let C := (U+D+2)/a
  have hC : 0 ≤ C := div_nonneg (by linarith) ha.le
  refine ⟨C,hC,?_⟩
  intro i d z hd σ hσ w j
  have hP := one_le_planePoly z
  have hpn := planePoly_nonneg z
  have hsp : 0 < σ w := ha.trans_le (hσ w)
  have hs : |score (u j) (chart i d z w) (σ w)| ≤ C * planePoly z := by
    calc
      _ ≤ (|u j|+|chart i d z w|)/a := score_le_linear ha (hσ w) _ _
      _ ≤ (U+(D+2)*planePoly z)/a := by gcongr; exacts [hu j, chart_abs_bound hd i w z]
      _ ≤ C * planePoly z := by
        dsimp [C]
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha]
        nlinarith
  have hinv : (σ w)⁻¹ ≤ a⁻¹ := by
    simp only [← one_div]
    exact one_div_le_one_div_of_le ha (hσ w)
  have hs2 : score (u j) (chart i d z w) (σ w)^2 ≤ C^2 * planePoly z^2 := by
    have := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hpn)).2 hs
    simpa only [sq_abs, mul_pow] using this
  refine ⟨hs,?_⟩
  calc
    _ ≤ score (u j) (chart i d z w) (σ w)^2 + (σ w)⁻¹ := by
      calc
        _ ≤ |score (u j) (chart i d z w) (σ w)^2| + |(σ w)⁻¹| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (inv_pos.mpr hsp)]
    _ ≤ C^2 * planePoly z^2 + a⁻¹ := add_le_add hs2 hinv
    _ ≤ _ := by nlinarith [inv_pos.mpr ha, sq_nonneg (planePoly z-1)]

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma two_abs_hessianPairPD_le {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    2 * |hessianPairPD hP K L| ≤ hessianCost P K + hessianCost P L := by
  have hp := two_hessianPairPD_le hP K L
  have hn := two_hessianPairPD_le hP (-K) L
  have hneg : hessianPairPD hP (-K) L = -hessianPairPD hP K L := by
    simp [hessianPairPD, hsReal, traceReal]
  have hc : hessianCost P (-K) = hessianCost P K := by
    rw [← hessianPairPD_self hP, ← hessianPairPD_self hP]
    simp [hessianPairPD, hsReal, traceReal]
  rw [hneg, hc] at hn
  rcases le_total 0 (hessianPairPD hP K L) with hh | hh
  · rwa [abs_of_nonneg hh]
  · rw [abs_of_nonpos hh]
    exact hn

lemma two_abs_hessianPair_le_of_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hLQ : L * Q = 0) (hQL : Q * L = 0) (hPD : (P + Q).PosDef) :
    2 * |hessianPair P K L| ≤ hessianCost P K + hessianCost P L := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hLQ hQL hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hLQ hQL hPD,
    hessianPair_eq_PD hPD]
  exact two_abs_hessianPairPD_le hPD K L

lemma two_abs_hessianPair_weightedGram_le (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k l : ι → ℝ) :
    2 * |hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B l)| ≤
      hessianCost (weightedGram B w) (weightedGram B k) +
      hessianCost (weightedGram B w) (weightedGram B l) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  have hLQ := weightedGram_mul_eq_zero B Q l hBQ
  exact two_abs_hessianPair_le_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hLQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B l) hQ.isHermitian hLQ) hPD
end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
lemma two_abs_heatMixed_le (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) :
    2 * |heatMixed A h u p σ v w z| ≤ heatCost A h u p σ v w + heatCost A h u p σ v z := by
  simp only [heatMixed, heatCost, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  exact two_abs_hessianPair_weightedGram_le _ (groupWeight_pos hh _ _ p hσ) _ _
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

structure HeatAtBounds (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (M : ℝ) : Prop where
  energy : ∀ v, ‖heatEnergy A h u p σ v‖ ≤ M
  first : ∀ v w, ‖heatFirst A h u p σ v w‖ ≤ M
  pure : ∀ v w, ‖heatPure A h u p σ v w‖ ≤ M
  variance : ∀ v w, ‖heatVariance A h u p σ v w‖ ≤ M
  cost : ∀ v w, ‖heatCost A h u p σ v w‖ ≤ M
  mixed : ∀ v w z, w ≠ v → z ≠ v → ‖heatMixed A h u p σ v w z‖ ≤ M

lemma heatAtBounds_of_norms (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {E L Q : ℝ} (hE : 0 ≤ E) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hr : ∀ v w, ‖heatCarrier A h u p σ v w‖^3 ≤ E)
    (hl : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a) else 0)‖ ≤ L)
    (hq : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a)^2-(σ a)⁻¹ else 0)‖ ≤ Q) :
    HeatAtBounds A h u p σ
      (‖traceRealCLM (ι := BlockSpace ι)‖ * E * (1 + (3/2:ℝ)*L + (3/4:ℝ)*L^2 + (3/2:ℝ)*Q)) := by
  let N := ‖traceRealCLM (ι := BlockSpace ι)‖
  have hN : 0 ≤ N := norm_nonneg _
  have he v : ‖heatEnergy A h u p σ v‖ ≤ N * E := by
    rw [heatEnergy_eq_localGram A hh u p hσ v v, localGram_eq_carrier A hh u p hσ v v]
    exact (norm_energy_gram_le _).trans (mul_le_mul_of_nonneg_left (hr v v) hN)
  have hf v w : ‖heatFirst A h u p σ v w‖ ≤ (3/2:ℝ)*N*L*E := by
    simp only [heatFirst, localGram_eq_carrier A hh u p hσ, localFirst_eq_carrier A hh u p hσ]
    apply (norm_energyGradient_inserted_gram_le _ _).trans
    gcongr
    · exact hl w
    · exact hr v w
  have hg v w : ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ ≤
      (3/2:ℝ)*N*Q*E := by
    simp only [localGram_eq_carrier A hh u p hσ, localSecond_eq_carrier A hh u p hσ]
    apply (norm_energyGradient_inserted_gram_le _ _).trans
    gcongr
    · exact hq w
    · exact hr v w
  have hc v w : ‖heatCost A h u p σ v w‖ ≤ (3/4:ℝ)*N*L^2*E := by
    simp only [heatCost, localGram_eq_carrier A hh u p hσ, localFirst_eq_carrier A hh u p hσ]
    apply (norm_hessianCost_inserted_gram_le _ _ (heatMask_isHermitian _)).trans
    gcongr
    · exact hl w
    · exact hr v w
  have hNE := mul_nonneg hN hE
  have hNLE := mul_nonneg (mul_nonneg hN hL) hE
  have hNL2E := mul_nonneg (mul_nonneg hN (sq_nonneg L)) hE
  have hNQE := mul_nonneg (mul_nonneg hN hQ) hE
  constructor
  · intro v; dsimp only [N] at *; nlinarith [he v]
  · intro v w; dsimp only [N] at *; nlinarith [hf v w]
  · intro v w
    have hp : ‖heatPure A h u p σ v w‖ ≤ ‖heatCost A h u p σ v w‖ +
        ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ := norm_add_le _ _
    dsimp only [N] at *; nlinarith [hc v w, hg v w]
  · intro v w
    have hv : ‖heatVariance A h u p σ v w‖ = (1/2:ℝ) *
        ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ := by
      simp [heatVariance, norm_mul]
    rw [hv]; dsimp only [N] at *; nlinarith [hg v w]
  · intro v w; dsimp only [N] at *; nlinarith [hc v w]
  · intro v w z hw hz
    have hx := two_abs_heatMixed_le A hh u p hσ hw hz
    rw [← Real.norm_eq_abs] at hx
    have hwle := le_abs_self (heatCost A h u p σ v w)
    have hzle := le_abs_self (heatCost A h u p σ v z)
    rw [← Real.norm_eq_abs] at hwle hzle
    dsimp only [N] at *; nlinarith [hc v w, hc v z]

lemma HeatAtBounds.mono {A : Three → Matrix ι ι ℂ} {h : ℝ} {u : ι → ℝ}
    {p σ : Three → ℝ} {M N : ℝ} (hb : HeatAtBounds A h u p σ M) (hMN : M ≤ N) :
    HeatAtBounds A h u p σ N := by
  exact ⟨fun v => (hb.energy v).trans hMN, fun v w => (hb.first v w).trans hMN,
    fun v w => (hb.pure v w).trans hMN, fun v w => (hb.variance v w).trans hMN,
    fun v w => (hb.cost v w).trans hMN, fun v w z hw hz => (hb.mixed v w z hw hz).trans hMN⟩

lemma exists_heat_uniform_majorant (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ B : (ℝ × ℝ) → ℝ, Integrable B ∧ (∀ z, 0 ≤ B z) ∧
      ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D → ∀ (σ : Three → ℝ),
      (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → HeatAtBounds A h u (chart i d z) σ (B z) := by
  obtain ⟨R,hR,hRB⟩ := exists_heatCarrier_gaussian_bound A hh ha hab hD u
  obtain ⟨S,hS,hSB⟩ := exists_score_polynomial_bound u ha hD
  let T := entryNormConstant (BlockSpace ι)
  let L := T*S
  let Q := T*(S^2+a⁻¹)
  have hT : 0 ≤ T := entryNormConstant_nonneg
  have hL : 0 ≤ L := mul_nonneg hT hS
  have hQ : 0 ≤ Q := mul_nonneg hT (add_nonneg (sq_nonneg _) (inv_nonneg.mpr ha.le))
  let N := ‖traceRealCLM (ι := BlockSpace ι)‖
  let C := N * R^3 * (1+(3/2:ℝ)*L+(3/4:ℝ)*L^2+(3/2:ℝ)*Q)
  have hN : 0 ≤ N := norm_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbpos : 0 < b := ha.trans_le hab
  have hb : 0 < 1/(32*b) := by positivity
  refine ⟨fun z => C * (planePoly z^2 * planeGaussian (1/(32*b)) z),
    (integrable_planePoly_sq_gaussian hb).const_mul C,
    fun z => mul_nonneg hC (mul_nonneg (sq_nonneg _) (planeGaussian_pos _ _).le), ?_⟩
  intro i d z hd σ hσa hσb
  have hσ : ∀ w, 0 < σ w := fun w => ha.trans_le (hσa w)
  let P := planePoly z
  let G := planeGaussian (1/(32*b)) z
  have hP : 0 ≤ P := planePoly_nonneg z
  have hP1 : 1 ≤ P := one_le_planePoly z
  have hG : 0 ≤ G := (planeGaussian_pos _ _).le
  have hG1 : G ≤ 1 := planeGaussian_le_one hb.le z
  have hr v w : ‖heatCarrier A h u (chart i d z) σ v w‖^3 ≤ R^3 * G := by
    calc
      _ ≤ (R*G)^3 := pow_le_pow_left₀ (norm_nonneg _) (hRB i d z hd σ hσa hσb v w) 3
      _ = R^3*G^3 := mul_pow _ _ _
      _ ≤ R^3 * G := by gcongr; nlinarith [mul_nonneg hG (sub_nonneg.mpr hG1)]
  have hl w : ‖heatMask (fun a j => if a = w then score (u j) (chart i d z a) (σ a) else 0)‖ ≤ L*P := by
    calc
      _ ≤ T*(S*P) := norm_heatMask_le _ (mul_nonneg hS hP) (by
        intro a j; split_ifs
        · exact (hSB i d z hd σ hσa a j).1
        · simpa using mul_nonneg hS hP)
      _ = _ := by dsimp [L]; ring
  have hq w : ‖heatMask (fun a j => if a = w then score (u j) (chart i d z a) (σ a)^2-(σ a)⁻¹ else 0)‖ ≤ Q*P^2 := by
    calc
      _ ≤ T*((S^2+a⁻¹)*P^2) := norm_heatMask_le _ (by positivity) (by
        intro k j; split_ifs
        · exact (hSB i d z hd σ hσa k j).2
        · simpa using (show 0 ≤ (S^2+a⁻¹)*P^2 by positivity))
      _ = _ := by dsimp [Q]; ring
  apply (heatAtBounds_of_norms A hh u (chart i d z) hσ
    (mul_nonneg (pow_nonneg hR _) hG) (mul_nonneg hL hP)
    (mul_nonneg hQ (sq_nonneg P)) hr hl hq).mono
  change N*(R^3*G)*(1+(3/2:ℝ)*(L*P)+(3/4:ℝ)*(L*P)^2+(3/2:ℝ)*(Q*P^2)) ≤ C*(P^2*G)
  have hP2 : P ≤ P^2 := by nlinarith
  have h1P2 : 1 ≤ P^2 := le_trans hP1 hP2
  calc
    _ = N*R^3*G*(1+(3/2:ℝ)*L*P+(3/4:ℝ)*L^2*P^2+(3/2:ℝ)*Q*P^2) := by ring
    _ ≤ N*R^3*G*(P^2+(3/2:ℝ)*L*P^2+(3/4:ℝ)*L^2*P^2+(3/2:ℝ)*Q*P^2) := by gcongr
    _ = _ := by dsimp [C]; ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter MeasureTheory
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def gramGradientAt (R P : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (3 : ℝ) • traceRealCLM.comp ((ContinuousLinearMap.mul ℝ _) ((R * CFC.sqrt P)ᴴ))

@[simp] lemma gramGradientAt_apply (R P D : Matrix ι ι ℂ) :
    gramGradientAt R P D = 3 * hsReal (R * CFC.sqrt P) D := rfl

lemma regularized_energyGram_hasFDerivAt (R : Matrix ι ι ℂ) {η : ℝ} (hη : 0 < η) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (regularize (Xᴴ * X) η))
      (gramGradientAt R (regularize (Rᴴ * R) η)) R := by
  have hg := (((hasFDerivAt_id R (𝕜 := ℝ)).star).mul' (hasFDerivAt_id R)).add_const
    (η • (1 : Matrix ι ι ℂ))
  have hp := regularize_posDef (Matrix.posSemidef_conjTranspose_mul_self R) hη
  have hn : ∀ᶠ X : Matrix ι ι ℂ in 𝓝 R, 0 ≤ regularize (Xᴴ * X) η :=
    Eventually.of_forall fun X =>
      (regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X) hη.le).nonneg
  have hh := (energy_hasFDerivWithinAt hp).comp_hasFDerivAt R hg hn
  convert! hh using 1
  ext D
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, id_eq,
    ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.star_eq_conjTranspose]
  rw [energyGradient_gram, gramGradientAt_apply]

lemma continuousAt_tendstoUniformlyOnFilter {E : Type uE} {F : Type uF} [TopologicalSpace E]
    [UniformSpace F] {H : ℝ × E → F} {x : E}
    (hH : ContinuousAt H (0, x)) :
    TendstoUniformlyOnFilter (fun η y => H (η, y)) (fun y => H (0, y))
      (𝓝[>] 0) (𝓝 x) := by
  apply tendstoUniformlyOnFilter_iff_tendsto.mpr
  have hp : (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x ≤ 𝓝 (0, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have h₂ : Tendsto H ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.mono_left hp
  have h₁ : Tendsto (fun p : ℝ × E => H (0, p.2))
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.tendsto.comp (tendsto_const_nhds.prodMk_nhds tendsto_snd)
  exact (h₁.prodMk_nhds h₂).mono_right (nhds_le_uniformity _)

def gramRegularization (η : ℝ) (R : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  regularize (Rᴴ * R) (η^2)

lemma continuous_gramRegularization : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramRegularization p.1 p.2) := by
  unfold gramRegularization regularize
  fun_prop

lemma gramRegularization_posSemidef (η : ℝ) (R : Matrix ι ι ℂ) :
    (gramRegularization η R).PosSemidef :=
  regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _) (sq_nonneg _)

@[simp] lemma gramRegularization_zero (R : Matrix ι ι ℂ) :
    gramRegularization 0 R = Rᴴ * R := by simp [gramRegularization, regularize]

lemma continuous_regularizedGradient : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramGradientAt p.2 (gramRegularization p.1 p.2)) := by
  unfold gramGradientAt
  have hs : Continuous (fun p : ℝ × Matrix ι ι ℂ => CFC.sqrt (gramRegularization p.1 p.2)) :=
    continuous_sqrt_matrix continuous_gramRegularization
      (fun p => gramRegularization_posSemidef p.1 p.2)
  have hr : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ) := (continuous_snd.mul hs).star
  have hm : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ)) :=
    (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ)).continuous.comp hr
  have ht : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      traceRealCLM.comp ((ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ))) :=
    (ContinuousLinearMap.compL ℝ (Matrix ι ι ℂ) (Matrix ι ι ℂ) ℝ
      traceRealCLM).continuous.comp hm
  exact ht.const_smul (3 : ℝ)

lemma eventually_regularizedEnergy_deriv (R : Matrix ι ι ℂ) :
    ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R,
      HasFDerivAt (fun X => energy (gramRegularization p.1 X))
        (gramGradientAt p.2 (gramRegularization p.1 p.2)) p.2 := by
  have hp0 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  have hh : ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R, 0 < p.1 :=
    hp0.prod_inl _
  filter_upwards [hh] with p hp
  exact regularized_energyGram_hasFDerivAt p.2 (sq_pos_of_pos hp)

lemma continuous_regularizedEnergy_single (R : Matrix ι ι ℂ) :
    Continuous (fun η : ℝ => energy (gramRegularization η R)) := by
  have hp : Continuous (fun η : ℝ => gramRegularization η R) := by
    unfold gramRegularization regularize
    fun_prop
  exact traceRealCLM.continuous.comp (hp.mul (continuous_sqrt_matrix hp
    (fun η => gramRegularization_posSemidef η R)))

lemma tendsto_regularizedEnergy (R : Matrix ι ι ℂ) :
    Tendsto (fun η => energy (gramRegularization η R))
      (𝓝[>] 0) (𝓝 (energy (Rᴴ * R))) := by
  have ht := (continuous_regularizedEnergy_single R).tendsto (0 : ℝ)
  rw [gramRegularization_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

theorem energyGram_hasFDerivAt (R : Matrix ι ι ℂ) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
      (gramGradientAt R (Rᴴ * R)) R := by
  have hh := hasFDerivAt_of_tendstoUniformlyOnFilter (𝕜 := ℝ) (x := R)
    (f := fun (η : ℝ) (X : Matrix ι ι ℂ) => energy (gramRegularization η X))
    (f' := fun (η : ℝ) (X : Matrix ι ι ℂ) => gramGradientAt X (gramRegularization η X))
    (g := fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
    (g' := fun X : Matrix ι ι ℂ => gramGradientAt X (gramRegularization 0 X))
    (continuousAt_tendstoUniformlyOnFilter
      (continuous_regularizedGradient.continuousAt (x := (0, R))))
    (eventually_regularizedEnergy_deriv R)
    (Eventually.of_forall (fun X => tendsto_regularizedEnergy X))
  simpa only [gramRegularization_zero] using hh

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section

lemma hasDerivAt_of_coordinates {ν : Type uν} [Fintype ν] [DecidableEq ν]
    {f : (ν → ℝ) → ℝ} {g : ℝ → ν → ℝ} {g' k : ν → ℝ} {s : ℝ}
    (hf : DifferentiableAt ℝ f (g s)) (hg : HasDerivAt g g' s)
    (hk : ∀ i, HasDerivAt (fun q => f (Function.update (g s) i q)) (k i) (g s i)) :
    HasDerivAt (fun t => f (g t)) (∑ i, g' i * k i) s := by
  let T := fderiv ℝ f (g s)
  have hTi : ∀ i, T (Pi.single i 1) = k i := by
    intro i
    have hfu : HasFDerivAt f T (Function.update (g s) i (g s i)) := by
      simpa only [Function.update_eq_self] using hf.hasFDerivAt
    have hi := hfu.comp_hasDerivAt (g s i)
      ((hasFDerivAt_update (i := i) (g s) (g s i)).hasDerivAt)
    have he : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) : ℝ →L[ℝ] (ν → ℝ)) 1 =
        Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [he] at hi
    exact hi.unique (hk i)
  have hT : T g' = ∑ i, g' i * k i := by
    conv_lhs => rw [← Finset.univ_sum_single g']
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (g' i) = g' i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [he, map_smul, hTi, smul_eq_mul]
  have hd := hf.hasFDerivAt.comp_hasDerivAt s hg
  change HasDerivAt _ (T g') s at hd
  rwa [hT] at hd

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_differentiableAt_variances (h a b : ℝ) (w : Three)
    {σ : Three → ℝ} (hσ : 0 < σ w) :
    DifferentiableAt ℝ (fun τ : Three → ℝ => weight h a b (τ w)) σ := by
  have hap : DifferentiableAt ℝ (fun τ : Three → ℝ => τ w) σ := by
    convert! (ContinuousLinearMap.proj w : (Three → ℝ) →L[ℝ] ℝ).differentiableAt
  have hd := (weight_hasDerivAt_variance h a b (σ w) hσ).differentiableAt.comp σ hap
  exact hd

omit [DecidableEq ι] in
lemma heatArray_differentiableAt_variances (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) (p : Three → ℝ)
    {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    DifferentiableAt ℝ (fun τ => heatArray A h u p τ v) σ := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have hleft := (weight_differentiableAt_variances h (u i) (p v) v (hσ v)).sqrt
    (weight_pos hh (hσ v) (u i) (p v)).ne'
  have hright := (weight_differentiableAt_variances h (u j) (p (v+1)) (v+1) (hσ (v+1))).sqrt
    (weight_pos hh (hσ (v+1)) (u j) (p (v+1))).ne'
  exact ((Complex.ofRealCLM.differentiableAt.comp σ hleft).mul_const (A v i j)).mul
    (Complex.ofRealCLM.differentiableAt.comp σ hright)

omit [DecidableEq ι] in
lemma triangleBlocks_differentiableAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → Three → Matrix ι ι ℂ} {x : E} (hW : ∀ v, DifferentiableAt ℝ (fun y => W y v) x)
    (v w : Three) : DifferentiableAt ℝ (fun y => triangleBlocks (W y) v w) x := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have he v i j := (differentiableAt_pi.mp (differentiableAt_pi.mp (hW v) i) j)
  fin_cases v <;> fin_cases w <;> simp only [triangleBlocks]
  all_goals first | exact differentiableAt_const _ | exact he _ _ _ | exact (he _ _ _).star

lemma rowStar_differentiableAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → Three → Matrix ι ι ℂ} {x : E} (hW : ∀ v, DifferentiableAt ℝ (fun y => W y v) x)
    (v : Three) : DifferentiableAt ℝ (fun y => rowStar (W y) v) x := by
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  simp only [rowStar_apply]
  by_cases ha : a.1 = v
  · simp only [ite_eq_left ha]
    exact differentiableAt_pi.mp (differentiableAt_pi.mp
      (triangleBlocks_differentiableAt hW a.1 b.1) a.2) b.2
  · simp only [ite_eq_right ha]
    exact differentiableAt_const _

lemma heatEnergy_differentiableAt_variances (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) (p : Three → ℝ)
    {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    DifferentiableAt ℝ (fun τ => heatEnergy A h u p τ v) σ := by
  have hd := (energyGram_hasFDerivAt (rowStar (heatArray A h u p σ) v)).differentiableAt.comp σ
    (rowStar_differentiableAt (heatArray_differentiableAt_variances A hh u p hσ) v)
  exact hd

lemma heatEnergy_hasDerivAt_time (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) (v : Three) :
    HasDerivAt (fun t => heatEnergy A h u p (fun w => α w * t) v)
      (∑ w, α w * heatVariance A h u p (fun w => α w * s) v w) s := by
  apply hasDerivAt_of_coordinates (f := fun τ => heatEnergy A h u p τ v)
    (g := fun t w => α w * t) (g' := α)
    (heatEnergy_differentiableAt_variances A hh u p (fun w => mul_pos (hα w) hs) v)
  · apply hasDerivAt_pi.mpr
    intro w
    convert! (hasDerivAt_id s).const_mul (α w) using 1
    simp only [mul_one]
  · exact fun w => heatEnergy_hasDerivAt_variance A hh u p (fun a => mul_pos (hα a) hs) v w

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma heatArray_differentiableAt_centers (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    (p : Three → ℝ) (v : Three) :
    DifferentiableAt ℝ (fun q => heatArray A h u q σ v) p := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have happ (w : Three) : DifferentiableAt ℝ (fun q : Three → ℝ => q w) p := by
    convert! (ContinuousLinearMap.proj w : (Three → ℝ) →L[ℝ] ℝ).differentiableAt
  have hw (a : Three) (k : ι) : DifferentiableAt ℝ
      (fun q : Three → ℝ => weight h (u k) (q a) (σ a)) p := by
    have hd := (weight_hasDerivAt_center h (u k) (p a) (σ a) (hσ a)).differentiableAt.comp p (happ a)
    exact hd
  have hleft := (hw v i).sqrt (weight_pos hh (hσ v) (u i) (p v)).ne'
  have hright := (hw (v+1) j).sqrt (weight_pos hh (hσ (v+1)) (u j) (p (v+1))).ne'
  exact ((Complex.ofRealCLM.differentiableAt.comp p hleft).mul_const (A v i j)).mul
    (Complex.ofRealCLM.differentiableAt.comp p hright)

lemma continuous_heatRow (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => rowStar (heatArray A h u p σ) v) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (rowStar_differentiableAt (heatArray_differentiableAt_centers A hh u hσ p) v).continuousAt

lemma continuous_heatCarrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatCarrier A h u p σ v w) := by
  unfold heatCarrier
  split_ifs
  · exact continuous_heatRow A hh u hσ v
  · exact (continuous_heatRow A hh u hσ v).star

lemma continuous_heatEnergy (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => heatEnergy A h u p σ v) := by
  exact continuous_energyGram.comp (continuous_heatRow A hh u hσ v)

omit [Fintype ι] in
lemma continuous_heatMask {E : Type uE} [TopologicalSpace E] {r : E → Three → ι → ℝ}
    (hr : ∀ w j, Continuous (fun x => r x w j)) : Continuous (fun x => heatMask (r x)) := by
  simp only [heatMask_eq_diagonal]
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (hr a.1 a.2)
  · simp only [Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

omit [Fintype ι] in
lemma continuous_scoreMask (u : ι → ℝ) (σ : Three → ℝ) (w : Three) :
    Continuous (fun p : Three → ℝ => heatMask (fun a j => if a = w then score (u j) (p a) (σ a) else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score; fun_prop
  · exact continuous_const

omit [Fintype ι] in
lemma continuous_secondMask (u : ι → ℝ) (σ : Three → ℝ) (w : Three) :
    Continuous (fun p : Three → ℝ => heatMask (fun a j => if a = w then score (u j) (p a) (σ a)^2-(σ a)⁻¹ else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score; fun_prop
  · exact continuous_const

lemma continuous_energyGradient_insert {E : Type uE} [TopologicalSpace E]
    {R L : E → Matrix ι ι ℂ} (hr : Continuous R) (hl : Continuous L) :
    Continuous (fun x => energyGradient ((R x)ᴴ * R x) ((R x)ᴴ * L x * R x)) := by
  have hs := continuous_sqrt_matrix (hr.star.mul hr) (fun x => Matrix.posSemidef_conjTranspose_mul_self (R x))
  simp only [energyGradient_apply]
  exact continuous_const.mul (traceRealCLM.continuous.comp (hs.mul ((hr.star.mul hl).mul hr)))

lemma continuous_heatFirst (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatFirst A h u p σ v w) := by
  simp only [heatFirst, localGram_eq_carrier A hh u _ hσ, localFirst_eq_carrier A hh u _ hσ]
  exact continuous_energyGradient_insert (continuous_heatCarrier A hh u hσ v w)
    (continuous_scoreMask u σ w)

lemma continuous_heatSecondGradient (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)) := by
  simp only [localGram_eq_carrier A hh u _ hσ, localSecond_eq_carrier A hh u _ hσ]
  exact continuous_energyGradient_insert (continuous_heatCarrier A hh u hσ v w)
    (continuous_secondMask u σ w)

lemma continuous_heatVariance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatVariance A h u p σ v w) :=
  continuous_const.mul (continuous_heatSecondGradient A hh u hσ v w)

lemma measurable_heatPure (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Measurable (fun p => heatPure A h u p σ v w) := by
  have hc : Continuous (fun q : (Three → ℝ) × ℝ => heatFirst A h u (Function.update q.1 w q.2) σ v w) :=
    (continuous_heatFirst A hh u hσ v w).comp (by fun_prop)
  have hm := (measurable_deriv_with_param
    (f := fun p q => heatFirst A h u (Function.update p w q) σ v w) hc).comp
    (show Measurable (fun p : Three → ℝ => (p, p w)) by fun_prop)
  convert! hm using 1
  funext p
  exact (heatFirst_hasDerivAt_center A hh u p hσ v w).deriv.symm

lemma measurable_heatCost (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Measurable (fun p => heatCost A h u p σ v w) := by
  have hm := (measurable_heatPure A hh u hσ v w).sub
    (continuous_heatSecondGradient A hh u hσ v w).measurable
  convert! hm using 1
  funext p
  simp [heatPure, heatCost]

lemma measurable_heatMixed (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    Measurable (fun p => heatMixed A h u p σ v w z) := by
  have hc : Continuous (fun q : (Three → ℝ) × ℝ => heatFirst A h u (Function.update q.1 z q.2) σ v w) :=
    (continuous_heatFirst A hh u hσ v w).comp (by fun_prop)
  have hm := (measurable_deriv_with_param
    (f := fun p q => heatFirst A h u (Function.update p z q) σ v w) hc).comp
    (show Measurable (fun p : Three → ℝ => (p, p z)) by fun_prop)
  convert! hm using 1
  funext p
  exact (heatFirst_hasDerivAt_other A hh u p hσ hw hz hwz).deriv.symm

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma measurable_chart (i : Three) (d : ℝ) : Measurable (chart i d) :=
  ((chart_continuous i).comp (continuous_const.prodMk continuous_id)).measurable

lemma hasDerivAt_chart_of_center {f : (Three → ℝ) → ℝ} {g : (Three → ℝ) → ℝ}
    (i : Three) (d : ℝ) (z : ℝ × ℝ)
    (h : ∀ p, HasDerivAt (fun t => f (Function.update p i t)) (g p) (p i)) :
    HasDerivAt (fun e => f (chart i e z)) (g (chart i d z)) d := by
  have hd := (h (chart i d z)).comp d (chart_hasDerivAt i d z)
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro e
  apply congrArg f
  ext j
  fin_cases i <;> fin_cases j <;> simp [chart,Function.update]

def planeIntegral (f : (Three → ℝ) → ℝ) (d : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, f (chart 2 d z)

lemma planeIntegral_eq (f : (Three → ℝ) → ℝ) (i : Three) (d : ℝ) :
    planeIntegral f d = ∫ z : ℝ × ℝ, f (chart i d z) := integral_chart_eq 2 i d f

lemma hasDerivAt_planeIntegral {f g : (Three → ℝ) → ℝ} {B : (ℝ × ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hB : Integrable B)
    (i : Three) (d : ℝ)
    (hb0 : ∀ z, ‖f (chart i d z)‖ ≤ B z)
    (hb : ∀ e ∈ Set.Ioo (d-1) (d+1), ∀ z, ‖g (chart i e z)‖ ≤ B z)
    (hd : ∀ p, HasDerivAt (fun t => f (Function.update p i t)) (g p) (p i)) :
    HasDerivAt (planeIntegral f) (planeIntegral g d) d := by
  have hs : Set.Ioo (d-1) (d+1) ∈ 𝓝 d := Ioo_mem_nhds (by linarith) (by linarith)
  have hint : Integrable (fun z => f (chart i d z)) :=
    hB.mono' (hf.comp (measurable_chart i d)).aestronglyMeasurable (Eventually.of_forall hb0)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun e z => f (chart i e z))
    (F' := fun e z => g (chart i e z)) hs
    (Eventually.of_forall (fun e => (hf.comp (measurable_chart i e)).aestronglyMeasurable)) hint
    (hg.comp (measurable_chart i d)).aestronglyMeasurable
    (Eventually.of_forall (fun z e he => hb e he z)) hB
    (Eventually.of_forall (fun z e _ => hasDerivAt_chart_of_center i e z hd))).2
  rw [← planeIntegral_eq g i d] at hh
  exact hh.congr_of_eventuallyEq (Eventually.of_forall (fun e => planeIntegral_eq f i e))

lemma finite_variance_bounds (σ : Three → ℝ) (hσ : ∀ w, 0 < σ w) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ (∀ w, a ≤ σ w) ∧ (∀ w, σ w ≤ b) := by
  let a := min (σ 0) (min (σ 1) (σ 2))
  let b := σ 0 + σ 1 + σ 2
  have ha : 0 < a := lt_min (hσ 0) (lt_min (hσ 1) (hσ 2))
  have hlo : ∀ w, a ≤ σ w := by
    intro w; fin_cases w
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hhi : ∀ w, σ w ≤ b := by
    intro w; fin_cases w <;> dsimp [b] <;> linarith [hσ 0,hσ 1,hσ 2]
  exact ⟨a,b,ha,(hlo 0).trans (hhi 0),hlo,hhi⟩

lemma abs_le_add_one_of_mem_Ioo {d e : ℝ} (he : e ∈ Set.Ioo (d-1) (d+1)) :
    |e| ≤ |d|+1 := by
  apply abs_le.mpr
  constructor <;> linarith [he.1,he.2,le_abs_self d,neg_le_abs d]

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

structure HeatPlaneIntegrable (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : Prop where
  energy : ∀ i v, Integrable (fun z => heatEnergy A h u (chart i d z) σ v)
  first : ∀ i v w, Integrable (fun z => heatFirst A h u (chart i d z) σ v w)
  pure : ∀ i v w, Integrable (fun z => heatPure A h u (chart i d z) σ v w)
  variance : ∀ i v w, Integrable (fun z => heatVariance A h u (chart i d z) σ v w)
  cost : ∀ i v w, Integrable (fun z => heatCost A h u (chart i d z) σ v w)
  mixed : ∀ i v w z, w ≠ v → z ≠ v → w ≠ z → Integrable (fun x => heatMixed A h u (chart i d x) σ v w z)

lemma heatPlane_integrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) :
    HeatPlaneIntegrable A h u d σ := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hbound⟩ := exists_heat_uniform_majorant A hh ha hab (abs_nonneg d) u
  have hb i z := hbound i d z (le_refl |d|) σ hla hlb
  have hmono (f : (Three → ℝ) → ℝ) (hf : Measurable f) (i : Three)
      (hb : ∀ z, ‖f (chart i d z)‖ ≤ B z) : Integrable (fun z => f (chart i d z)) :=
    hB.mono' (hf.comp (measurable_chart i d)).aestronglyMeasurable (Eventually.of_forall hb)
  constructor
  · intro i v
    exact hmono _ (continuous_heatEnergy A hh u hσ v).measurable i (fun z => (hb i z).energy v)
  · intro i v w
    exact hmono _ (continuous_heatFirst A hh u hσ v w).measurable i (fun z => (hb i z).first v w)
  · intro i v w
    exact hmono _ (measurable_heatPure A hh u hσ v w) i (fun z => (hb i z).pure v w)
  · intro i v w
    exact hmono _ (continuous_heatVariance A hh u hσ v w).measurable i (fun z => (hb i z).variance v w)
  · intro i v w
    exact hmono _ (measurable_heatCost A hh u hσ v w) i (fun z => (hb i z).cost v w)
  · intro i v w z hw hz hwz
    exact hmono _ (measurable_heatMixed A hh u hσ hw hz hwz) i (fun x => (hb i x).mixed v w z hw hz)

lemma planeEnergy_hasDerivAt (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (planeIntegral (fun p => heatEnergy A h u p σ v))
      (planeIntegral (fun p => heatFirst A h u p σ v w) d) d := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hb⟩ := exists_heat_uniform_majorant A hh ha hab (by positivity : 0 ≤ |d|+1) u
  apply hasDerivAt_planeIntegral (continuous_heatEnergy A hh u hσ v).measurable
    (continuous_heatFirst A hh u hσ v w).measurable hB w d
  · exact fun z => (hb w d z (by linarith) σ hla hlb).energy v
  · exact fun e he z => (hb w e z (abs_le_add_one_of_mem_Ioo he) σ hla hlb).first v w
  · exact fun p => heatEnergy_hasDerivAt_center A hh u p hσ v w

lemma planeFirst_hasDerivAt (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (planeIntegral (fun p => heatFirst A h u p σ v w))
      (planeIntegral (fun p => heatPure A h u p σ v w) d) d := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hb⟩ := exists_heat_uniform_majorant A hh ha hab (by positivity : 0 ≤ |d|+1) u
  apply hasDerivAt_planeIntegral (continuous_heatFirst A hh u hσ v w).measurable
    (measurable_heatPure A hh u hσ v w) hB w d
  · exact fun z => (hb w d z (by linarith) σ hla hlb).first v w
  · exact fun e he z => (hb w e z (abs_le_add_one_of_mem_Ioo he) σ hla hlb).pure v w
  · exact fun p => heatFirst_hasDerivAt_center A hh u p hσ v w

lemma planeFirst_hasDerivAt_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    HasDerivAt (planeIntegral (fun p => heatFirst A h u p σ v w))
      (planeIntegral (fun p => heatMixed A h u p σ v w z) d) d := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hb⟩ := exists_heat_uniform_majorant A hh ha hab (by positivity : 0 ≤ |d|+1) u
  apply hasDerivAt_planeIntegral (continuous_heatFirst A hh u hσ v w).measurable
    (measurable_heatMixed A hh u hσ hw hz hwz) hB z d
  · exact fun x => (hb z d x (by linarith) σ hla hlb).first v w
  · exact fun e he x => (hb z e x (abs_le_add_one_of_mem_Ioo he) σ hla hlb).mixed v w z hw hz
  · exact fun p => heatFirst_hasDerivAt_other A hh u p hσ hw hz hwz

lemma planePure_eq_mixed (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    (i : Three) {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    planeIntegral (fun p => heatPure A h u p σ v i) d =
      planeIntegral (fun p => heatMixed A h u p σ v w z) d := by
  have hf : planeIntegral (fun p => heatFirst A h u p σ v i) =
      planeIntegral (fun p => heatFirst A h u p σ v w) := by
    funext e
    exact (planeEnergy_hasDerivAt A hh u e hσ v i).unique (planeEnergy_hasDerivAt A hh u e hσ v w)
  have hi := planeFirst_hasDerivAt A hh u d hσ v i
  rw [hf] at hi
  exact hi.unique (planeFirst_hasDerivAt_other A hh u d hσ hw hz hwz)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma planeEnergy_hasDerivAt_time (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) (v : Three) :
    HasDerivAt (fun t => planeIntegral (fun p => heatEnergy A h u p (fun w => α w*t) v) d)
      (∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d) s := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds α hα
  have hb : 0 < b := ha.trans_le hab
  have has : 0 < a*(s/2) := mul_pos ha (by linarith)
  have habs : a*(s/2) ≤ b*(2*s) := by gcongr; linarith
  obtain ⟨B,hB,hBn,hbound⟩ := exists_heat_uniform_majorant A hh has habs (abs_nonneg d) u
  let C := ∑ w, α w
  have hC : 0 ≤ C := Finset.sum_nonneg (fun w _ => (hα w).le)
  have hσ : ∀ w, 0 < α w*s := fun w => mul_pos (hα w) hs
  have hint := (heatPlane_integrable A hh u d hσ).energy 2 v
  have hvar := (heatPlane_integrable A hh u d hσ).variance 2 v
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*s) v w) := by
    exact (Finset.aestronglyMeasurable_fun_sum Finset.univ (fun w _ =>
        (hvar w).aestronglyMeasurable.const_mul (α w)))
  have hboundσ (t : ℝ) (ht : t ∈ Set.Ioo (s/2) (2*s)) :
      (∀ w, a*(s/2) ≤ α w*t) ∧ (∀ w, α w*t ≤ b*(2*s)) := by
    have ht0 : 0 < t := (by linarith : 0 < s/2).trans ht.1
    constructor
    · intro w; exact mul_le_mul (hla w) ht.1.le (by linarith) (hα w).le
    · intro w; exact mul_le_mul (hlb w) ht.2.le ht0.le hb.le
  have hn : Set.Ioo (s/2) (2*s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hfmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (fun z : ℝ × ℝ => heatEnergy A h u (chart 2 d z) (fun w => α w*t) v) := by
    filter_upwards [hn] with t ht
    have ht0 : 0 < t := (by linarith : 0 < s/2).trans ht.1
    exact ((continuous_heatEnergy A hh u (fun w => mul_pos (hα w) ht0) v).measurable.comp
      (measurable_chart 2 d)).aestronglyMeasurable
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z => heatEnergy A h u (chart 2 d z) (fun w => α w*t) v)
    (F' := fun t z => ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*t) v w)
    (bound := fun z => C*B z) hn hfmeas hint hmeas
    (Eventually.of_forall (fun z t ht => by
      calc
        _ ≤ ∑ w, ‖α w * heatVariance A h u (chart 2 d z) (fun a => α a*t) v w‖ := norm_sum_le _ _
        _ ≤ ∑ w, α w * B z := by
          apply Finset.sum_le_sum
          intro w _
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hα w)]
          exact mul_le_mul_of_nonneg_left
            ((hbound 2 d z (le_refl _) _ (hboundσ t ht).1 (hboundσ t ht).2).variance v w) (hα w).le
        _ = C*B z := (Finset.sum_mul _ _ _).symm))
    (hB.const_mul C)
    (Eventually.of_forall (fun z t ht => heatEnergy_hasDerivAt_time A hh u (chart 2 d z) α hα
      ((by linarith : 0 < s/2).trans ht.1) v))).2
  have he : (∫ z : ℝ × ℝ, ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*s) v w) =
      ∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d := by
    rw [integral_finsetSum _ (fun w _ => (hvar w).const_mul (α w))]
    simp only [integral_const_mul, planeIntegral]
  rw [he] at hder
  exact hder

lemma two_planeVariance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    2 * planeIntegral (fun p => heatVariance A h u p σ v w) d =
      planeIntegral (fun p => heatPure A h u p σ v w) d -
      planeIntegral (fun p => heatCost A h u p σ v w) d := by
  rw [planeIntegral, ← integral_const_mul]
  have he : (fun z : ℝ × ℝ => 2 * heatVariance A h u (chart 2 d z) σ v w) =
      (fun z => heatPure A h u (chart 2 d z) σ v w - heatCost A h u (chart 2 d z) σ v w) := by
    funext z
    simp only [heatVariance,heatPure,heatCost]
    ring
  rw [he, integral_sub ((heatPlane_integrable A hh u d hσ).pure 2 v w)
    ((heatPlane_integrable A hh u d hσ).cost 2 v w)]
  rfl

lemma planeCost_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) (v w : Three) :
    0 ≤ planeIntegral (fun p => heatCost A h u p σ v w) d :=
  integral_nonneg (fun z => heatCost_nonneg A h u (chart 2 d z) σ v w)

lemma two_planeMixed_le (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    2 * planeIntegral (fun p => heatMixed A h u p σ v w z) d ≤
      planeIntegral (fun p => heatCost A h u p σ v w) d +
      planeIntegral (fun p => heatCost A h u p σ v z) d := by
  have hi := heatPlane_integrable A hh u d hσ
  simp only [planeIntegral]
  rw [← integral_const_mul, ← integral_add (hi.cost 2 v w) (hi.cost 2 v z)]
  exact integral_mono ((hi.mixed 2 v w z hw hz hwz).const_mul 2)
    ((hi.cost 2 v w).add (hi.cost 2 v z)) (fun p => two_heatMixed_le A hh u (chart 2 d p) hσ hw hz)

lemma planeCost_neighbors (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a) (w : Three) :
    (∑ v, if v = w then 0 else planeIntegral (fun p => heatCost A h u p σ v w) d) ≤
      Real.sqrt 2 * planeIntegral (fun p => heatCost A h u p σ w w) d := by
  have hi := heatPlane_integrable A hh u d hσ
  have hv v : Integrable (fun z : ℝ × ℝ => if v = w then (0:ℝ) else heatCost A h u (chart 2 d z) σ v w) := by
    split_ifs
    · exact integrable_zero _ _ _
    · exact hi.cost 2 v w
  have he : (∑ v, if v = w then 0 else planeIntegral (fun p => heatCost A h u p σ v w) d) =
      ∫ z : ℝ × ℝ, ∑ v, if v = w then 0 else heatCost A h u (chart 2 d z) σ v w := by
    rw [integral_finsetSum _ (fun v _ => hv v)]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp [planeIntegral]
  rw [he, planeIntegral, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun v _ => hv v))
    ((hi.cost 2 w w).const_mul _) (fun z => heatCost_neighbors A hh u (chart 2 d z) hσ w)

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators

lemma finite_cost_dissipation (α : Three → ℝ) (hα : ∀ w, 0 ≤ α w)
    (K : Three → Three → ℝ) (Z : Three → ℝ) (hK : ∀ v w, 0 ≤ K v w)
    (hrow : ∀ v, 2*Z v ≤ ∑ w, if w = v then 0 else K v w)
    (hcol : ∀ w, (∑ v, if v = w then 0 else K v w) ≤ Real.sqrt 2 * K w w) :
    (∑ v, ((∑ w, α w)*Z v - (∑ w, α w*K v w))) ≤
      ∑ w, (-α w + Real.sqrt 2 * max 0 ((∑ v, α v)/2-α w))*K w w := by
  let S := ∑ w, α w
  have hS : 0 ≤ S := Finset.sum_nonneg (fun w _ => hα w)
  have hr v : S*Z v ≤ S/2 * ∑ w, if w = v then 0 else K v w := by
    have hh := mul_le_mul_of_nonneg_left (hrow v) (show 0 ≤ S/2 by positivity)
    nlinarith
  have hc w : (S/2-α w)*(∑ v, if v = w then 0 else K v w) ≤
      Real.sqrt 2 * max 0 (S/2-α w)*K w w := by
    have ho : 0 ≤ ∑ v, if v = w then 0 else K v w :=
      Finset.sum_nonneg (fun v _ => by split_ifs; exact le_refl 0; exact hK v w)
    calc
      _ ≤ max 0 (S/2-α w)*(∑ v, if v = w then 0 else K v w) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) ho
      _ ≤ max 0 (S/2-α w)*(Real.sqrt 2*K w w) :=
        mul_le_mul_of_nonneg_left (hcol w) (le_max_left _ _)
      _ = _ := by ring
  calc
    _ ≤ ∑ v, (S/2*(∑ w, if w = v then 0 else K v w) - (∑ w, α w*K v w)) := by
      apply Finset.sum_le_sum
      intro v _
      exact sub_le_sub_right (hr v) _
    _ = ∑ w, (-α w*K w w + (S/2-α w)*(∑ v, if v = w then 0 else K v w)) := by
      simp [Fin.sum_univ_three]
      ring
    _ ≤ ∑ w, (-α w*K w w + Real.sqrt 2 * max 0 (S/2-α w)*K w w) := by
      apply Finset.sum_le_sum
      intro w _
      exact add_le_add (le_refl _) (hc w)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      dsimp [S]
      ring

lemma offdiag_sum_eq (f : Three → ℝ) (v : Three) :
    (∑ w, if w = v then 0 else f w) = f (v+1)+f (v+2) := by
  fin_cases v <;> simp [Fin.sum_univ_three, add_comm]

lemma neighbor_one_ne (v : Three) : v+1 ≠ v := by fin_cases v <;> decide
lemma neighbor_two_ne (v : Three) : v+2 ≠ v := by fin_cases v <;> decide
lemma neighbors_ne (v : Three) : v+1 ≠ v+2 := by fin_cases v <;> decide
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def totalPlaneEnergy (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : ℝ :=
  ∑ v, planeIntegral (fun p => heatEnergy A h u p σ v) d

def totalPlaneTime (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (α : Three → ℝ) (s : ℝ) : ℝ :=
  ∑ v, ∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d

lemma totalPlaneEnergy_hasDerivAt (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => totalPlaneEnergy A h u d (fun w => α w*t))
      (totalPlaneTime A h u d α s) s := by
  exact HasDerivAt.fun_sum (fun v _ => planeEnergy_hasDerivAt_time A hh u d α hα hs v)

lemma two_totalPlaneTime (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) :
    2 * totalPlaneTime A h u d α s =
      ∑ v, ((∑ w, α w) * planeIntegral (fun p => heatMixed A h u p (fun a => α a*s) v (v+1) (v+2)) d -
        (∑ w, α w * planeIntegral (fun p => heatCost A h u p (fun a => α a*s) v w) d)) := by
  have hσ : ∀ w, 0 < α w*s := fun w => mul_pos (hα w) hs
  unfold totalPlaneTime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have hp := two_planeVariance A hh u d hσ v w
  rw [planePure_eq_mixed A hh u d hσ w (neighbor_one_ne v) (neighbor_two_ne v) (neighbors_ne v)] at hp
  linear_combination (α w)*hp

lemma plane_dissipation (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) :
    2 * totalPlaneTime A h u d α s ≤
      ∑ w, (-α w + Real.sqrt 2 * max 0 ((∑ v, α v)/2-α w)) *
        planeIntegral (fun p => heatCost A h u p (fun a => α a*s) w w) d := by
  have hσ : ∀ w, 0 < α w*s := fun w => mul_pos (hα w) hs
  rw [two_totalPlaneTime A hh u d α hα hs]
  apply finite_cost_dissipation α (fun w => (hα w).le)
  · exact fun v w => planeCost_nonneg A h u d _ v w
  · intro v
    rw [offdiag_sum_eq]
    exact two_planeMixed_le A hh u d hσ (neighbor_one_ne v) (neighbor_two_ne v) (neighbors_ne v)
  · exact planeCost_neighbors A hh u d hσ

def strictRate (i w : Three) : ℝ := if w = i then 1 else 11/10

def strictConstant : ℝ := (1/2) * min (1 - (3/5)*Real.sqrt 2) (11/10 - (1/2)*Real.sqrt 2)

lemma strictRate_pos (i w : Three) : 0 < strictRate i w := by
  unfold strictRate; split_ifs <;> norm_num

lemma sum_strictRate (i : Three) : (∑ w, strictRate i w) = 16/5 := by
  have he (w : Three) : strictRate i w = (11/10:ℝ) + if w = i then (-1/10:ℝ) else 0 := by
    unfold strictRate
    split_ifs <;> norm_num
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  norm_num [Finset.sum_ite_eq', Fintype.card_fin, Three]

lemma strictConstant_pos : 0 < strictConstant := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg (2:ℝ)
  have h1 : 0 < 1 - (3/5)*Real.sqrt 2 := by nlinarith
  have h2 : 0 < 11/10 - (1/2)*Real.sqrt 2 := by nlinarith
  exact mul_pos (by norm_num) (lt_min h1 h2)

lemma strictRate_coefficient (i w : Three) :
    -strictRate i w + Real.sqrt 2 * max 0 ((∑ v, strictRate i v)/2-strictRate i w) ≤
      -2 * strictConstant := by
  rw [sum_strictRate]
  have h1 := min_le_left (1 - (3/5)*Real.sqrt 2) (11/10 - (1/2)*Real.sqrt 2)
  have h2 := min_le_right (1 - (3/5)*Real.sqrt 2) (11/10 - (1/2)*Real.sqrt 2)
  unfold strictRate strictConstant
  split_ifs <;> norm_num <;> linarith

lemma plane_strict_dissipation (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (i : Three) {s : ℝ} (hs : 0 < s) :
    strictConstant * (∑ w, planeIntegral (fun p => heatCost A h u p (fun a => strictRate i a*s) w w) d) ≤
      -totalPlaneTime A h u d (strictRate i) s := by
  have hd := plane_dissipation A hh u d (strictRate i) (strictRate_pos i) hs
  have he : (∑ w, (-strictRate i w + Real.sqrt 2 * max 0 ((∑ v, strictRate i v)/2-strictRate i w)) *
        planeIntegral (fun p => heatCost A h u p (fun a => strictRate i a*s) w w) d) ≤
      -2 * strictConstant * (∑ w, planeIntegral (fun p => heatCost A h u p (fun a => strictRate i a*s) w w) d) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_right
      (strictRate_coefficient i w) (planeCost_nonneg A h u d _ w w))
  linarith
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def windowDiags (u : ι → ℝ) (p : Three → ℝ) (s : ℝ) : Three → Matrix ι ι ℂ :=
  fun v => Matrix.diagonal (fun i => (windowRatio s (u i-p v):ℂ))

def windowTrace (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p : Three → ℝ) (s : ℝ) : ℂ :=
  Matrix.trace (windowDiags u p s 0 * heatArray A h u p (fun _ => (11/10)*s) 0 *
    windowDiags u p s 1 * heatArray A h u p (fun _ => (11/10)*s) 1 *
    windowDiags u p s 2 * heatArray A h u p (fun _ => (11/10)*s) 2)

lemma rowBare_strict_eq_base (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p : Three → ℝ) (s : ℝ) (v : Three) :
    rowBare A (heatWeights h u p (fun z => strictRate v z*s)) v =
      rowBare A (heatWeights h u p (fun _ => (11/10)*s)) v := by
  apply rowBare_congr
  intro w hw i
  simp [heatWeights,strictRate,hw]

omit [Fintype ι] [DecidableEq ι] in
lemma heatWeights_strict_le_base {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) (v w : Three) (i : ι) :
    heatWeights h u p (fun z => strictRate v z*s) w i ≤
      Real.sqrt (11/10)*heatWeights h u p (fun _ => (11/10)*s) w i := by
  have hr : 1 ≤ Real.sqrt (11/10) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  by_cases hw : w=v
  · subst w
    simp only [heatWeights,strictRate,ite_true,one_mul,weight]
    have hd := mul_le_mul_of_nonneg_left (density_le_lambda hs (u i-p v)) hh.le
    simpa only [mul_left_comm] using hd
  · simp only [heatWeights,strictRate,ite_eq_right hw]
    exact le_mul_of_one_le_left (weight_pos hh (by positivity) _ _).le hr

lemma strict_starGram_le_base (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    starGram (heatArray A h u p (fun z => strictRate v z*s)) v ≤
      Real.sqrt (11/10) • starGram (heatArray A h u p (fun _ => (11/10)*s)) v := by
  have hb (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) w i :=
    (weight_pos hh (by positivity) _ _).le
  have ht (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun z => strictRate v z*s) w i :=
    (weight_pos hh (mul_pos (strictRate_pos v w) hs) _ _).le
  unfold heatArray
  rw [starGram_weightedArray _ _ ht,starGram_weightedArray _ _ hb,
    rowBare_strict_eq_base,← weightedGram_smul]
  exact weightedGram_mono _ _ _ (fun a => heatWeights_strict_le_base hh hs u p v a.1 a.2)

lemma windowInsertion_eq_score (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    starInsert (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) v =
      Real.sqrt s • starInsert (heatArray A h u p (fun z => strictRate v z*s))
        (heatScores u p (fun z => strictRate v z*s)) v := by
  have hb (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) w i :=
    (weight_pos hh (by positivity) _ _).le
  have ht (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun z => strictRate v z*s) w i :=
    (weight_pos hh (mul_pos (strictRate_pos v w) hs) _ _).le
  unfold heatArray windowDiags heatScores
  rw [← rowBare_insert _ _ _ hb,← rowBare_insert _ _ _ ht,
    rowBare_strict_eq_base,← weightedGram_smul]
  apply weightedGram_rowBare_congr
  intro i
  dsimp only
  simp only [heatWeights,strictRate,ite_true,one_mul,weight]
  have hn : density ((11/10)*s) (u i-p v) ≠ 0 := (density_pos (by positivity) _).ne'
  unfold windowRatio
  rw [oddWindow_score hs]
  simp only [div_eq_mul_inv]
  calc
    _ = (Real.sqrt s*(h*density s (u i-p v)*score (u i) (p v) s))*
        (density ((11/10)*s) (u i-p v)*(density ((11/10)*s) (u i-p v))⁻¹) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hn]; ring

lemma windowStarCost_le (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    hessianCost (starGram (heatArray A h u p (fun _ => (11/10)*s)) v)
      (starInsert (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) v) ≤
      2*s*heatCost A h u p (fun z => strictRate v z*s) v v := by
  have hσ : ∀ z, 0 < strictRate v z*s := fun z => mul_pos (strictRate_pos v z) hs
  let P := starGram (heatArray A h u p (fun z => strictRate v z*s)) v
  let K := starInsert (heatArray A h u p (fun z => strictRate v z*s))
    (heatScores u p (fun z => strictRate v z*s)) v
  have hsol : ∃ Y, sylv (CFC.sqrt P) Y = K := sylv_solvable_inserted_gram _ _
  have hsol' : ∃ Y, sylv (CFC.sqrt P) Y = Real.sqrt s • K := by
    obtain ⟨Y,hY⟩ := hsol
    exact ⟨Real.sqrt s • Y,by rw [sylv_smul_right,hY]⟩
  have hc := hessianCost_le_of_le_smul
    (Matrix.posSemidef_conjTranspose_mul_self (rowStar (heatArray A h u p (fun _ => (11/10)*s)) v))
    hsol' (by positivity : 0 < Real.sqrt (11/10)) (strict_starGram_le_base A hh hs u p v)
  rw [windowInsertion_eq_score A hh hs,heatCost_center A hh u p hσ]
  change hessianCost _ (Real.sqrt s • K) ≤ 2*s*hessianCost P K
  rw [hessianCost_smul_direction hsol,Real.sq_sqrt hs.le] at hc
  have hr : Real.sqrt (Real.sqrt (11/10)) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · rw [Real.sqrt_le_iff]; norm_num
  have hn : 0 ≤ hessianCost P K := hessianCost_nonneg _ _
  exact hc.trans (by
    calc
      _ ≤ 2*(s*hessianCost P K) := mul_le_mul_of_nonneg_right hr (mul_nonneg hs.le hn)
      _ = _ := by ring)

lemma windowTrace_le (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) :
    ‖windowTrace A h u p s‖ ≤ (440/3)*s*∑ v,
      heatCost A h u p (fun z => strictRate v z*s) v v := by
  have hD (v : Three) : (windowDiags u p s v).IsHermitian := by
    unfold windowDiags Matrix.IsHermitian
    rw [Matrix.diagonal_conjTranspose]
    simp
  have hd : ‖blockD (windowDiags u p s)‖ ≤ 44 :=
    norm_blockD_real_diagonal_le _ (by norm_num) (fun v i => abs_windowRatio_le hs _)
  have hm := mixed_trace_le (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) hD
  have hi := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset Three)) =>
    windowStarCost_le A hh hs u p v)
  apply hm.trans
  calc
    _ ≤ (5/3:ℝ)*44*(∑ v, 2*s*heatCost A h u p (fun z => strictRate v z*s) v v) := by
      gcongr
      exact Finset.sum_nonneg (fun v _ => hessianCost_nonneg _ _)
    _ = _ := by rw [← Finset.mul_sum]; ring

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma trace_mul_three (X Y Z : Matrix ι ι ℂ) :
    Matrix.trace (X*Y*Z) = ∑ i, ∑ j, ∑ k, X i j*Y j k*Z k i := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

lemma trace_diagonal_triangle (W : Three → Matrix ι ι ℂ) (d : Three → ι → ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2) =
      ∑ i, ∑ j, ∑ k, ((d 0 i:ℂ)*W 0 i j)*((d 1 j:ℂ)*W 1 j k)*((d 2 k:ℂ)*W 2 k i) := by
  rw [show Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2 =
      (Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0)*
      (Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1)*
      (Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2) by simp only [Matrix.mul_assoc]]
  simp only [trace_mul_three,Matrix.diagonal_mul]

lemma weighted_triangle_entry (a b c : ℂ) (g0 g1 g2 d0 d1 d2 : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) :
    ((d0:ℂ)*((Real.sqrt g0:ℂ)*a*(Real.sqrt g1:ℂ)))*
    ((d1:ℂ)*((Real.sqrt g1:ℂ)*b*(Real.sqrt g2:ℂ)))*
    ((d2:ℂ)*((Real.sqrt g2:ℂ)*c*(Real.sqrt g0:ℂ))) =
      a*b*c*((g0*d0)*(g1*d1)*(g2*d2):ℝ) := by
  have h0 : (Real.sqrt g0:ℂ)^2 = (g0:ℂ) := by exact_mod_cast Real.sq_sqrt hg0
  have h1 : (Real.sqrt g1:ℂ)^2 = (g1:ℂ) := by exact_mod_cast Real.sq_sqrt hg1
  have h2 : (Real.sqrt g2:ℂ)^2 = (g2:ℂ) := by exact_mod_cast Real.sq_sqrt hg2
  calc
    _ = a*b*c*(Real.sqrt g0:ℂ)^2*(Real.sqrt g1:ℂ)^2*(Real.sqrt g2:ℂ)^2*d0*d1*d2 := by ring
    _ = _ := by rw [h0,h1,h2]; push_cast; ring

lemma trace_weighted_triangle (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) :
    Matrix.trace (Matrix.diagonal (fun i => (d 0 i:ℂ))*weightedArray A g 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*weightedArray A g 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*weightedArray A g 2) =
      ∑ i, ∑ j, ∑ k, A 0 i j*A 1 j k*A 2 k i*((g 0 i*d 0 i)*(g 1 j*d 1 j)*(g 2 k*d 2 k):ℝ) := by
  rw [trace_diagonal_triangle]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact weighted_triangle_entry _ _ _ _ _ _ _ _ _ (hg 0 i) (hg 1 j) (hg 2 k)

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma weight_integrable_center (h u σ : ℝ) (hσ : 0 ≤ σ) :
    Integrable (fun p => weight h u p σ) := by
  exact ((volume.measurePreserving_sub_left u).integrable_comp_of_integrable (density_integrable hσ)).const_mul h

lemma integral_weight_center (h u : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ p, weight h u p σ) = h := by
  unfold weight
  rw [integral_const_mul,integral_sub_left_eq_self,integral_density hσ,mul_one]

lemma chart_integrable_iff (f : (Three → ℝ) → ℝ) (i j : Three) (d : ℝ) :
    Integrable (fun z : ℝ×ℝ => f (chart i d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart j d z)) := by
  have hi k : Integrable (fun z : ℝ×ℝ => f (chart k d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart 2 d z)) := by
    simp_rw [chartChange_eq k d]
    exact (chartChange_preserving k d).integrable_comp_emb (chartChange k d).measurableEmbedding (g := fun z : ℝ×ℝ => f (chart 2 d z))
  exact (hi i).trans (hi j).symm

lemma weight_pair_integrable (h a b d : ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v k : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart k d z v) (σ v) *
      weight h b (chart k d z (v+1)) (σ (v+1))) := by
  apply (chart_integrable_iff (fun p => weight h a (p v) (σ v)*weight h b (p (v+1)) (σ (v+1))) (v+2) k d).mp
  change Integrable (fun z : ℝ×ℝ => weight h a (chart (v+2) d z v) (σ v)*weight h b (chart (v+2) d z (v+1)) (σ (v+1))) (volume.prod volume)
  fin_cases v
  · simpa [chart] using (weight_integrable_center h a (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h b (σ 1) (hσ 1).le)
  · simpa [chart] using (weight_integrable_center h a (σ 1) (hσ 1).le).mul_prod
      (weight_integrable_center h b (σ 2) (hσ 2).le)
  · simpa [chart,mul_comm] using (weight_integrable_center h b (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h a (σ 2) (hσ 2).le)

lemma integral_weight_pair (h a b d : ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => weight h a (p v) (σ v)*weight h b (p (v+1)) (σ (v+1))) d = h^2 := by
  rw [planeIntegral_eq _ (v+2)]
  change (∫ z : ℝ×ℝ, weight h a (chart (v+2) d z v) (σ v)*weight h b (chart (v+2) d z (v+1)) (σ (v+1)) ∂volume.prod volume) = h^2
  have hp (a b σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
      (∫ z : ℝ×ℝ, weight h a z.1 σ * weight h b z.2 τ ∂volume.prod volume) = h^2 := by
    rw [integral_prod_mul (fun p => weight h a p σ) (fun p => weight h b p τ),
      integral_weight_center h a hσ,integral_weight_center h b hτ,pow_two]
  fin_cases v
  · simpa [chart] using hp a b (σ 0) (σ 1) (hσ 0) (hσ 1)
  · simpa [chart] using hp a b (σ 1) (σ 2) (hσ 1) (hσ 2)
  · simpa [chart,mul_comm] using hp b a (σ 0) (σ 2) (hσ 0) (hσ 2)

variable {ι : Type uι} [Fintype ι]

def edgeCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v : Three) : ℝ :=
  ∑ i, ∑ j, ‖A v i j‖^3 * (heatWeights h u p σ v i*heatWeights h u p σ (v+1) j)

lemma edgeCubic_integrable (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v k : Three) :
    Integrable (fun z : ℝ×ℝ => edgeCubic A h u (chart k d z) σ v) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (weight_pair_integrable h (u i) (u j) d σ hσ v k).const_mul _))

lemma planeIntegral_edgeCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => edgeCubic A h u p σ v) d = ∑ i, ∑ j, h^2 * ‖A v i j‖^3 := by
  unfold planeIntegral edgeCubic heatWeights
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (weight_pair_integrable h (u i) (u j) d σ hσ v 2).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (weight_pair_integrable h (u i) (u j) d σ hσ v 2).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  change ‖A v i j‖^3 * planeIntegral (fun p => weight h (u i) (p v) (σ v)*weight h (u j) (p (v+1)) (σ (v+1))) d = _
  rw [integral_weight_pair h (u i) (u j) d σ hσ v,mul_comm]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_triple_integrable {s t v : ℝ} (hs : 0 < s) (ht : 0 < t) (hv : 0 < v) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) := by
  have hst : Integrable (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)) := by
    exact ((volume.measurePreserving_sub_left a).integrable_comp_of_integrable (density_integrable hs.le)).mul_prod
      ((volume.measurePreserving_sub_left b).integrable_comp_of_integrable (density_integrable ht.le))
  apply (hst.mul_const (density v 0)).mono'
  · have hc : Continuous (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) :=
      (((continuous_density s).comp (continuous_const.sub continuous_fst)).mul
        ((continuous_density t).comp (continuous_const.sub continuous_snd))).mul
          ((continuous_density v).comp ((continuous_const.add continuous_fst).add continuous_snd))
    exact hc.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (density_nonneg hs.le _) (density_nonneg ht.le _)) (density_nonneg hv.le _))]
    exact mul_le_mul_of_nonneg_left (density_le_zero v _) (mul_nonneg (density_nonneg hs.le _) (density_nonneg ht.le _))

lemma integral_density_triple {s t v : ℝ} (hs : 0 < s) (ht : 0 < t) (hv : 0 < v) (a b c : ℝ) :
    (∫ z : ℝ×ℝ, density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) =
      density (s+t+v) (a+b+c) := by
  rw [MeasureTheory.Measure.volume_eq_prod,integral_prod _ (density_triple_integrable hs ht hv a b c)]
  have inner (p : ℝ) : (∫ q, density s (a-p)*density t (b-q)*density v (c+p+q)) =
      density s (a-p)*density (t+v) (b+c+p) := by
    have he (q : ℝ) : density v (c+p+q) = density v ((-c-p)-q) := by
      rw [show (-c-p)-q = -(c+p+q) by ring,density_neg]
    simp_rw [he,mul_assoc]
    rw [integral_const_mul,integral_density_product ht hv]
    congr 2
    ring
  simp_rw [inner]
  have he (p : ℝ) : density (t+v) (b+c+p) = density (t+v) ((-b-c)-p) := by
    rw [show (-b-c)-p = -(b+c+p) by ring,density_neg]
  simp_rw [he]
  rw [integral_density_product hs (add_pos ht hv)]
  congr 1 <;> ring

lemma planeIntegral_weight_triple (h a b c : ℝ) (σ : MatrixEnergy.Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 2) (σ 2)) 0 =
      h^3*density (σ 0+σ 1+σ 2) (a+b+c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1) * (h*density (σ 1) (b-z.2)) *
      (h*density (σ 2) (c-(0-z.1-z.2)))) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1) * (h*density (σ 1) (b-z.2)) *
      (h*density (σ 2) (c-(0-z.1-z.2))) =
      h^3*(density (σ 0) (a-z.1)*density (σ 1) (b-z.2)*density (σ 2) (c+z.1+z.2)) := by
    rw [show c-(0-z.1-z.2) = c+z.1+z.2 by ring]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_density_triple (hσ 0) (hσ 1) (hσ 2)]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section

lemma density_mul_windowRatio {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density ((11/10)*s) t * windowRatio s t = oddWindow s t := by
  unfold windowRatio
  exact mul_div_cancel₀ _ (density_pos (by positivity) _).ne'

lemma abs_oddWindow_le {s : ℝ} (hs : 0 < s) (t : ℝ) :
    |oddWindow s t| ≤ 44*density ((11/10)*s) t := by
  rw [← density_mul_windowRatio hs t,abs_mul,abs_of_nonneg (density_nonneg (by positivity) _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (abs_windowRatio_le hs t) (density_nonneg (by positivity) t)

lemma continuous_oddWindow (s : ℝ) : Continuous (oddWindow s) := by
  unfold oddWindow
  exact (continuous_id.div_const _).mul (continuous_density s)

lemma oddWindow_triple_integrable {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) := by
  have hi := (density_triple_integrable (by positivity : 0 < (11/10)*s)
    (by positivity : 0 < (11/10)*s) (by positivity : 0 < (11/10)*s) a b c).const_mul (44^3:ℝ)
  apply hi.mono'
  · exact (((continuous_oddWindow s).comp (continuous_const.sub continuous_fst)).mul
      ((continuous_oddWindow s).comp (continuous_const.sub continuous_snd)) |>.mul
        ((continuous_oddWindow s).comp ((continuous_const.add continuous_fst).add continuous_snd))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    have h0 := abs_oddWindow_le hs (a-z.1)
    have h1 := abs_oddWindow_le hs (b-z.2)
    have h2 := abs_oddWindow_le hs (c+z.1+z.2)
    have hd0 := density_nonneg (by positivity : 0 ≤ (11/10)*s) (a-z.1)
    have hd1 := density_nonneg (by positivity : 0 ≤ (11/10)*s) (b-z.2)
    calc
      _ ≤ (44*density ((11/10)*s) (a-z.1))*(44*density ((11/10)*s) (b-z.2))*(44*density ((11/10)*s) (c+z.1+z.2)) := by gcongr
      _ = _ := by ring

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma windowTrace_eq (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) :
    windowTrace A h u p s = ∑ i, ∑ j, ∑ k,
      (h^3:ℝ)* (A 0 i j*A 1 j k*A 2 k i) *
        ((oddWindow s (u i-p 0)*oddWindow s (u j-p 1)*oddWindow s (u k-p 2):ℝ):ℂ) := by
  unfold windowTrace windowDiags heatArray
  have hg (v : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) v i :=
    (weight_pos hh (by positivity) _ _).le
  rw [trace_weighted_triangle A (heatWeights h u p (fun _ => (11/10)*s))
    (fun v i => windowRatio s (u i-p v)) hg]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he (v : Three) (i : ι) : heatWeights h u p (fun _ => (11/10)*s) v i * windowRatio s (u i-p v) =
      h*oddWindow s (u i-p v) := by
    unfold heatWeights weight
    rw [mul_assoc,density_mul_windowRatio hs]
  rw [he,he,he]
  push_cast
  ring

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_equal_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    density s (a-p)*density s (b+p) =
      density (2*s) (a+b)*density (s/2) (p-(a-b)/2) := by
  rw [show b+p = -((-b)-p) by ring,density_neg,density_product hs hs]
  congr 1
  · congr 1 <;> ring
  · congr 1
    · field_simp; ring
    · field_simp; ring

lemma weighted_signed_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    (a-p)*(b+p)*density s (a-p)*density s (b+p) =
      density (2*s) (a+b)*(cubic ((a+b)^2/4) 0 (-1) 0 (p-(a-b)/2)*density (s/2) (p-(a-b)/2)) := by
  rw [mul_assoc ((a-p)*(b+p)),density_equal_pair hs]
  unfold cubic
  ring

lemma integral_signed_pair {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, (a-p)*(b+p)*density s (a-p)*density s (b+p)) =
      ((a+b)^2/4-s/2)*density (2*s) (a+b) := by
  simp_rw [weighted_signed_pair hs]
  rw [integral_const_mul,integral_shifted_cubic_density (by positivity : 0 < s/2)]
  ring

lemma integral_oddWindow_pair {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, oddWindow s (a-p)*oddWindow s (b+p)) =
      (((a+b)^2/4-s/2)*density (2*s) (a+b))/s := by
  have hr := (Real.sqrt_pos.mpr hs).ne'
  have he (p : ℝ) : oddWindow s (a-p)*oddWindow s (b+p) =
      ((a-p)*(b+p)*density s (a-p)*density s (b+p))/s := by
    unfold oddWindow
    field_simp
    rw [Real.sq_sqrt hs.le]
    ring
  simp_rw [he]
  rw [integral_div,integral_signed_pair hs]

lemma density_one_two_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    density s (a-p)*density (2*s) (b+p) =
      density (3*s) (a+b)*density (2*s/3) (p-(2*a-b)/3) := by
  rw [show b+p = -((-b)-p) by ring,density_neg,density_product hs (by positivity : 0 < 2*s)]
  congr 1
  · congr 1 <;> ring
  · congr 1
    · field_simp; ring
    · field_simp; ring

lemma weighted_signed_outer {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    (a-p)*density s (a-p)*(((b+p)^2/4-s/2)*density (2*s) (b+p)) =
      density (3*s) (a+b)*(cubic ((a+b)^3/27-(a+b)*s/6) (s/2) (-(a+b)/4) (-1/4)
        (p-(2*a-b)/3)*density (2*s/3) (p-(2*a-b)/3)) := by
  calc
    _ = ((a-p)*((b+p)^2/4-s/2))*(density s (a-p)*density (2*s) (b+p)) := by ring
    _ = _ := by rw [density_one_two_pair hs]; unfold cubic; ring

lemma integral_signed_outer {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, (a-p)*density s (a-p)*(((b+p)^2/4-s/2)*density (2*s) (b+p))) =
      ((a+b)^3/27-(a+b)*s/3)*density (3*s) (a+b) := by
  simp_rw [weighted_signed_outer hs]
  rw [integral_const_mul,integral_shifted_cubic_density (by positivity : 0 < 2*s/3)]
  ring

def signedKernel (s t : ℝ) : ℝ :=
  (t^3/27-t*s/3)/(s*Real.sqrt s)*density (3*s) t

lemma integral_oddWindow_triple {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    (∫ z : ℝ×ℝ, oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) =
      signedKernel s (a+b+c) := by
  rw [Measure.volume_eq_prod,integral_prod _ (oddWindow_triple_integrable hs a b c)]
  have inner (p : ℝ) : (∫ q : ℝ, oddWindow s (a-p)*oddWindow s (b-q)*oddWindow s (c+p+q)) =
      oddWindow s (a-p)*((((b+c+p)^2/4-s/2)*density (2*s) (b+c+p))/s) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_oddWindow_pair hs]
    congr 3 <;> ring_nf
  simp_rw [inner]
  have he (p : ℝ) : oddWindow s (a-p)*((((b+c+p)^2/4-s/2)*density (2*s) (b+c+p))/s) =
      ((a-p)*density s (a-p)*(((b+c+p)^2/4-s/2)*density (2*s) (b+c+p)))/(s*Real.sqrt s) := by
    unfold oddWindow
    ring
  simp_rw [he]
  rw [integral_div,integral_signed_outer hs]
  unfold signedKernel
  rw [show a+(b+c) = a+b+c by ring]
  ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma abs_hsReal_le_sum (X Y : Matrix ι ι ℂ) :
    |hsReal X Y| ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y i j‖ := by
  unfold hsReal traceReal
  calc
    _ ≤ ‖(Xᴴ * Y).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j, ∑ i, ‖star (X i j) * Y i j‖ := by
      unfold Matrix.trace
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact norm_sum_le _ _
    _ = _ := by simp only [norm_mul,norm_star]; rw [Finset.sum_comm]

def segmentMatrix (A B : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  (1-t) • A + t • B

lemma segmentMatrix_hasDerivAt (A B : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (segmentMatrix A B) (B-A) t := by
  convert! (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const A).add
    ((hasDerivAt_id t).smul_const B) using 1; simp [sub_eq_add_neg,add_comm]

lemma segmentEnergy_hasDerivAt (A B : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun s => energy ((segmentMatrix A B s)ᴴ * segmentMatrix A B s))
      (3 * hsReal (segmentMatrix A B t * CFC.sqrt ((segmentMatrix A B t)ᴴ * segmentMatrix A B t)) (B-A)) t := by
  exact (energyGram_hasFDerivAt _).comp_hasDerivAt t (segmentMatrix_hasDerivAt A B t)

omit [Fintype ι] [DecidableEq ι] in
lemma segmentMatrix_norm_entry_le (A B : Matrix ι ι ℂ) (M : ι → ι → ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ M i j) (hB : ∀ i j, ‖B i j‖ ≤ M i j)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (i j : ι) :
    ‖segmentMatrix A B t i j‖ ≤ M i j := by
  calc
    _ ≤ ‖((1-t):ℝ) • A i j‖ + ‖t • B i j‖ := norm_add_le _ _
    _ = (1-t)*‖A i j‖+t*‖B i j‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ht.1,
        abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-t)]
    _ ≤ (1-t)*M i j+t*M i j := add_le_add
      (mul_le_mul_of_nonneg_left (hA i j) (by linarith [ht.2]))
      (mul_le_mul_of_nonneg_left (hB i j) ht.1)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma rowNorm_mono {X Y : Matrix ι ι ℂ} (h : ∀ i j, ‖X i j‖ ≤ ‖Y i j‖) (i : ι) :
    rowNorm X i ≤ rowNorm Y i := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun j _ => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (h i j))

omit [DecidableEq ι] in
lemma colNorm_mono {X Y : Matrix ι ι ℂ} (h : ∀ i j, ‖X i j‖ ≤ ‖Y i j‖) (j : ι) :
    colNorm X j ≤ colNorm Y j := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun i _ => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (h i j))

lemma energy_jump_le (A B M : Matrix ι ι ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ ‖M i j‖) (hB : ∀ i j, ‖B i j‖ ≤ ‖M i j‖) :
    |energy (Bᴴ*B) - energy (Aᴴ*A)| ≤
      3 * ∑ i, ∑ j, rowNorm M i * colNorm M j * ‖(B-A) i j‖ := by
  have hb (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
      ‖3 * hsReal (segmentMatrix A B t * CFC.sqrt ((segmentMatrix A B t)ᴴ * segmentMatrix A B t)) (B-A)‖ ≤
      3 * ∑ i, ∑ j, rowNorm M i * colNorm M j * ‖(B-A) i j‖ := by
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 3), Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (abs_hsReal_le_sum _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (entry_gradient_le _ i j).trans
    have he := segmentMatrix_norm_entry_le A B (fun i j => ‖M i j‖) hA hB ⟨ht.1,ht.2.le⟩
    exact mul_le_mul (rowNorm_mono he i) (colNorm_mono he j) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (segmentEnergy_hasDerivAt A B t).hasDerivWithinAt) hb
  simpa [segmentMatrix,Real.norm_eq_abs] using h
end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowNorm_rowStar (A : Three → Matrix ι ι ℂ) (v : Three) (i : ι) :
    rowNorm (rowStar A v) (v,i) = Real.sqrt (∑ w, ∑ j, ‖triangleBlocks A v w i j‖^2) := by
  simp only [rowNorm,Fintype.sum_prod_type,rowStar_apply,ite_true]

lemma colNorm_rowStar (A : Three → Matrix ι ι ℂ) (v w : Three) (j : ι) :
    colNorm (rowStar A v) (w,j) = Real.sqrt (∑ i, ‖triangleBlocks A v w i j‖^2) := by
  unfold colNorm
  simp only [Fintype.sum_prod_type,rowStar_apply]
  congr 1
  have he (a : Three) : (∑ i, ‖if a = v then triangleBlocks A a w i j else 0‖^2) =
      if a = v then (∑ i, ‖triangleBlocks A a w i j‖^2) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  simp

lemma rowStar_norm_mono {A B : Three → Matrix ι ι ℂ}
    (h : ∀ v i j, ‖A v i j‖ ≤ ‖B v i j‖) (v : Three) (a b : BlockSpace ι) :
    ‖rowStar A v a b‖ ≤ ‖rowStar B v a b‖ := by
  simp only [rowStar_apply]
  by_cases hv : a.1 = v
  · simp only [ite_eq_left hv]
    unfold triangleBlocks
    split_ifs <;> first | exact le_rfl | exact h _ _ _ | simpa only [Matrix.conjTranspose_apply,norm_star] using h _ _ _
  · simp [hv]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_norm (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) (i j : ι) :
    ‖weightedArray A g v i j‖ = Real.sqrt (g v i)*‖A v i j‖*Real.sqrt (g (v+1) j) := by
  simp only [weightedArray,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_norm_sq (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) (i j : ι) :
    ‖weightedArray A g v i j‖^2 = g v i*‖A v i j‖^2*g (v+1) j := by
  rw [weightedArray_norm,mul_pow,mul_pow,Real.sq_sqrt (hg v i),Real.sq_sqrt (hg (v+1) j)]

lemma rowNorm_weightedStar_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (i : ι) :
    rowNorm (rowStar (weightedArray A g) 0) (0,i) =
      Real.sqrt (g 0 i) * Real.sqrt ((∑ j, ‖A 0 i j‖^2*g 1 j)+(∑ j, ‖A 2 j i‖^2*g 2 j)) := by
  rw [rowNorm_rowStar,Fin.sum_univ_three]
  simp only [triangleBlocks,show (0:Three) ≠ 1 by decide,show (1:Three) ≠ 0 by decide,show (2:Three) ≠ 0 by decide,show (2:Three) ≠ 1 by decide,ite_true,ite_false,Matrix.zero_apply,Matrix.conjTranspose_apply,norm_star,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_add]
  simp_rw [weightedArray_norm_sq A g hg]
  simp only [show (0:Three)+1=1 by decide,show (2:Three)+1=0 by decide]
  have he : (∑ j, g 0 i*‖A 0 i j‖^2*g 1 j)+(∑ j, g 2 j*‖A 2 j i‖^2*g 0 i) =
      g 0 i*((∑ j, ‖A 0 i j‖^2*g 1 j)+(∑ j, ‖A 2 j i‖^2*g 2 j)) := by
    simp only [mul_add,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he,Real.sqrt_mul (hg 0 i)]

lemma colNorm_weightedStar_zero_one (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (j : ι) :
    colNorm (rowStar (weightedArray A g) 0) (1,j) =
      Real.sqrt (g 1 j) * Real.sqrt (∑ i, ‖A 0 i j‖^2*g 0 i) := by
  rw [colNorm_rowStar]
  simp only [triangleBlocks,show (0:Three) ≠ 1 by decide,show (1:Three) ≠ 0 by decide,ite_true,ite_false]
  simp_rw [weightedArray_norm_sq A g hg]
  rw [show (0:Three)+1=1 by decide]
  have he : (∑ i, g 0 i*‖A 0 i j‖^2*g 1 j) = g 1 j*(∑ i, ‖A 0 i j‖^2*g 0 i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,Real.sqrt_mul (hg 1 j)]

lemma rowNorm_weightedStar_one (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (j : ι) :
    rowNorm (rowStar (weightedArray A g) 1) (1,j) =
      Real.sqrt (g 1 j) * Real.sqrt ((∑ i, ‖A 0 i j‖^2*g 0 i)+(∑ i, ‖A 1 j i‖^2*g 2 i)) := by
  rw [rowNorm_rowStar,Fin.sum_univ_three]
  simp only [triangleBlocks,show (1:Three) ≠ 0 by decide,show (2:Three) ≠ 0 by decide,show (2:Three) ≠ 1 by decide,ite_true,ite_false,Matrix.zero_apply,Matrix.conjTranspose_apply,norm_star,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,add_zero]
  simp_rw [weightedArray_norm_sq A g hg]
  simp only [show (0:Three)+1=1 by decide,show (1:Three)+1=2 by decide]
  have he : (∑ i, g 0 i*‖A 0 i j‖^2*g 1 j)+(∑ i, g 1 j*‖A 1 j i‖^2*g 2 i) =
      g 1 j*((∑ i, ‖A 0 i j‖^2*g 0 i)+(∑ i, ‖A 1 j i‖^2*g 2 i)) := by
    simp only [mul_add,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he,Real.sqrt_mul (hg 1 j)]

lemma colNorm_weightedStar_one_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (i : ι) :
    colNorm (rowStar (weightedArray A g) 1) (0,i) =
      Real.sqrt (g 0 i) * Real.sqrt (∑ j, ‖A 0 i j‖^2*g 1 j) := by
  rw [colNorm_rowStar]
  simp only [triangleBlocks,show (1:Three) ≠ 0 by decide,ite_true,ite_false,Matrix.conjTranspose_apply,norm_star]
  simp_rw [weightedArray_norm_sq A g hg]
  rw [show (0:Three)+1=1 by decide]
  have he : (∑ j, g 0 i*‖A 0 i j‖^2*g 1 j) = g 0 i*(∑ j, ‖A 0 i j‖^2*g 1 j) := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he,Real.sqrt_mul (hg 0 i)]

end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
def replaceZero (A : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) : Three → Matrix ι ι ℂ :=
  fun v => if v = 0 then B else A v

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_sub (A B : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    weightedArray (A-B) g = weightedArray A g-weightedArray B g := by
  ext v i j
  simp [weightedArray,mul_sub,sub_mul]

lemma rowStar_sub (A B : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar (A-B) v = rowStar A v-rowStar B v := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [rowStar_apply,Matrix.sub_apply]
  by_cases hv : a = v
  · simp only [ite_eq_left hv]
    fin_cases a <;> fin_cases b <;> simp [triangleBlocks]
  · simp only [ite_eq_right hv,sub_self]

omit [Fintype ι] [DecidableEq ι] in
lemma replaceZero_sub (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) :
    replaceZero A B-replaceZero A C = replaceZero 0 (B-C) := by
  ext v i j
  by_cases hv : v=0 <;> simp [replaceZero,hv]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_replaceZero_zero (B : Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    weightedArray (replaceZero 0 B) g = replaceZero 0 (fun i j => (Real.sqrt (g 0 i):ℂ)*B i j*(Real.sqrt (g 1 j):ℂ)) := by
  ext v i j
  by_cases hv : v=0
  · subst v
    simp [weightedArray,replaceZero,show (0:Three)+1=1 by decide]
  · simp [weightedArray,replaceZero,hv]

lemma rowStar_replaceZero_two (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (g : Three → ι → ℝ) :
    rowStar (weightedArray (replaceZero A B) g) 2 = rowStar (weightedArray (replaceZero A C) g) 2 := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [rowStar_apply]
  by_cases ha : a=2
  · subst a
    simp only [ite_true]
    fin_cases b <;> simp [triangleBlocks,weightedArray,replaceZero]
  · simp [ha]

lemma jump_sum_zero (M : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :
    (∑ a, ∑ b, rowNorm (rowStar M 0) a*colNorm (rowStar M 0) b*‖rowStar (replaceZero 0 B) 0 a b‖) =
      ∑ i, ∑ j, rowNorm (rowStar M 0) (0,i)*colNorm (rowStar M 0) (1,j)*‖B i j‖ := by
  simp only [Fintype.sum_prod_type,rowStar_apply]
  simp [Fin.sum_univ_three,triangleBlocks,replaceZero]

lemma jump_sum_one (M : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :
    (∑ a, ∑ b, rowNorm (rowStar M 1) a*colNorm (rowStar M 1) b*‖rowStar (replaceZero 0 B) 1 a b‖) =
      ∑ i, ∑ j, rowNorm (rowStar M 1) (1,j)*colNorm (rowStar M 1) (0,i)*‖B i j‖ := by
  simp only [Fintype.sum_prod_type,rowStar_apply]
  simp only [Fin.sum_univ_three]
  simp only [show (1:Three) ≠ 0 by decide, show (2:Three) ≠ 1 by decide,show (0:Three) ≠ 1 by decide,ite_true,ite_false,triangleBlocks,replaceZero]
  simp
  rw [Finset.sum_comm]

lemma weightedStar_replaceZero_norm_le (A : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (g : Three → ι → ℝ) (v : Three) (a b : BlockSpace ι) :
    ‖rowStar (weightedArray (replaceZero A B) g) v a b‖ ≤ ‖rowStar (weightedArray A g) v a b‖ := by
  apply rowStar_norm_mono _ v a b
  intro w i j
  simp only [weightedArray_norm]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  by_cases hw : w=0
  · subst w
    simpa only [replaceZero,ite_true] using hB i j
  · simp [replaceZero,hw]
end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma sqrt_weight_product_le {a b x y d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d) :
    (Real.sqrt a*Real.sqrt x)*(Real.sqrt b*Real.sqrt y)*(Real.sqrt a*d*Real.sqrt b) ≤ d*a*b*(x+y)/2 := by
  have hxy : Real.sqrt x*Real.sqrt y ≤ (x+y)/2 := by
    nlinarith [Real.sq_sqrt hx,Real.sq_sqrt hy,sq_nonneg (Real.sqrt x-Real.sqrt y)]
  calc
    _ = (Real.sqrt a*Real.sqrt a)*(Real.sqrt b*Real.sqrt b)*d*(Real.sqrt x*Real.sqrt y) := by ring
    _ = d*a*b*(Real.sqrt x*Real.sqrt y) := by rw [Real.mul_self_sqrt ha,Real.mul_self_sqrt hb]; ring
    _ ≤ d*a*b*((x+y)/2) := mul_le_mul_of_nonneg_left hxy (by positivity)
    _ = _ := by ring

def jumpSlicing (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (i j : ι) : ℝ :=
  2*(∑ m, ‖A 0 i m‖^2*g 1 m)+2*(∑ m, ‖A 0 m j‖^2*g 0 m)+
    (∑ m, ‖A 2 m i‖^2*g 2 m)+(∑ m, ‖A 1 j m‖^2*g 2 m)

lemma energy_replaceZero_jump_zero (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |energy (starGram (weightedArray (replaceZero A B) g) 0)-energy (starGram (weightedArray (replaceZero A C) g) 0)| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*
        ((∑ m, ‖A 0 i m‖^2*g 1 m)+(∑ m, ‖A 2 m i‖^2*g 2 m)+(∑ m, ‖A 0 m j‖^2*g 0 m)) := by
  have hj := energy_jump_le (rowStar (weightedArray (replaceZero A C) g) 0)
    (rowStar (weightedArray (replaceZero A B) g) 0) (rowStar (weightedArray A g) 0)
    (weightedStar_replaceZero_norm_le A C hC g 0) (weightedStar_replaceZero_norm_le A B hB g 0)
  rw [← rowStar_sub,← weightedArray_sub,replaceZero_sub,weightedArray_replaceZero_zero,jump_sum_zero (weightedArray A g) (fun i j => (Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ))] at hj
  apply hj.trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [rowNorm_weightedStar_zero A g hg,colNorm_weightedStar_zero_one A g hg]
  have hnorm : ‖(Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ)‖ =
      Real.sqrt (g 0 i)*‖B i j-C i j‖*Real.sqrt (g 1 j) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Matrix.sub_apply]
  rw [hnorm]
  have h := sqrt_weight_product_le
    (x := (∑ m, ‖A 0 i m‖^2*g 1 m)+(∑ m, ‖A 2 m i‖^2*g 2 m))
    (y := ∑ m, ‖A 0 m j‖^2*g 0 m) (hg 0 i) (hg 1 j)
    (add_nonneg (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 1 m)))
      (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 2 m))))
    (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 0 m))) (norm_nonneg (B i j-C i j))
  linarith

lemma energy_replaceZero_jump_one (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |energy (starGram (weightedArray (replaceZero A B) g) 1)-energy (starGram (weightedArray (replaceZero A C) g) 1)| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*
        ((∑ m, ‖A 0 m j‖^2*g 0 m)+(∑ m, ‖A 1 j m‖^2*g 2 m)+(∑ m, ‖A 0 i m‖^2*g 1 m)) := by
  have hj := energy_jump_le (rowStar (weightedArray (replaceZero A C) g) 1)
    (rowStar (weightedArray (replaceZero A B) g) 1) (rowStar (weightedArray A g) 1)
    (weightedStar_replaceZero_norm_le A C hC g 1) (weightedStar_replaceZero_norm_le A B hB g 1)
  rw [← rowStar_sub,← weightedArray_sub,replaceZero_sub,weightedArray_replaceZero_zero,jump_sum_one (weightedArray A g) (fun i j => (Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ))] at hj
  apply hj.trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [rowNorm_weightedStar_one A g hg,colNorm_weightedStar_one_zero A g hg]
  have hnorm : ‖(Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ)‖ =
      Real.sqrt (g 1 j)*‖B i j-C i j‖*Real.sqrt (g 0 i) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Matrix.sub_apply]
    ring
  rw [hnorm]
  have h := sqrt_weight_product_le
    (x := (∑ m, ‖A 0 m j‖^2*g 0 m)+(∑ m, ‖A 1 j m‖^2*g 2 m))
    (y := ∑ m, ‖A 0 i m‖^2*g 1 m) (hg 1 j) (hg 0 i)
    (add_nonneg (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 0 m)))
      (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 2 m))))
    (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 1 m))) (norm_nonneg (B i j-C i j))
  nlinarith
end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_weight_param {E : Type uE} [TopologicalSpace E] (h u : ℝ)
    {p σ : E → ℝ} (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ t, 0 < σ t) :
    Continuous (fun t => weight h u (p t) (σ t)) := by
  unfold weight density
  have hden : ∀ t, Real.sqrt (2*Real.pi*σ t) ≠ 0 := fun t => (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hpos t))).ne'
  apply continuous_const.mul
  apply Continuous.mul
  · exact (Real.continuous_sqrt.comp (continuous_const.mul hσ)).inv₀ hden
  · apply Real.continuous_exp.comp
    exact ((continuous_const.sub hp).pow 2 |>.neg).div (continuous_const.mul hσ) (fun t => (mul_pos (by norm_num) (hpos t)).ne')

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_heatArray_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => heatArray A h u (p t) (σ t) v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hw (w : Three) (k : ι) : Continuous (fun t => (Real.sqrt (heatWeights h u (p t) (σ t) w k) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_weight_param h (u k) ((continuous_apply w).comp hp) ((continuous_apply w).comp hσ) (hpos · w)))
  exact ((hw v i).mul continuous_const).mul (hw (v+1) j)

lemma continuous_heatRow_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => rowStar (heatArray A h u (p t) (σ t)) v) := by
  have he := continuous_heatArray_param A h u hp hσ hpos
  have hb (a b : Three) : Continuous (fun t => triangleBlocks (heatArray A h u (p t) (σ t)) a b) := by
    unfold triangleBlocks
    split_ifs <;> first | exact continuous_const | exact he _ | exact (he _).star
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [rowStar_apply]
  by_cases hv : a.1 = v
  · simp only [ite_eq_left hv]
    exact (continuous_apply b.2).comp ((continuous_apply a.2).comp (hb a.1 b.1))
  · simp only [ite_eq_right hv]
    exact continuous_const
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
noncomputable section

lemma weight_three_integrable {h : ℝ} (hh : 0 < h) (a b c d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h c (chart 2 d z v) (σ v)) := by
  have hi := weight_pair_integrable h a b d σ hσ 0 2
  have he : (0:Three)+1=1 := by decide
  rw [he] at hi
  apply (hi.mul_const (h*density (σ v) 0)).mono'
  · have hc (k : Three) : Continuous (fun z : ℝ×ℝ => chart 2 d z k) :=
      (continuous_apply k).comp ((chart_continuous 2).comp (continuous_const.prodMk continuous_id))
    exact ((continuous_weight_param h a (hc 0) continuous_const (fun _ => hσ 0)).mul
      (continuous_weight_param h b (hc 1) continuous_const (fun _ => hσ 1)) |>.mul
      (continuous_weight_param h c (hc v) continuous_const (fun _ => hσ v))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg
      (weight_pos hh (hσ 0) _ _).le (weight_pos hh (hσ 1) _ _).le) (weight_pos hh (hσ v) _ _).le)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (density_le_zero (σ v) _) hh.le)
      (mul_nonneg (weight_pos hh (hσ 0) _ _).le (weight_pos hh (hσ 1) _ _).le)

lemma planeIntegral_weight_repeat_zero (h a b c d : ℝ) (σ : Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 0) (σ 0)) d =
      h^3*density (2*σ 0) (a-c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 0) (c-z.1)) ∂volume.prod volume) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 0) (c-z.1)) =
      h^3*((density (σ 0) (a-z.1)*density (σ 0) (c-z.1))*density (σ 1) (b-z.2)) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul (fun p => density (σ 0) (a-p)*density (σ 0) (c-p)) (fun q => density (σ 1) (b-q)),integral_density_product (hσ 0) (hσ 0),integral_sub_left_eq_self,integral_density (hσ 1),mul_one]
  congr 2
  ring

lemma planeIntegral_weight_repeat_one (h a b c d : ℝ) (σ : Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 1) (σ 1)) d =
      h^3*density (2*σ 1) (b-c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 1) (c-z.2)) ∂volume.prod volume) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 1) (c-z.2)) =
      h^3*(density (σ 0) (a-z.1)*(density (σ 1) (b-z.2)*density (σ 1) (c-z.2))) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul (fun p => density (σ 0) (a-p)) (fun q => density (σ 1) (b-q)*density (σ 1) (c-q)),integral_density_product (hσ 1) (hσ 1),integral_sub_left_eq_self,integral_density (hσ 0),one_mul]
  congr 2
  ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

lemma weight_slice_integrable {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (c f : ι → ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*
      ∑ m, f m*weight h (c m) (chart 2 d z v) (σ v)) := by
  have hi : Integrable (fun z : ℝ×ℝ => ∑ m, f m*(weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h (c m) (chart 2 d z v) (σ v))) :=
    integrable_finsetSum _ (fun m _ => (weight_three_integrable hh a b (c m) d σ hσ v).const_mul (f m))
  convert hi using 1
  ext z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma planeIntegral_weight_slice {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (c f : ι → ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p v) (σ v)) d =
      ∑ m, f m*planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h (c m) (p v) (σ v)) d := by
  unfold planeIntegral
  have he (z : ℝ×ℝ) : weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*
      (∑ m, f m*weight h (c m) (chart 2 d z v) (σ v)) =
      ∑ m, f m*(weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*weight h (c m) (chart 2 d z v) (σ v)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun m _ => (weight_three_integrable hh a b (c m) d σ hσ v).const_mul (f m))]
  simp only [integral_const_mul]

lemma weight_slice_zero_integral {h : ℝ} (hh : 0 < h) (a b d : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 0) (σ 0)) d = h^2*∑ m, f m*(h*density (2*σ 0) (a-c m)) := by
  rw [planeIntegral_weight_slice hh a b d c f σ hσ 0]
  simp_rw [planeIntegral_weight_repeat_zero h a b _ d σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma weight_slice_one_integral {h : ℝ} (hh : 0 < h) (a b d : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 1) (σ 1)) d = h^2*∑ m, f m*(h*density (2*σ 1) (b-c m)) := by
  rw [planeIntegral_weight_slice hh a b d c f σ hσ 1]
  simp_rw [planeIntegral_weight_repeat_one h a b _ d σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma weight_slice_two_integral {h : ℝ} (hh : 0 < h) (a b : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 2) (σ 2)) 0 = h^2*∑ m, f m*(h*density (σ 0+σ 1+σ 2) (a+b+c m)) := by
  rw [planeIntegral_weight_slice hh a b 0 c f σ hσ 2]
  simp_rw [planeIntegral_weight_triple h a b _ σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma energy_le_trace_sqrt {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy P ≤ traceReal P * Real.sqrt (traceReal P) := by
  have he : traceReal P = ∑ i, hP.isHermitian.eigenvalues i := by
    have hh := congrArg Complex.re hP.isHermitian.trace_eq_sum_eigenvalues
    simp only [Complex.re_sum] at hh
    exact hh
  rw [energy_spectral hP,he,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hP.eigenvalues_nonneg i)
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)

omit [DecidableEq ι] in
lemma traceReal_gram (R : Matrix ι ι ℂ) :
    traceReal (Rᴴ*R) = ∑ i, ∑ j, ‖R i j‖^2 := by
  unfold traceReal Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [Finset.sum_comm]

lemma energy_gram_le_HS (R : Matrix ι ι ℂ) :
    energy (Rᴴ*R) ≤ (∑ i, ∑ j, ‖R i j‖^2) * Real.sqrt (∑ i, ∑ j, ‖R i j‖^2) := by
  simpa only [traceReal_gram] using energy_le_trace_sqrt (Matrix.posSemidef_conjTranspose_mul_self R)

end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert
open scoped BigOperators

lemma sum_sq_le_sum_mul_of_nonneg {ι : Type uι} (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) (hz : ∀ i ∈ s, 0 ≤ z i)
    (he : ∀ i ∈ s, x i ^ 2 = y i * z i) :
    (∑ i ∈ s, x i)^2 ≤ (∑ i ∈ s, y i)*(∑ i ∈ s, z i) := by
  have hp i (hi : i ∈ s) : Real.sqrt (y i) * Real.sqrt (z i) = x i := by
    rw [← Real.sqrt_mul (hy i hi),← he i hi,Real.sqrt_sq (hx i hi)]
  have hh := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => Real.sqrt (y i)) (fun i => Real.sqrt (z i))
  have hys : (∑ i ∈ s, (Real.sqrt (y i))^2) = ∑ i ∈ s, y i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hy i hi))
  have hzs : (∑ i ∈ s, (Real.sqrt (z i))^2) = ∑ i ∈ s, z i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hz i hi))
  rw [hys,hzs] at hh
  have he' : (∑ i ∈ s, Real.sqrt (y i) * Real.sqrt (z i)) = ∑ i ∈ s, x i :=
    Finset.sum_congr rfl hp
  rw [he'] at hh
  have hq := sq_le_sq₀ (Finset.sum_nonneg hx) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr hh
  simpa only [mul_pow,Real.sq_sqrt (Finset.sum_nonneg hy),Real.sq_sqrt (Finset.sum_nonneg hz)] using hq

lemma weighted_cubic {ι : Type uι} (s : Finset ι) (a w : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, a i^2*w i) * Real.sqrt (∑ i ∈ s, a i^2*w i) ≤
      (∑ i ∈ s, a i^3*w i) * Real.sqrt (∑ i ∈ s, w i) := by
  let T := ∑ i ∈ s, a i^2*w i
  let B := ∑ i ∈ s, a i^3*w i
  let L := ∑ i ∈ s, a i*w i
  let W := ∑ i ∈ s, w i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i hi => mul_nonneg (sq_nonneg _) (hw i hi))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (pow_nonneg (ha i hi) _) (hw i hi))
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (hw i hi))
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hTL : T^2 ≤ B*L := sum_sq_le_sum_mul_of_nonneg s _ _ _
    (fun i hi => mul_nonneg (sq_nonneg _) (hw i hi))
    (fun i hi => mul_nonneg (pow_nonneg (ha i hi) _) (hw i hi))
    (fun i hi => mul_nonneg (ha i hi) (hw i hi)) (fun i _ => by ring)
  have hLW : L^2 ≤ T*W := sum_sq_le_sum_mul_of_nonneg s _ _ _
    (fun i hi => mul_nonneg (ha i hi) (hw i hi))
    (fun i hi => mul_nonneg (sq_nonneg _) (hw i hi)) hw (fun i _ => by ring)
  change T * Real.sqrt T ≤ B * Real.sqrt W
  by_cases ht : T = 0
  · simpa only [ht,zero_mul] using mul_nonneg hB (Real.sqrt_nonneg W)
  have htpos : 0 < T := hT.lt_of_ne' ht
  have hq := mul_le_mul hTL hTL (sq_nonneg T) (mul_nonneg hB hL)
  have hh := mul_le_mul_of_nonneg_left hLW (sq_nonneg B)
  have hc : T^3 ≤ B^2 * W := by
    by_contra! hc
    have hp := mul_pos htpos (sub_pos.mpr hc)
    nlinarith
  apply (sq_le_sq₀ (mul_nonneg hT (Real.sqrt_nonneg T)) (mul_nonneg hB (Real.sqrt_nonneg W))).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hT,Real.sq_sqrt hW]
  nlinarith [hc]
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

def hsSquare (R : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖R i j‖^2

def hsCube (R : Matrix ι ι ℂ) : ℝ := hsSquare R * Real.sqrt (hsSquare R)

lemma hsSquare_nonneg (R : Matrix ι ι ℂ) : 0 ≤ hsSquare R :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma hsSquare_star (R : Matrix ι ι ℂ) : hsSquare Rᴴ = hsSquare R := by
  unfold hsSquare
  simp only [Matrix.conjTranspose_apply,norm_star]
  rw [Finset.sum_comm]

lemma hsSquare_rowStar_sum [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    hsSquare (rowStar A v) = ∑ w, hsSquare (triangleBlocks A v w) := by
  unfold hsSquare
  simp only [Fintype.sum_prod_type,rowStar_apply]
  have he (a : Three) : (∑ i, ∑ b : Three, ∑ j, ‖if a = v then triangleBlocks A a b i j else 0‖^2) =
      if a = v then (∑ b : Three, ∑ i, ∑ j, ‖triangleBlocks A a b i j‖^2) else 0 := by
    split_ifs with ha
    · exact Finset.sum_comm
    · simp
  simp_rw [he]
  simp

lemma hsSquare_zero : hsSquare (0 : Matrix ι ι ℂ) = 0 := by simp [hsSquare]

lemma hsSquare_rowStar [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    hsSquare (rowStar A v) = hsSquare (A v) + hsSquare (A (v+2)) := by
  rw [hsSquare_rowStar_sum,Fin.sum_univ_three]
  fin_cases v <;> simp [triangleBlocks,hsSquare_zero,hsSquare_star]
  ac_rfl

lemma cubic_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)*Real.sqrt (a+b) ≤ Real.sqrt 2*(a*Real.sqrt a+b*Real.sqrt b) := by
  have hh := TriangularHilbert.weighted_cubic (Finset.univ : Finset (Fin 2))
    ![Real.sqrt a,Real.sqrt b] (fun _ => 1)
    (by intro i _; fin_cases i <;> simp [Real.sqrt_nonneg]) (by simp)
  have he (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x)^3 = x*Real.sqrt x := by
    rw [pow_succ,Real.sq_sqrt hx]
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    Real.sq_sqrt ha,Real.sq_sqrt hb,he a ha,he b hb,mul_one,one_mul,one_add_one_eq_two,mul_comm] using hh

lemma energy_star_le_hsCube [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    energy (starGram A v) ≤ Real.sqrt 2*(hsCube (A v)+hsCube (A (v+2))) := by
  have hh := energy_gram_le_HS (rowStar A v)
  change energy (starGram A v) ≤ hsSquare (rowStar A v)*Real.sqrt (hsSquare (rowStar A v)) at hh
  rw [hsSquare_rowStar] at hh
  exact hh.trans (cubic_add_le (hsSquare_nonneg _) (hsSquare_nonneg _))

lemma hsSquare_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    hsSquare (weightedArray A g v) = ∑ i, ∑ j, ‖A v i j‖^2 * (g v i*g (v+1) j) := by
  unfold hsSquare weightedArray
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt (hg v i),Real.sq_sqrt (hg (v+1) j)]
  ring

lemma hsCube_weightedArray_le (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ v, (∑ i, g v i) ≤ M) (v : Three) :
    hsCube (weightedArray A g v) ≤ M * ∑ i, ∑ j, ‖A v i j‖^3 * (g v i*g (v+1) j) := by
  have hh := TriangularHilbert.weighted_cubic (Finset.univ : Finset (ι×ι))
    (fun a => ‖A v a.1 a.2‖) (fun a => g v a.1*g (v+1) a.2)
    (fun _ _ => norm_nonneg _) (fun a _ => mul_nonneg (hg _ _) (hg _ _))
  simp only [Fintype.sum_prod_type] at hh
  have hw : (∑ i, ∑ j, g v i*g (v+1) j) ≤ M^2 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul,pow_two]
    exact mul_le_mul (hm v) (hm (v+1)) (Finset.sum_nonneg (fun j _ => hg _ j)) hM
  have hs : Real.sqrt (∑ i, ∑ j, g v i*g (v+1) j) ≤ M := by
    simpa only [Real.sqrt_sq hM] using Real.sqrt_le_sqrt hw
  unfold hsCube
  rw [hsSquare_weightedArray A g hg]
  exact hh.trans (by
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (mul_nonneg (hg _ _) (hg _ _))))))
end
end TriangularHilbert.MatrixEnergy
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def arrayCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) : ℝ :=
  ∑ v, ∑ i, ∑ j, h^2*‖A v i j‖^3

lemma sum_three_shift (f : Three → ℝ) : (∑ v, f (v+2)) = ∑ v, f v := by
  simp [Fin.sum_univ_three]
  ring

lemma totalPlaneEnergy_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : 0 ≤ totalPlaneEnergy A h u d σ := by
  apply Finset.sum_nonneg
  intro v _
  exact integral_nonneg (fun _ => energy_gram_nonneg _)

lemma totalPlaneEnergy_le_mass (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v)
    {M : ℝ} (hM : 0 ≤ M) (hm : ∀ p v, (∑ i, heatWeights h u p σ v i) ≤ M) :
    totalPlaneEnergy A h u d σ ≤ 2*Real.sqrt 2*M*arrayCubic A h := by
  have hg p v i : 0 ≤ heatWeights h u p σ v i := (weight_pos hh (hσ v) (u i) (p v)).le
  have hb p v : heatEnergy A h u p σ v ≤ Real.sqrt 2*M*(edgeCubic A h u p σ v+edgeCubic A h u p σ (v+2)) := by
    have he := energy_star_le_hsCube (heatArray A h u p σ) v
    have h1 := hsCube_weightedArray_le A (heatWeights h u p σ) (hg p) hM (hm p) v
    have h2 := hsCube_weightedArray_le A (heatWeights h u p σ) (hg p) hM (hm p) (v+2)
    change hsCube (heatArray A h u p σ v) ≤ M*edgeCubic A h u p σ v at h1
    change hsCube (heatArray A h u p σ (v+2)) ≤ M*edgeCubic A h u p σ (v+2) at h2
    exact he.trans (by nlinarith [Real.sqrt_nonneg (2:ℝ)])
  have hi v : planeIntegral (fun p => heatEnergy A h u p σ v) d ≤
      Real.sqrt 2*M*((∑ i, ∑ j, h^2*‖A v i j‖^3)+(∑ i, ∑ j, h^2*‖A (v+2) i j‖^3)) := by
    have ht := integral_mono ((heatPlane_integrable A hh u d hσ).energy 2 v)
      (((edgeCubic_integrable A h u d σ hσ v 2).add
        (edgeCubic_integrable A h u d σ hσ (v+2) 2)).const_mul (Real.sqrt 2*M))
      (fun z => hb (chart 2 d z) v)
    simp only [Pi.add_apply] at ht
    rw [integral_const_mul,integral_add (edgeCubic_integrable A h u d σ hσ v 2)
      (edgeCubic_integrable A h u d σ hσ (v+2) 2)] at ht
    change planeIntegral (fun p => heatEnergy A h u p σ v) d ≤
      Real.sqrt 2*M*(planeIntegral (fun p => edgeCubic A h u p σ v) d+
        planeIntegral (fun p => edgeCubic A h u p σ (v+2)) d) at ht
    simpa only [planeIntegral_edgeCubic A h u d σ hσ] using ht
  have ht := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset Three)) => hi v)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,
    sum_three_shift (fun v => ∑ i, ∑ j, h^2*‖A v i j‖^3)] at ht
  exact ht.trans_eq (by unfold arrayCubic; ring)

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sum_energy_replaceZero_jump (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |(∑ v, energy (starGram (weightedArray (replaceZero A B) g) v))-
      (∑ v, energy (starGram (weightedArray (replaceZero A C) g) v))| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*jumpSlicing A g i j := by
  have h0 := energy_replaceZero_jump_zero A B C hB hC g hg
  have h1 := energy_replaceZero_jump_one A B C hB hC g hg
  have h2 : energy (starGram (weightedArray (replaceZero A B) g) 2) =
      energy (starGram (weightedArray (replaceZero A C) g) 2) := by
    simp only [starGram,rowStar_replaceZero_two A B C g]
  rw [Fin.sum_univ_three,Fin.sum_univ_three,h2]
  have he : ∀ a b c d e : ℝ, a+b+c-(d+e+c) = (a-d)+(b-e) := by intros; ring
  rw [he]
  apply (abs_add_le _ _).trans ((add_le_add h0 h1).trans_eq _)
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold jumpSlicing
  ring
end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def jumpExpectation (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (σ : Three → ℝ) (i j : ι) : ℝ :=
  2*(∑ m, ‖A 0 i m‖^2*(h*density (2*σ 1) (u j-u m)))+
  2*(∑ m, ‖A 0 m j‖^2*(h*density (2*σ 0) (u i-u m)))+
  (∑ m, ‖A 2 m i‖^2*(h*density (σ 0+σ 1+σ 2) (u i+u j+u m)))+
  (∑ m, ‖A 1 j m‖^2*(h*density (σ 0+σ 1+σ 2) (u i+u j+u m)))

omit [DecidableEq ι] in
lemma heat_jumpSlice_integrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) (i j : ι) :
    Integrable (fun z : ℝ×ℝ => heatWeights h u (chart 2 0 z) σ 0 i*
      heatWeights h u (chart 2 0 z) σ 1 j*jumpSlicing A (heatWeights h u (chart 2 0 z) σ) i j) := by
  have hX := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ 1
  have hY := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ 0
  have hH := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 2 m i‖^2) σ hσ 2
  have hK := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 1 j m‖^2) σ hσ 2
  have hi : Integrable (fun z : ℝ×ℝ =>
    2*(weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 0 i m‖^2*weight h (u m) (chart 2 0 z 1) (σ 1))+
    2*(weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 0 m j‖^2*weight h (u m) (chart 2 0 z 0) (σ 0))+
    (weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 2 m i‖^2*weight h (u m) (chart 2 0 z 2) (σ 2))+
    (weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 1 j m‖^2*weight h (u m) (chart 2 0 z 2) (σ 2))) :=
    (((hX.const_mul 2).add (hY.const_mul 2)).add hH).add hK
  convert hi using 1
  ext z
  simp only [heatWeights,jumpSlicing]
  ring

omit [DecidableEq ι] in
lemma planeIntegral_heat_jumpSlice (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) (i j : ι) :
    planeIntegral (fun p => heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*
      jumpSlicing A (heatWeights h u p σ) i j) 0 = h^2*jumpExpectation A h u σ i j := by
  have hX := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ 1
  have hY := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ 0
  have hH := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 2 m i‖^2) σ hσ 2
  have hK := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 1 j m‖^2) σ hσ 2
  have he (p : Three → ℝ) : heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*
      jumpSlicing A (heatWeights h u p σ) i j =
    2*(weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 0 i m‖^2*weight h (u m) (p 1) (σ 1))+
    2*(weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 0 m j‖^2*weight h (u m) (p 0) (σ 0))+
    (weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 2 m i‖^2*weight h (u m) (p 2) (σ 2))+
    (weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 1 j m‖^2*weight h (u m) (p 2) (σ 2)) := by
    unfold heatWeights jumpSlicing; ring
  simp_rw [he]
  unfold planeIntegral
  erw [integral_add (((hX.const_mul 2).add (hY.const_mul 2)).add hH) hK,
    integral_add ((hX.const_mul 2).add (hY.const_mul 2)) hH,
    integral_add (hX.const_mul 2) (hY.const_mul 2),integral_const_mul,integral_const_mul]
  have hXI := weight_slice_one_integral hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ
  have hYI := weight_slice_zero_integral hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ
  have hHI := weight_slice_two_integral hh (u i) (u j) u (fun m => ‖A 2 m i‖^2) σ hσ
  have hKI := weight_slice_two_integral hh (u i) (u j) u (fun m => ‖A 1 j m‖^2) σ hσ
  unfold planeIntegral at hXI hYI hHI hKI
  erw [hXI,hYI,hHI,hKI]
  unfold jumpExpectation
  ring

lemma totalPlaneEnergy_replaceZero_jump (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) :
    |totalPlaneEnergy (replaceZero A B) h u 0 σ-totalPlaneEnergy (replaceZero A C) h u 0 σ| ≤
      3/2*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpExpectation A h u σ i j := by
  have hE (M : Three → Matrix ι ι ℂ) : Integrable (fun z : ℝ×ℝ => ∑ v, heatEnergy M h u (chart 2 0 z) σ v) :=
    integrable_finsetSum _ (fun v _ => (heatPlane_integrable M hh u 0 hσ).energy 2 v)
  have hj (i j : ι) : Integrable (fun z : ℝ×ℝ => ‖B i j-C i j‖*(heatWeights h u (chart 2 0 z) σ 0 i*
      heatWeights h u (chart 2 0 z) σ 1 j*jumpSlicing A (heatWeights h u (chart 2 0 z) σ) i j)) :=
    (heat_jumpSlice_integrable A hh u hσ i j).const_mul _
  have hJ := integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hj i j))
  have hb := (abs_integral_le_integral_abs (f := fun z : ℝ×ℝ => (∑ v, heatEnergy (replaceZero A B) h u (chart 2 0 z) σ v)-
      (∑ v, heatEnergy (replaceZero A C) h u (chart 2 0 z) σ v))).trans
    (integral_mono ((hE _).sub (hE _)).abs (hJ.const_mul (3/2)) (fun z => by
      simpa only [heatEnergy,heatArray,mul_assoc] using
        sum_energy_replaceZero_jump A B C hB hC (heatWeights h u (chart 2 0 z) σ)
          (fun v i => (weight_pos hh (hσ v) _ _).le)))
  rw [integral_sub (hE _) (hE _),integral_finsetSum _ (fun v _ => (heatPlane_integrable (replaceZero A B) hh u 0 hσ).energy 2 v),
    integral_finsetSum _ (fun v _ => (heatPlane_integrable (replaceZero A C) hh u 0 hσ).energy 2 v)] at hb
  change |totalPlaneEnergy (replaceZero A B) h u 0 σ-totalPlaneEnergy (replaceZero A C) h u 0 σ| ≤ _ at hb
  apply hb.trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hj i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hj _ j),integral_const_mul]
  change 3/2*(∑ i, ∑ j, ‖B i j-C i j‖*planeIntegral (fun p =>
    heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*jumpSlicing A (heatWeights h u p σ) i j) 0) = _
  simp_rw [planeIntegral_heat_jumpSlice A hh u hσ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open scoped BigOperators

lemma finite_disjoint_selection {κ : Type uκ} {X : Type uX} (s : Finset κ) (B : κ → Set X)
  (δ : κ → ℝ) (hne : ∀ a ∈ s, (B a).Nonempty) :
  ∃ u : Finset κ, u ⊆ s ∧
    (∀ a ∈ u, ∀ b ∈ u, a ≠ b → Disjoint (B a) (B b)) ∧
    ∀ a ∈ s, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ δ a ≤ δ b := by
  classical
  revert hne
  refine Finset.strongInductionOn s (fun s ih hne => ?_)
  by_cases hs : s.Nonempty
  · obtain ⟨b,hb,hmax⟩ := s.exists_max_image δ hs
    let t := s.filter (fun a => Disjoint (B a) (B b))
    have hts : t ⊆ s := Finset.filter_subset _ _
    have hbt : b ∉ t := by
      simp only [t,Finset.mem_filter,not_and]
      intro _ hd
      obtain ⟨x,hx⟩ := hne b hb
      exact Set.disjoint_left.mp hd hx hx
    have htss : t ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hts,by
      intro he; exact hbt (he.symm ▸ hb)⟩
    obtain ⟨u,hu,hdis,hcover⟩ := ih t htss (fun a ha => hne a (hts ha))
    refine ⟨insert b u,Finset.insert_subset hb (hu.trans hts),?_,?_⟩
    · intro a ha c hc hac
      rcases Finset.mem_insert.mp ha with hab | hau
      · subst a
        rcases Finset.mem_insert.mp hc with hcb | hcu
        · exact (hac hcb.symm).elim
        · exact (Finset.mem_filter.mp (hu hcu)).2.symm
      · rcases Finset.mem_insert.mp hc with hcb | hcu
        · subst c
          exact (Finset.mem_filter.mp (hu hau)).2
        · exact hdis a hau c hcu hac
    · intro a ha
      by_cases hab : Disjoint (B a) (B b)
      · obtain ⟨c,hc,hac,hδ⟩ := hcover a (Finset.mem_filter.mpr ⟨ha,hab⟩)
        exact ⟨c,Finset.mem_insert_of_mem hc,hac,hδ⟩
      · exact ⟨b,Finset.mem_insert_self _ _,Set.not_disjoint_iff_nonempty_inter.mp hab,hmax a ha⟩
  · refine ⟨∅,Finset.empty_subset _,by simp,?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def intInterval (n : ℤ) (r : ℕ) : Finset ℤ := Finset.Icc (n-r) (n+r)

lemma mem_intInterval (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ n-(r:ℤ) ≤ m ∧ m ≤ n+r := Finset.mem_Icc

lemma center_mem_intInterval (n : ℤ) (r : ℕ) : n ∈ intInterval n r := by
  rw [mem_intInterval]; constructor <;> omega

lemma card_intInterval (n : ℤ) (r : ℕ) : (intInterval n r).card = 2*r+1 := by
  rw [intInterval,Int.card_Icc]
  have he : n+(r:ℤ)+1-(n-r) = ((2*r+1 : ℕ):ℤ) := by push_cast; ring
  rw [he,Int.toNat_natCast]

lemma interval_inter_center {a b : ℤ} {r s : ℕ}
    (hab : ((intInterval a r : Set ℤ) ∩ (intInterval b s : Set ℤ)).Nonempty)
    (hrs : r ≤ s) : a ∈ intInterval b (3*s) := by
  obtain ⟨m,hm,hm'⟩ := hab
  have hm1 := (mem_intInterval m a r).mp hm
  have hm2 := (mem_intInterval m b s).mp hm'
  rw [mem_intInterval]
  constructor <;> push_cast <;> omega

lemma int_intervals_weak (D s : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (r : ℤ → ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hav : ∀ n ∈ s, ρ * (2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    ρ * (s.card:ℝ) ≤ 3 * ∑ m ∈ D, f m := by
  classical
  obtain ⟨u,hu,hd,hcov⟩ := finite_disjoint_selection s
    (fun n => (intInterval n (r n) : Set ℤ)) (fun n => (r n : ℝ))
    (fun n _ => ⟨n,center_mem_intInterval n (r n)⟩)
  have hcover : s ⊆ u.biUnion (fun n => intInterval n (3*r n)) := by
    intro a ha
    obtain ⟨b,hb,hab,hrs⟩ := hcov a ha
    exact Finset.mem_biUnion.mpr ⟨b,hb,interval_inter_center hab (by exact_mod_cast hrs)⟩
  have hc : (s.card:ℝ) ≤ 3*∑ n ∈ u, (2*(r n:ℝ)+1) := by
    have h1 := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le : (u.biUnion (fun n => intInterval n (3*r n))).card ≤ _)
    have h2 : (∑ n ∈ u, (intInterval n (3*r n)).card) ≤ ∑ n ∈ u, 3*(2*r n+1) := by
      apply Finset.sum_le_sum
      intro n _
      rw [card_intInterval]
      omega
    have h3 : (s.card:ℝ) ≤ (∑ n ∈ u, 3*(2*r n+1):ℕ) := by exact_mod_cast h1.trans h2
    simpa only [Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Finset.mul_sum] using h3
  have hdis : (↑u : Set ℤ).PairwiseDisjoint (fun n => D ∩ intInterval n (r n)) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro m hm hm'
    exact Set.disjoint_left.mp (hd a ha b hb hab) (Finset.mem_inter.mp hm).2 (Finset.mem_inter.mp hm').2
  have hsubset : u.biUnion (fun n => D ∩ intInterval n (r n)) ⊆ D := by
    intro m hm
    obtain ⟨n,_,hn⟩ := Finset.mem_biUnion.mp hm
    exact (Finset.mem_inter.mp hn).1
  have hsum : (∑ n ∈ u, ∑ m ∈ D ∩ intInterval n (r n), f m) ≤ ∑ m ∈ D, f m := by
    rw [← Finset.sum_biUnion hdis]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m hm _ => hf m hm)
  calc
    _ ≤ ρ*(3*∑ n ∈ u, (2*(r n:ℝ)+1)) := mul_le_mul_of_nonneg_left hc hρ
    _ = 3*∑ n ∈ u, ρ*(2*(r n:ℝ)+1) := by rw [← Finset.mul_sum]; ring
    _ ≤ 3*∑ n ∈ u, ∑ m ∈ D ∩ intInterval n (r n), f m :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n hn => hav n (hu hn))) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def squareLayer (a t : ℝ) : ℝ := (Set.Ioo 0 (Real.sqrt a)).indicator (fun t => t^2) t

def oneLayer (a t : ℝ) : ℝ := (Set.Ioo 0 (Real.sqrt a)).indicator (fun _ => (1:ℝ)) t

lemma squareLayer_integrable (a : ℝ) : Integrable (squareLayer a) := by
  have h : IntegrableOn (fun t : ℝ => t^2) (Set.Icc 0 (Real.sqrt a)) volume :=
    (continuous_id.pow 2).integrableOn_Icc
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (h.mono_set Set.Ioo_subset_Icc_self)

lemma oneLayer_integrable (a : ℝ) : Integrable (oneLayer a) := by
  have h : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioo 0 (Real.sqrt a)) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  exact (integrable_indicator_iff measurableSet_Ioo).mpr h

lemma integral_squareLayer {a : ℝ} (ha : 0 ≤ a) :
    (∫ t, squareLayer a t) = a * Real.sqrt a / 3 := by
  simp only [squareLayer]
  rw [integral_indicator measurableSet_Ioo]
  rw [← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (Real.sqrt_nonneg a)]
  rw [integral_pow]
  have he : (Real.sqrt a)^3 = a*Real.sqrt a := by
    rw [pow_succ,Real.sq_sqrt ha]
  norm_num [he]

lemma integral_oneLayer (a : ℝ) : (∫ t, oneLayer a t) = Real.sqrt a := by
  simp only [oneLayer]
  rw [integral_indicator measurableSet_Ioo,← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (Real.sqrt_nonneg a),intervalIntegral.integral_const]
  simp

lemma layer_iff {a t : ℝ} (ht : 0 < t) :
    t ∈ Set.Ioo 0 (Real.sqrt a) ↔ t^2 < a := by
  exact and_iff_right ht |>.trans (Real.lt_sqrt (by positivity))

end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma truncated_average_lower (D : Finset ℤ) (f : ℤ → ℝ) (r : ℤ → ℕ) (n : ℤ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hav : ρ*(2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    (ρ/2)*(2*(r n:ℝ)+1) ≤
      ∑ m ∈ D ∩ intInterval n (r n), if ρ < 2*f m then f m else 0 := by
  classical
  have he (m : ℤ) : f m ≤ (if ρ < 2*f m then f m else 0) + ρ/2 := by
    split_ifs <;> linarith
  have hsum := Finset.sum_le_sum (fun m (_ : m ∈ D ∩ intInterval n (r n)) => he m)
  have hc : ((D ∩ intInterval n (r n)).card:ℝ) ≤ 2*(r n:ℝ)+1 := by
    have ht := Finset.card_le_card (Finset.inter_subset_right : D ∩ intInterval n (r n) ⊆ intInterval n (r n))
    rw [card_intInterval] at ht
    exact_mod_cast ht
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
  have hp := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ ρ/2)
  linarith

lemma int_intervals_strong (D s : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ m ∈ D, 0 ≤ f m) (hg : ∀ n ∈ s, 0 ≤ g n) (r : ℤ → ℕ)
    (hav : ∀ n ∈ s, g n*(2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    (∑ n ∈ s, g n*Real.sqrt (g n)) ≤
      18*Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
  classical
  have layer_bound (t : ℝ) : (∑ n ∈ s, 3*squareLayer (g n) t) ≤
      18 * ∑ m ∈ D, f m * oneLayer (2*f m) t := by
    by_cases ht : 0 < t
    · let u := s.filter (fun n => t^2 < g n)
      let f' := fun m => if t^2 < 2*f m then f m else 0
      have hw := int_intervals_weak D u f'
        (fun m hm => by unfold f'; split_ifs; exact hf m hm; exact le_rfl) r (by positivity : 0 ≤ t^2/2)
        (fun n hn => truncated_average_lower D f r n (sq_nonneg t)
          ((mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hn).2.le (by positivity)).trans
            (hav n (Finset.mem_filter.mp hn).1)))
      have hl : (∑ n ∈ s, 3*squareLayer (g n) t) = 3*t^2*(u.card:ℝ) := by
        simp only [squareLayer,Set.indicator_apply,layer_iff ht,mul_ite,mul_zero]
        rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const]
        simp only [u,nsmul_eq_mul]
        ring
      have hr : (∑ m ∈ D, f m*oneLayer (2*f m) t) = ∑ m ∈ D, f' m := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [oneLayer,Set.indicator_apply,layer_iff ht,f']
        split_ifs <;> simp
      rw [hl,hr]
      linarith
    · have he (a : ℝ) : squareLayer a t = 0 ∧ oneLayer a t = 0 := by
        simp [squareLayer,oneLayer,Set.indicator_of_notMem,ht]
      simp only [(he _).1,(he _).2,mul_zero,Finset.sum_const_zero,le_refl]
  have hL : Integrable (fun t => ∑ n ∈ s, 3*squareLayer (g n) t) :=
    integrable_finsetSum _ (fun n _ => (squareLayer_integrable (g n)).const_mul 3)
  have hR : Integrable (fun t => 18*∑ m ∈ D, f m*oneLayer (2*f m) t) :=
    (integrable_finsetSum _ (fun m _ => (oneLayer_integrable (2*f m)).const_mul (f m))).const_mul 18
  have hi := integral_mono hL hR layer_bound
  rw [integral_finsetSum _ (fun n _ => (squareLayer_integrable (g n)).const_mul 3),
    integral_const_mul,integral_finsetSum _ (fun m _ => (oneLayer_integrable (2*f m)).const_mul (f m))] at hi
  have hl : (∑ n ∈ s, ∫ t, 3*squareLayer (g n) t) = ∑ n ∈ s, g n*Real.sqrt (g n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul,integral_squareLayer (hg n hn)]
    ring
  have hr : (∑ m ∈ D, ∫ t, f m*oneLayer (2*f m) t) =
      Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_const_mul,integral_oneLayer,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hl,hr] at hi
  simpa only [mul_assoc] using hi
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval_iff_dist (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ (m-n).natAbs ≤ r := by
  rw [mem_intInterval]
  have he : (m-n).natAbs ≤ r ↔ |m-n| ≤ (r:ℤ) := by
    rw [← Int.natCast_natAbs]
    omega
  rw [he,abs_le]
  constructor <;> intro h <;> constructor <;> omega

def supportRadius (D : Finset ℤ) (n : ℤ) : ℕ := D.sup (fun m => (m-n).natAbs)

def intAverage (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) (r : ℕ) : ℝ :=
  (∑ m ∈ D ∩ intInterval n r, f m)/(2*(r:ℝ)+1)

lemma intAverage_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) (r : ℕ) :
    0 ≤ intAverage D f n r := by
  exact div_nonneg (Finset.sum_nonneg (fun m hm => hf m (Finset.mem_inter.mp hm).1)) (by positivity)

lemma inter_intInterval_of_supportRadius_le (D : Finset ℤ) (n : ℤ) {r : ℕ}
    (hr : supportRadius D n ≤ r) : D ∩ intInterval n r = D := by
  apply Finset.inter_eq_left.mpr
  intro m hm
  rw [mem_intInterval_iff_dist]
  exact (Finset.le_sup hm).trans hr

def intMax (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) : ℝ :=
  (Finset.range (supportRadius D n+1)).sup' (by exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) (intAverage D f n)

lemma intAverage_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : intAverage D f n r ≤ intMax D f n := by
  by_cases hr : r ≤ supportRadius D n
  · exact Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  · have hb : supportRadius D n ≤ r := le_of_lt (lt_of_not_ge hr)
    have hm : intAverage D f n r ≤ intAverage D f n (supportRadius D n) := by
      unfold intAverage
      rw [inter_intInterval_of_supportRadius_le D n hb,
        inter_intInterval_of_supportRadius_le D n le_rfl]
      apply div_le_div_of_nonneg_left (Finset.sum_nonneg hf) (by positivity)
      exact_mod_cast (by omega : 2*supportRadius D n+1 ≤ 2*r+1)
    exact hm.trans (Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_self _)))

lemma intMax_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) :
    0 ≤ intMax D f n := (intAverage_nonneg D f hf n 0).trans (intAverage_le_intMax D f hf n 0)

lemma intMax_attained (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) :
    ∃ r : ℕ, intMax D f n = intAverage D f n r := by
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (supportRadius D n+1)) (by exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) (intAverage D f n)
  exact ⟨r,hr⟩

lemma sum_interval_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : (∑ m ∈ D ∩ intInterval n r, f m) ≤ intMax D f n*(2*(r:ℝ)+1) := by
  exact (div_le_iff₀ (by positivity : 0 < 2*(r:ℝ)+1)).mp (intAverage_le_intMax D f hf n r)
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open scoped BigOperators

lemma descending_layer_identity (g : ℕ → ℝ) (k N : ℕ) (hk : k ≤ N) :
    g k = g N + ∑ r ∈ Finset.range N, if k ≤ r then g r-g (r+1) else 0 := by
  induction N with
  | zero =>
    have he : k = 0 := by omega
    subst k
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hkN : k ≤ N
    · rw [ite_eq_left hkN]
      linarith [ih hkN]
    · have he : k = N+1 := by omega
      subst k
      have hs : (∑ r ∈ Finset.range N, if N+1 ≤ r then g r-g (r+1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        rw [ite_eq_right (by have := Finset.mem_range.mp hr; omega)]
      rw [hs,ite_eq_right (by omega)]
      ring

lemma weighted_prefix_identity {κ : Type uκ} (s : Finset κ) (d : κ → ℕ) (a : κ → ℝ)
    (g : ℕ → ℝ) (N : ℕ) (hd : ∀ i ∈ s, d i ≤ N) :
    (∑ i ∈ s, a i*g (d i)) = g N*(∑ i ∈ s, a i) +
      ∑ r ∈ Finset.range N, (g r-g (r+1)) * ∑ i ∈ s.filter (fun i => d i ≤ r), a i := by
  classical
  calc
    _ = ∑ i ∈ s, a i*(g N+∑ r ∈ Finset.range N, if d i ≤ r then g r-g (r+1) else 0) :=
      Finset.sum_congr rfl (fun i hi => congrArg (a i*·) (descending_layer_identity g (d i) N (hd i hi)))
    _ = g N*(∑ i ∈ s, a i) + ∑ r ∈ Finset.range N, ∑ i ∈ s, a i*(if d i ≤ r then g r-g (r+1) else 0) := by
      simp_rw [mul_add,Finset.mul_sum]
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      congr 1
      simp_rw [mul_comm (g N)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

lemma weighted_prefix_le {κ : Type uκ} (s : Finset κ) (d : κ → ℕ) (a b : κ → ℝ)
    (g : ℕ → ℝ) (N : ℕ) (hd : ∀ i ∈ s, d i ≤ N) (hg : 0 ≤ g N)
    (hdec : ∀ r < N, g (r+1) ≤ g r)
    (hp : ∀ r ≤ N, (∑ i ∈ s.filter (fun i => d i ≤ r), a i) ≤ ∑ i ∈ s.filter (fun i => d i ≤ r), b i) :
    (∑ i ∈ s, a i*g (d i)) ≤ ∑ i ∈ s, b i*g (d i) := by
  classical
  rw [weighted_prefix_identity s d a g N hd,weighted_prefix_identity s d b g N hd]
  apply add_le_add
  · have he : s.filter (fun i => d i ≤ N) = s := Finset.filter_eq_self.mpr hd
    have ht := hp N le_rfl
    rw [he] at ht
    exact mul_le_mul_of_nonneg_left ht hg
  · exact Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
      (hp r (Finset.mem_range.mp hr).le) (sub_nonneg.mpr (hdec r (Finset.mem_range.mp hr))))
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma intMax_strong (D s : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) :
    (∑ n ∈ s, intMax D f n * Real.sqrt (intMax D f n)) ≤
      18*Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
  choose r hr using intMax_attained D f
  apply int_intervals_strong D s f (intMax D f) hf (fun n _ => intMax_nonneg D f hf n) r
  intro n _
  rw [hr n,intAverage]
  exact le_of_eq (div_mul_cancel₀ _ (by positivity))

lemma intInterval_filter (n : ℤ) (N r : ℕ) (hr : r ≤ N) :
    (intInterval n N).filter (fun m => (m-n).natAbs ≤ r) = intInterval n r := by
  ext m
  simp only [Finset.mem_filter,mem_intInterval_iff_dist]
  exact ⟨And.right,fun h => ⟨h.trans hr,h⟩⟩

lemma intInterval_sum_fin (n : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    (∑ m ∈ intInterval n N, f m) = ∑ i : Fin (2*N+1), f (n-(N:ℤ)+(i:ℕ)) := by
  symm
  apply Finset.sum_bij (fun (i : Fin (2*N+1)) _ => n-(N:ℤ)+(i:ℕ))
  · intro i _
    rw [mem_intInterval]
    have hi := i.isLt
    constructor <;> omega
  · intro i _ j _ he
    apply Fin.ext
    omega
  · intro m hm
    rw [mem_intInterval] at hm
    refine ⟨⟨(m-(n-(N:ℤ))).toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    rfl

lemma intInterval_weighted_le (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) (hdec : ∀ r, g (r+1) ≤ g r) :
    (∑ m ∈ D, f m*g (m-n).natAbs) ≤
      intMax D f n * ∑ m ∈ intInterval n (supportRadius D n), g (m-n).natAbs := by
  classical
  let N := supportRadius D n
  have hD : D ⊆ intInterval n N := by
    intro m hm
    rw [mem_intInterval_iff_dist]
    exact (Finset.le_sup (f := fun k : ℤ => (k-n).natAbs) hm)
  have he : (∑ m ∈ D, f m*g (m-n).natAbs) =
      ∑ m ∈ intInterval n N, (if m ∈ D then f m else 0)*g (m-n).natAbs := by
    simp only [ite_mul,zero_mul,Finset.sum_ite,Finset.sum_const_zero,add_zero]
    congr 1
    ext m
    simp only [Finset.mem_filter]
    exact ⟨fun hm => ⟨hD hm,hm⟩,And.right⟩
  rw [he]
  have hw := weighted_prefix_le (intInterval n N) (fun m => (m-n).natAbs)
    (fun m => if m ∈ D then f m else 0) (fun _ => intMax D f n) g N
    (fun m hm => (mem_intInterval_iff_dist m n N).mp hm) (hg N) (fun r _ => hdec r) ?_
  · simpa only [← Finset.mul_sum] using hw
  · intro r hr
    rw [intInterval_filter n N r hr]
    have he' : (∑ m ∈ intInterval n r, if m ∈ D then f m else 0) = ∑ m ∈ D ∩ intInterval n r, f m := by
      rw [Finset.sum_ite,Finset.sum_const_zero,add_zero]
      congr 1
      ext m
      simp only [Finset.mem_filter,Finset.mem_inter,and_comm]
    rw [he',Finset.sum_const,card_intInterval,nsmul_eq_mul]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,mul_comm] using sum_interval_le_intMax D f hf n r
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open scoped BigOperators
noncomputable section

lemma density_radial_int (σ h : ℝ) (m : ℤ) :
    density σ (h*(m:ℝ)) = density σ (h*(m.natAbs:ℝ)) := by
  have he := congrArg (fun n : ℤ => (n : ℝ)) (Int.natAbs_sq m).symm
  simp only [Int.cast_pow,Int.cast_natCast] at he
  simp only [density,mul_pow,he]

lemma density_radial_descending {σ h : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (r : ℕ) :
    h*density σ (h*(r+1:ℕ)) ≤ h*density σ (h*(r:ℝ)) := by
  apply mul_le_mul_of_nonneg_left _ hh
  unfold density
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hr : (0:ℝ) ≤ r := by positivity
  push_cast
  nlinarith [sq_nonneg h]

lemma intInterval_density_mass {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) (N : ℕ) :
    (∑ m ∈ intInterval n N, h*density σ (h*((m-n).natAbs:ℝ))) ≤ meshMassConstant := by
  simp_rw [← density_radial_int]
  rw [intInterval_sum_fin]
  have he (i : Fin (2*N+1)) : h*density σ (h*((n-(N:ℤ)+(i:ℕ)-n:ℤ):ℝ)) =
      h*density σ (-(h*N)+h*i) := by
    congr 2
    push_cast
    ring
  simp_rw [he]
  exact mesh_mass_le hh hσ (-(h*N)) (2*N+1)

lemma gaussian_sum_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m ∈ D, f m*(h*density σ (h*((m-n:ℤ):ℝ)))) ≤ meshMassConstant * intMax D f n := by
  have hpos : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  simp_rw [density_radial_int]
  have hw := intInterval_weighted_le D f hf n (fun r => h*density σ (h*(r:ℝ)))
    (fun r => mul_nonneg hh.le (density_nonneg hpos.le _)) (density_radial_descending hpos hh.le)
  apply hw.trans
  rw [mul_comm meshMassConstant]
  exact mul_le_mul_of_nonneg_left (intInterval_density_mass hh hσ n (supportRadius D n)) (intMax_nonneg D f hf n)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def lineExtend (D : Finset ℤ) (f : D → ℝ) (n : ℤ) : ℝ :=
  if hn : n ∈ D then f ⟨n,hn⟩ else 0

lemma lineExtend_apply (D : Finset ℤ) (f : D → ℝ) (n : D) : lineExtend D f n = f n := by
  simp only [lineExtend,dite_eq_left n.property]

lemma sum_lineExtend (D : Finset ℤ) (f : D → ℝ) (g : ℤ → ℝ) :
    (∑ n ∈ D, lineExtend D f n*g n) = ∑ n : D, f n*g n := by
  rw [← Finset.sum_coe_sort]
  simp only [lineExtend_apply]

def lineMax (D : Finset ℤ) (f : D → ℝ) (n : ℤ) : ℝ := intMax D (lineExtend D f) n

lemma lineMax_nonneg (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m) (n : ℤ) :
    0 ≤ lineMax D f n := by
  exact intMax_nonneg D (lineExtend D f) (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) n

lemma lineMax_strong (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {κ : Type uκ} [Fintype κ] (u : κ → ℤ) (hu : Function.Injective u) :
    (∑ n, lineMax D f (u n)*Real.sqrt (lineMax D f (u n))) ≤
      18*Real.sqrt 2 * ∑ m : D, f m*Real.sqrt (f m) := by
  classical
  have hi := intMax_strong D (Finset.univ.image u) (lineExtend D f)
    (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩)
  rw [Finset.sum_image (fun _ _ _ _ h => hu h)] at hi
  rw [← Finset.sum_coe_sort D (fun m => lineExtend D f m*Real.sqrt (lineExtend D f m))] at hi
  simpa only [lineMax,lineExtend_apply] using hi

lemma gaussian_sum_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m : D, f m*(h*Heat.density σ (h*((m-n:ℤ):ℝ)))) ≤ Heat.meshMassConstant*lineMax D f n := by
  have hi := Heat.gaussian_sum_le_intMax D (lineExtend D f)
    (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) hh hσ n
  rw [sum_lineExtend] at hi
  exact hi

lemma cubic_young {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*b ≤ (a^3+2*b*Real.sqrt b)/3 := by
  have hs := Real.sq_sqrt hb
  have hnn : 0 ≤ (a-Real.sqrt b)^2*(a+2*Real.sqrt b) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hs3 : (Real.sqrt b)^3 = b*Real.sqrt b := by rw [pow_succ,hs]
  have ha2 : a*(Real.sqrt b)^2 = a*b := by rw [hs]
  nlinarith only [hnn,hs3,ha2]

lemma sum_abs_sq_sqrt {κ : Type uκ} [Fintype κ] (f : κ → ℂ) :
    (∑ m, ‖f m‖^2*Real.sqrt (‖f m‖^2)) = ∑ m, ‖f m‖^3 := by
  apply Finset.sum_congr rfl
  intro m _
  rw [Real.sqrt_sq (norm_nonneg _)]; ring

lemma lineMax_scalar_product_bound (D : Finset ℤ) (f : D → ℂ)
    {κ : Type uκ} [Fintype κ] (u : κ → ℤ) (hu : Function.Injective u) (a : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i*lineMax D (fun m => ‖f m‖^2) (u i)) ≤
      ((∑ i, a i^3)+36*Real.sqrt 2*(∑ m, ‖f m‖^3))/3 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset κ)) =>
    cubic_young (ha i) (lineMax_nonneg D (fun m => ‖f m‖^2) (fun m => sq_nonneg _) (u i)))
  have hm := lineMax_strong D (fun m => ‖f m‖^2) (fun m => sq_nonneg _) u hu
  rw [sum_abs_sq_sqrt] at hm
  simp only [mul_assoc,← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum] at hs
  linarith
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

def jumpMax (D : Finset ℤ) (A : Three → Matrix D D ℂ) (i j : D) : ℝ :=
  2*lineMax D (fun m => ‖A 0 i m‖^2) j+
  2*lineMax D (fun m => ‖A 0 m j‖^2) i+
  lineMax D (fun m => ‖A 2 m i‖^2) (-(i:ℤ)-(j:ℤ))+
  lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ))

lemma jumpMax_nonneg (D : Finset ℤ) (A : Three → Matrix D D ℂ) (i j : D) :
    0 ≤ jumpMax D A i j := by
  unfold jumpMax
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _))
    (mul_nonneg (by norm_num) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)))
    (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)

lemma gaussian_sum_back_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m : D, f m*(h*density σ (h*n-h*(m:ℤ)))) ≤ meshMassConstant*lineMax D f n := by
  have he (m : D) : density σ (h*n-h*(m:ℤ)) = density σ (h*((m-n:ℤ):ℝ)) := by
    rw [show h*n-h*(m:ℤ) = -(h*((m-n:ℤ):ℝ)) by push_cast; ring,density_neg]
  simp_rw [he]
  exact gaussian_sum_le_lineMax D f hf hh hσ n

lemma gaussian_sum_triangle_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (i j : ℤ) :
    (∑ m : D, f m*(h*density σ (h*i+h*j+h*(m:ℤ)))) ≤ meshMassConstant*lineMax D f (-i-j) := by
  have he (m : D) : h*i+h*j+h*(m:ℤ) = h*((m-(-i-j):ℤ):ℝ) := by push_cast; ring
  simp_rw [he]
  exact gaussian_sum_le_lineMax D f hf hh hσ (-i-j)

lemma jumpExpectation_le_jumpMax (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    {h : ℝ} (hh : 0 < h) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) (i j : D) :
    jumpExpectation A h (fun m => h*(m:ℤ)) σ i j ≤ meshMassConstant*jumpMax D A i j := by
  have htwo (v : Three) : h^2 ≤ 2*σ v := by nlinarith [hσ v,sq_nonneg h]
  have hsum : h^2 ≤ σ 0+σ 1+σ 2 := by nlinarith [hσ 0,hσ 1,hσ 2,sq_nonneg h]
  have hX := gaussian_sum_back_le_lineMax D (fun m => ‖A 0 i m‖^2) (fun _ => sq_nonneg _) hh (htwo 1) j
  have hY := gaussian_sum_back_le_lineMax D (fun m => ‖A 0 m j‖^2) (fun _ => sq_nonneg _) hh (htwo 0) i
  have hH := gaussian_sum_triangle_le_lineMax D (fun m => ‖A 2 m i‖^2) (fun _ => sq_nonneg _) hh hsum i j
  have hK := gaussian_sum_triangle_le_lineMax D (fun m => ‖A 1 j m‖^2) (fun _ => sq_nonneg _) hh hsum i j
  unfold jumpExpectation jumpMax
  linarith

lemma finite_mesh_energy_jump_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (B C : Matrix D D ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) :
    |totalPlaneEnergy (replaceZero A B) h (fun m => h*(m:ℤ)) 0 σ-
      totalPlaneEnergy (replaceZero A C) h (fun m => h*(m:ℤ)) 0 σ| ≤
      3/2*meshMassConstant*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpMax D A i j := by
  have hj := totalPlaneEnergy_replaceZero_jump A B C hB hC hh (fun m => h*(m:ℤ))
    (fun v => (sq_pos_of_pos hh).trans_le (hσ v))
  apply hj.trans
  calc
    _ ≤ 3/2*h^2*∑ i, ∑ j, ‖B i j-C i j‖*(meshMassConstant*jumpMax D A i j) := by
      gcongr with i j
      exact jumpExpectation_le_jumpMax D A hh hσ i j
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma sum_lineMax_scalar_product_bound (D : Finset ℤ) (f g : D → D → ℂ) (u : D → D → ℤ)
    (hu : ∀ i, Function.Injective (u i)) :
    (∑ i, ∑ j, ‖g i j‖*lineMax D (fun m => ‖f i m‖^2) (u i j)) ≤
      ((∑ i, ∑ j, ‖g i j‖^3)+36*Real.sqrt 2*(∑ i, ∑ m, ‖f i m‖^3))/3 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset D)) =>
    lineMax_scalar_product_bound D (f i) (u i) (hu i) (fun j => ‖g i j‖) (fun j => norm_nonneg _))
  simpa only [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum] using hs

def jumpScalarConstant : ℝ := 2+48*Real.sqrt 2

lemma jumpScalarConstant_pos : 0 < jumpScalarConstant := by unfold jumpScalarConstant; positivity

lemma sum_jumpMax_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) :
    (∑ i, ∑ j, ‖A 0 i j‖*jumpMax D A i j) ≤
      jumpScalarConstant * (∑ v, ∑ i, ∑ j, ‖A v i j‖^3) := by
  have hu : Function.Injective (fun i : D => (i:ℤ)) := Subtype.val_injective
  have hn (i : D) : Function.Injective (fun j : D => -(i:ℤ)-(j:ℤ)) := by
    intro j k hjk
    apply Subtype.ext
    dsimp at hjk
    omega
  have hX := sum_lineMax_scalar_product_bound D (fun i m => A 0 i m) (fun i j => A 0 i j)
    (fun _ j => (j:ℤ)) (fun _ => hu)
  have hY := sum_lineMax_scalar_product_bound D (fun j m => A 0 m j) (fun j i => A 0 i j)
    (fun _ i => (i:ℤ)) (fun _ => hu)
  have hH := sum_lineMax_scalar_product_bound D (fun i m => A 2 m i) (fun i j => A 0 i j)
    (fun i j => -(i:ℤ)-(j:ℤ)) hn
  have hK := sum_lineMax_scalar_product_bound D (fun j m => A 1 j m) (fun j i => A 0 i j)
    (fun j i => -(j:ℤ)-(i:ℤ)) hn
  have hc (v : Three) : (∑ j : D, ∑ i : D, ‖A v i j‖^3) = ∑ i : D, ∑ j : D, ‖A v i j‖^3 := by rw [Finset.sum_comm]
  rw [hc] at hY hH hK
  have hYe : (∑ j : D, ∑ i : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) (i:ℤ)) =
      ∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) (i:ℤ) := by rw [Finset.sum_comm]
  rw [hYe] at hY
  have hKe : (∑ j : D, ∑ i : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(j:ℤ)-(i:ℤ))) =
      ∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  rw [hKe] at hK
  have hb (v : Three) : 0 ≤ ∑ i : D, ∑ j : D, ‖A v i j‖^3 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) _))
  have he : (∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j) =
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 i m‖^2) j)+
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) i)+
      (∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 2 m i‖^2) (-(i:ℤ)-(j:ℤ)))+
      (∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ))) := by
    simp only [jumpMax,mul_add,Finset.sum_add_distrib,Finset.mul_sum,
      mul_left_comm]
  rw [he,Fin.sum_univ_three]
  unfold jumpScalarConstant
  nlinarith [hb 0,hb 1,hb 2,Real.sqrt_nonneg (2:ℝ)]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma finite_mesh_mass_le (D : Finset ℤ) {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (p : ℝ) :
    (∑ i : D, weight h (h*(i:ℤ)) p σ) ≤ meshMassConstant := by
  let N := supportRadius D 0
  have hD : D ⊆ intInterval 0 N := by
    intro m hm
    rw [mem_intInterval_iff_dist]
    exact Finset.le_sup (f := fun k : ℤ => (k-0).natAbs) hm
  rw [Finset.sum_coe_sort D (fun i : ℤ => weight h (h*(i:ℝ)) p σ)]
  have hi : (∑ i ∈ D, weight h (h*(i:ℝ)) p σ) ≤ ∑ i ∈ intInterval 0 N, weight h (h*(i:ℝ)) p σ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hD
    intro i _ _
    exact (weight_pos hh ((sq_pos_of_pos hh).trans_le hσ) _ _).le
  apply hi.trans
  rw [intInterval_sum_fin]
  have he (i : Fin (2*N+1)) : weight h (h*((0-(N:ℤ)+(i:ℕ):ℤ):ℝ)) p σ =
      h*density σ ((-(h*N)-p)+h*i) := by
    unfold weight
    congr 2
    push_cast
    ring
  simp_rw [he]
  exact mesh_mass_le hh hσ (-(h*N)-p) (2*N+1)

lemma finite_mesh_totalPlaneEnergy_le (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    {h : ℝ} (hh : 0 < h) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) :
    totalPlaneEnergy A h (fun i => h*(i:ℤ)) d σ ≤
      2*Real.sqrt 2*meshMassConstant*arrayCubic A h := by
  exact totalPlaneEnergy_le_mass A hh _ d (fun v => (sq_pos_of_pos hh).trans_le (hσ v)) meshMassConstant_pos.le
    (fun p v => finite_mesh_mass_le D hh (hσ v) (p v))
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma continuous_heatCarrier_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => heatCarrier A h u (p t) (σ t) v w) := by
  unfold heatCarrier
  split_ifs
  · exact continuous_heatRow_param A h u hp hσ hpos v
  · exact (continuous_heatRow_param A h u hp hσ hpos v).star

omit [Fintype ι] in
lemma continuous_scoreMask_param {E : Type uE} [TopologicalSpace E] (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (w : Three) :
    Continuous (fun t => heatMask (fun a j => if a = w then score (u j) (p t a) (σ t a) else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score
    exact (continuous_const.sub ((continuous_apply a).comp hp)).div
      ((continuous_apply a).comp hσ) (fun t => (hpos t a).ne')
  · exact continuous_const

omit [Fintype ι] in
lemma continuous_secondMask_param {E : Type uE} [TopologicalSpace E] (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (w : Three) :
    Continuous (fun t => heatMask (fun a j => if a = w then score (u j) (p t a) (σ t a)^2-(σ t a)⁻¹ else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score
    exact (((continuous_const.sub ((continuous_apply a).comp hp)).div
      ((continuous_apply a).comp hσ) (fun t => (hpos t a).ne')).pow 2).sub
      (((continuous_apply a).comp hσ).inv₀ (fun t => (hpos t a).ne'))
  · exact continuous_const

lemma continuous_heatFirst_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => heatFirst A h u (p t) (σ t) v w) := by
  simp only [heatFirst,localGram_eq_carrier A hh u _ (hpos _),localFirst_eq_carrier A hh u _ (hpos _)]
  exact continuous_energyGradient_insert (continuous_heatCarrier_param A h u hp hσ hpos v w)
    (continuous_scoreMask_param u hp hσ hpos w)

lemma continuous_heatSecondGradient_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => energyGradient (localGram A h u (p t) (σ t) v w) (localSecond A h u (p t) (σ t) v w)) := by
  simp only [localGram_eq_carrier A hh u _ (hpos _),localSecond_eq_carrier A hh u _ (hpos _)]
  exact continuous_energyGradient_insert (continuous_heatCarrier_param A h u hp hσ hpos v w)
    (continuous_secondMask_param u hp hσ hpos w)

lemma continuous_heatVariance_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => heatVariance A h u (p t) (σ t) v w) :=
  continuous_const.mul (continuous_heatSecondGradient_param A hh u hp hσ hpos v w)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma measurable_heatPure_param {E : Type uE} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Measurable (fun t => heatPure A h u (p t) (σ t) v w) := by
  have hc : Continuous (fun q : E × ℝ => heatFirst A h u (Function.update (p q.1) w q.2) (σ q.1) v w) :=
    continuous_heatFirst_param A hh u (by fun_prop) (hσ.comp continuous_fst) (fun q a => hpos q.1 a) v w
  have hm := (measurable_deriv_with_param
    (f := fun t q => heatFirst A h u (Function.update (p t) w q) (σ t) v w) hc).comp
    (show Measurable (fun t : E => (t,p t w)) from measurable_id.prodMk (((continuous_apply w).comp hp).measurable))
  convert! hm using 1
  funext t
  exact (heatFirst_hasDerivAt_center A hh u (p t) (hpos t) v w).deriv.symm

lemma measurable_heatCost_param {E : Type uE} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Measurable (fun t => heatCost A h u (p t) (σ t) v w) := by
  have hm := (measurable_heatPure_param A hh u hp hσ hpos v w).sub
    (continuous_heatSecondGradient_param A hh u hp hσ hpos v w).measurable
  convert! hm using 1
  funext t
  simp [heatPure,heatCost]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section

lemma intervalIntegrable_of_clamped {f g : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hg : StronglyMeasurable g) (hbound : ∀ t, ‖g t‖ ≤ C)
    (he : ∀ t ∈ Set.Icc a b, f t = g t) : IntervalIntegrable f volume a b := by
  have hi : IntervalIntegrable g volume a b :=
    intervalIntegrable_const.mono_fun' hg.aestronglyMeasurable (Eventually.of_forall hbound)
  apply hi.congr
  rw [Set.uIoc_of_le hab]
  exact fun t ht => (he t ⟨ht.1.le,ht.2⟩).symm

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma planeTime_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∀ v w, IntervalIntegrable (fun t => planeIntegral (fun p => heatVariance A h u p (fun z => α z*t) v w) d) volume a b) ∧
    (∀ v w, IntervalIntegrable (fun t => planeIntegral (fun p => heatCost A h u p (fun z => α z*t) v w) d) volume a b) := by
  let T : ℝ → ℝ := fun t => max a (min b t)
  have hT : Continuous T := by unfold T; fun_prop
  have hTl (t : ℝ) : a ≤ T t := le_max_left _ _
  have hTu (t : ℝ) : T t ≤ b := max_le hab (min_le_left _ _)
  have hTe (t : ℝ) (ht : t ∈ Set.Icc a b) : T t = t := by
    simp [T,min_eq_right ht.2,max_eq_right ht.1]
  let σ : ℝ → Three → ℝ := fun t w => α w*T t
  have hσ : Continuous σ := by apply continuous_pi; intro w; exact continuous_const.mul hT
  have hpos (t : ℝ) (w : Three) : 0 < σ t w := mul_pos (hα w) (ha.trans_le (hTl t))
  obtain ⟨l,r,hl,hlr,hlo,hhi⟩ := finite_variance_bounds α hα
  obtain ⟨B,hB,_,hbound⟩ := exists_heat_uniform_majorant A hh (mul_pos hl ha)
    (show l*a ≤ r*b from mul_le_mul hlr hab ha.le (hl.trans_le hlr).le) (abs_nonneg d) u
  have hb t z : HeatAtBounds A h u (chart 2 d z) (σ t) (B z) :=
    hbound 2 d z le_rfl (σ t)
      (fun w => mul_le_mul (hlo w) (hTl t) ha.le (hα w).le)
      (fun w => mul_le_mul (hhi w) (hTu t) (ha.trans_le (hTl t)).le (hl.trans_le hlr).le)
  have hp : Continuous (fun q : ℝ × (ℝ×ℝ) => chart 2 d q.2) :=
    (chart_continuous 2).comp (continuous_const.prodMk continuous_snd)
  have hσq : Continuous (fun q : ℝ × (ℝ×ℝ) => σ q.1) := hσ.comp continuous_fst
  have hclamp (f : ℝ → (Three → ℝ) → ℝ)
      (hm : Measurable (fun q : ℝ × (ℝ×ℝ) => f q.1 (chart 2 d q.2)))
      (hbo : ∀ t z, ‖f t (chart 2 d z)‖ ≤ B z) :
      StronglyMeasurable (fun t => planeIntegral (f t) d) ∧
      ∀ t, ‖planeIntegral (f t) d‖ ≤ ∫ z, B z :=
    ⟨hm.stronglyMeasurable.integral_prod_right,fun t => norm_integral_le_of_norm_le hB (Eventually.of_forall (hbo t))⟩
  constructor
  · intro v w
    have hc := hclamp (fun t p => heatVariance A h u p (σ t) v w)
      (continuous_heatVariance_param A hh u hp hσq (fun q z => hpos q.1 z) v w).measurable
      (fun t z => (hb t z).variance v w)
    apply intervalIntegrable_of_clamped hab hc.1 hc.2
    intro t ht
    simp only [σ,hTe t ht]
  · intro v w
    have hc := hclamp (fun t p => heatCost A h u p (σ t) v w)
      (measurable_heatCost_param A hh u hp hσq (fun q z => hpos q.1 z) v w)
      (fun t z => (hb t z).cost v w)
    apply intervalIntegrable_of_clamped hab hc.1 hc.2
    intro t ht
    simp only [σ,hTe t ht]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma totalPlaneTime_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (totalPlaneTime A h u d α) volume a b := by
  have hi : IntervalIntegrable (∑ v : Three, ∑ w : Three,
      fun s => α w * planeIntegral (fun p => heatVariance A h u p (fun z => α z*s) v w) d) volume a b := by
    apply IntervalIntegrable.sum Finset.univ
    intro v _
    apply IntervalIntegrable.sum Finset.univ
    intro w _
    exact ((planeTime_intervalIntegrable A hh u d α hα ha hab).1 v w).const_mul (α w)
  convert hi using 1
  ext s
  simp [totalPlaneTime]

lemma integral_totalPlaneTime (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, totalPlaneTime A h u d α s) =
      totalPlaneEnergy A h u d (fun w => α w*b) - totalPlaneEnergy A h u d (fun w => α w*a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (totalPlaneTime_intervalIntegrable A hh u d α hα ha hab)
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  exact totalPlaneEnergy_hasDerivAt A hh u d α hα (ha.trans_le hs.1)

lemma integrated_strict_dissipation (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (i : Three)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    strictConstant * (∫ s in a..b, ∑ w, planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) ≤
      totalPlaneEnergy A h u d (fun w => strictRate i w*a) - totalPlaneEnergy A h u d (fun w => strictRate i w*b) := by
  have hc : IntervalIntegrable (fun s => ∑ w, planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) volume a b :=
    by
      have hi : IntervalIntegrable (∑ w : Three, fun s => planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) volume a b := IntervalIntegrable.sum Finset.univ (fun w _ => (planeTime_intervalIntegrable A hh u d (strictRate i) (strictRate_pos i) ha hab).2 w w)
      convert hi using 1
      ext s
      simp
  have ht := totalPlaneTime_intervalIntegrable A hh u d (strictRate i) (strictRate_pos i) ha hab
  have hi := intervalIntegral.integral_mono_on hab (hc.const_mul strictConstant) ht.neg
    (fun s hs => plane_strict_dissipation A hh u d i (ha.trans_le hs.1))
  rw [intervalIntegral.integral_const_mul] at hi
  change strictConstant * (∫ s in a..b, ∑ w, planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) ≤ ∫ s in a..b, -(totalPlaneTime A h u d (strictRate i) s) at hi
  rw [intervalIntegral.integral_neg,integral_totalPlaneTime A hh u d (strictRate i) (strictRate_pos i) ha hab] at hi
  linarith

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma telescope_with_jumps (E : ℕ → ℕ → ℝ) (n : ℕ) (hn : 0 ≤ E n n) :
    (∑ k ∈ Finset.range n, (E k k-E k (k+1))) ≤ E 0 0+
      ∑ k ∈ Finset.range n, |E (k+1) (k+1)-E k (k+1)| := by
  have he : (∑ k ∈ Finset.range n, (E k k-E k (k+1))) = E 0 0-E n n+
      ∑ k ∈ Finset.range n, (E (k+1) (k+1)-E k (k+1)) := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]; ring
  rw [he]
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    le_abs_self (E (k+1) (k+1)-E k (k+1)))
  linarith

def opening (a s : ℝ) (A : ℂ) : ℂ := if a ≤ s then A else 0

def windowMask (a b s : ℝ) (A : ℂ) : ℂ := if a ≤ s ∧ s < b then A else 0

lemma windowMask_eq_sub (a b s : ℝ) (hab : a ≤ b) (A : ℂ) :
    windowMask a b s A = opening a s A-opening b s A := by
  unfold windowMask opening
  split_ifs <;> simp_all <;> linarith

lemma windowMask_norm_le (a b s : ℝ) (A : ℂ) : ‖windowMask a b s A‖ ≤ ‖A‖ := by
  unfold windowMask
  split_ifs <;> simp

lemma sum_opening_variation (t : ℕ → ℝ) (ht : Monotone t) (a : ℝ) (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖opening a (t (k+1)) A-opening a (t k) A‖) =
      (if a ≤ t n then ‖A‖ else 0)-(if a ≤ t 0 then ‖A‖ else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    have hh := ht (Nat.le_succ n)
    have h0 := ht (Nat.zero_le n)
    unfold opening
    split_ifs <;> simp_all <;> linarith

lemma sum_windowMask_variation (t : ℕ → ℝ) (ht : Monotone t) (a b : ℝ) (hab : a ≤ b)
    (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖windowMask a b (t (k+1)) A-windowMask a b (t k) A‖) ≤ 2*‖A‖ := by
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    norm_sub_le (opening a (t (k+1)) A-opening a (t k) A)
      (opening b (t (k+1)) A-opening b (t k) A))
  have he (k : ℕ) : windowMask a b (t (k+1)) A-windowMask a b (t k) A =
      (opening a (t (k+1)) A-opening a (t k) A)-(opening b (t (k+1)) A-opening b (t k) A) := by
    rw [windowMask_eq_sub _ _ _ hab,windowMask_eq_sub _ _ _ hab]
    ring
  simp_rw [he]
  apply hi.trans
  rw [Finset.sum_add_distrib,sum_opening_variation t ht a A n,sum_opening_variation t ht b A n]
  split_ifs <;> linarith [norm_nonneg A]
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma arrayCubic_eq (D : Finset ℤ) (A : Three → Matrix D D ℂ) (h : ℝ) :
    arrayCubic A h = h^2*(∑ v, ∑ i, ∑ j, ‖A v i j‖^3) := by
  simp only [arrayCubic,Finset.mul_sum]

lemma arrayCubic_mono {ι : Type uι} [Fintype ι] (A B : Three → Matrix ι ι ℂ)
    (hAB : ∀ v i j, ‖A v i j‖ ≤ ‖B v i j‖) (h : ℝ) : arrayCubic A h ≤ arrayCubic B h := by
  unfold arrayCubic
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  gcongr
  exact hAB v i j

lemma arrayCubic_replaceZero_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (B : Matrix D D ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (h : ℝ) : arrayCubic (replaceZero A B) h ≤ arrayCubic A h := by
  apply arrayCubic_mono
  intro v i j
  by_cases hv : v=0
  · subst v; exact hB i j
  · simp [replaceZero,hv]

lemma finite_mesh_total_jumps_le (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    (B : ℕ → Matrix D D ℂ) (hB : ∀ k i j, ‖B k i j‖ ≤ ‖A 0 i j‖) (n : ℕ)
    (hvar : ∀ i j, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (σ : ℕ → Three → ℝ) (hσ : ∀ k v, h^2 ≤ σ k v) :
    (∑ k ∈ Finset.range n,
      |totalPlaneEnergy (replaceZero A (B (k+1))) h (fun m => h*(m:ℤ)) 0 (σ k)-
        totalPlaneEnergy (replaceZero A (B k)) h (fun m => h*(m:ℤ)) 0 (σ k)|) ≤
      3*meshMassConstant*jumpScalarConstant*arrayCubic A h := by
  have hj := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    finite_mesh_energy_jump_le D A (B (k+1)) (B k) (hB (k+1)) (hB k) hh (hσ k))
  apply hj.trans
  rw [← Finset.mul_sum]
  have he : (∑ k ∈ Finset.range n, ∑ i : D, ∑ j : D, ‖B (k+1) i j-B k i j‖*jumpMax D A i j) =
      ∑ i : D, ∑ j : D, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖)*jumpMax D A i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
  rw [he]
  have hs : (∑ i : D, ∑ j : D, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖)*jumpMax D A i j) ≤
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have ht := mul_le_mul_of_nonneg_right (hvar i j) (jumpMax_nonneg D A i j)
    simpa only [mul_assoc] using ht
  have hz : 0 ≤ 3/2*meshMassConstant*h^2 := by have hm := meshMassConstant_pos; positivity
  calc
    _ ≤ (3/2*meshMassConstant*h^2)*(2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j)) := mul_le_mul_of_nonneg_left hs hz
    _ ≤ (3/2*meshMassConstant*h^2)*(2*(jumpScalarConstant*(∑ v, ∑ i, ∑ j, ‖A v i j‖^3))) := by
      gcongr
      exact sum_jumpMax_le D A
    _ = _ := by rw [arrayCubic_eq]; ring

lemma strictRate_ge_one (i v : Three) : 1 ≤ strictRate i v := by
  unfold strictRate; split_ifs <;> norm_num

def maskedConstant : ℝ := meshMassConstant*(2*Real.sqrt 2+3*jumpScalarConstant)

lemma maskedConstant_pos : 0 < maskedConstant := by
  unfold maskedConstant
  have hm := meshMassConstant_pos
  have hj := jumpScalarConstant_pos
  positivity

lemma finite_masked_dissipation (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    (B : ℕ → Matrix D D ℂ) (hB : ∀ k i j, ‖B k i j‖ ≤ ‖A 0 i j‖) (n : ℕ)
    (hvar : ∀ i j, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : h^2 ≤ t 0) (r : Three) :
    strictConstant * (∑ k ∈ Finset.range n,
      ∫ s in t k..t (k+1), ∑ v, planeIntegral (fun p => heatCost (replaceZero A (B k)) h
        (fun m => h*(m:ℤ)) p (fun z => strictRate r z*s) v v) 0) ≤ maskedConstant*arrayCubic A h := by
  have htpos (k : ℕ) : 0 < t k := (sq_pos_of_pos hh).trans_le (ht0.trans (ht (Nat.zero_le _)))
  have hσ (k : ℕ) (v : Three) : h^2 ≤ strictRate r v*t k :=
    (ht0.trans (ht (Nat.zero_le _))).trans (le_mul_of_one_le_left (htpos k).le (strictRate_ge_one r v))
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    integrated_strict_dissipation (replaceZero A (B k)) hh (fun m => h*(m:ℤ)) 0 r
      (htpos k) (ht (Nat.le_succ k)))
  rw [← Finset.mul_sum] at hi
  apply hi.trans
  let E : ℕ → ℕ → ℝ := fun k l => totalPlaneEnergy (replaceZero A (B k)) h (fun m => h*(m:ℤ)) 0
    (fun v => strictRate r v*t l)
  have htel := telescope_with_jumps E n (totalPlaneEnergy_nonneg _ _ _ _ _)
  apply htel.trans
  have hin := (finite_mesh_totalPlaneEnergy_le D (replaceZero A (B 0)) hh 0 (hσ 0)).trans
    (mul_le_mul_of_nonneg_left (arrayCubic_replaceZero_le D A (B 0) (hB 0) h) (by have hm := meshMassConstant_pos; positivity))
  have hj := finite_mesh_total_jumps_le D A B hB n hvar hh (fun k v => strictRate r v*t (k+1)) (fun k v => hσ (k+1) v)
  change E 0 0 ≤ _ at hin
  change (∑ k ∈ Finset.range n, |E (k+1) (k+1)-E k (k+1)|) ≤ _ at hj
  apply (add_le_add hin hj).trans_eq
  unfold maskedConstant
  ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def sortedTimes (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) : ℝ :=
  S.orderEmbOfFin rfl ⟨min k (S.card-1),lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Finset.card_pos.mpr hS) (by omega))⟩

lemma sortedTimes_monotone (S : Finset ℝ) (hS : S.Nonempty) : Monotone (sortedTimes S hS) := by
  intro k l hkl
  apply (S.orderEmbOfFin rfl).monotone
  exact min_le_min_right _ hkl

lemma sortedTimes_mem (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) : sortedTimes S hS k ∈ S :=
  Finset.orderEmbOfFin_mem _ _ _

lemma sortedTimes_zero (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS 0 = S.min' hS := by
  exact Finset.orderEmbOfFin_zero rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_last (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS (S.card-1) = S.max' hS := by
  simp only [sortedTimes,min_self]
  exact Finset.orderEmbOfFin_last rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_no_between (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e : ℝ}
    (he : e ∈ S) : ¬ (sortedTimes S hS k < e ∧ e < sortedTimes S hS (k+1)) := by
  have he' : e ∈ Set.range (S.orderEmbOfFin rfl) := by simpa using he
  obtain ⟨j,rfl⟩ := he'
  intro ⟨h1,h2⟩
  have h1' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h1
  have h2' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h2
  change min k (S.card-1) < j.val at h1'
  change j.val < min (k+1) (S.card-1) at h2'
  omega

lemma sortedTimes_le_iff (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e s : ℝ}
    (he : e ∈ S) (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    e ≤ s ↔ e ≤ sortedTimes S hS k := by
  constructor
  · intro hes
    by_contra h
    exact sortedTimes_no_between S hS k he ⟨lt_of_not_ge h,hes.trans_lt hs.2⟩
  · exact fun h => h.trans hs.1

lemma sortedTimes_mask_const (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {a b s : ℝ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) (A : ℂ) :
    windowMask a b s A = windowMask a b (sortedTimes S hS k) A := by
  have h1 := sortedTimes_le_iff S hS k ha hs
  have h2 := not_congr (sortedTimes_le_iff S hS k hb hs)
  simp only [not_le] at h2
  simp only [windowMask,h1,h2]

lemma intervalIntegrable_of_Ico_eq {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (he : ∀ s ∈ Set.Ico a b, f s=g s) :
    IntervalIntegrable f volume a b := by
  apply hg.congr_ae
  rw [Set.uIoc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Ioc).2
  filter_upwards [volume.ae_ne b] with s hsb hs
  exact (he s ⟨hs.1.le,lt_of_le_of_ne hs.2 hsb⟩).symm

end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def maskedArray (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ) (s : ℝ) : Three → Matrix ι ι ℂ :=
  replaceZero A (fun i j => windowMask (a i j) (b i j) s (A 0 i j))

def maskedCost (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (h : ℝ) (u : ι → ℝ) (r : Three) (s : ℝ) : ℝ :=
  ∑ v, planeIntegral (fun p => heatCost (maskedArray A a b s) h u p (fun z => strictRate r z*s) v v) 0

omit [Fintype ι] [DecidableEq ι] in
lemma maskedArray_const (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    (k : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    maskedArray A a b s = maskedArray A a b (sortedTimes S hS k) := by
  unfold maskedArray
  congr 1
  funext i j
  exact sortedTimes_mask_const S hS k (ha i j) (hb i j) hs _

lemma planeSumCost_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (r : Three) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => ∑ v, planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b := by
  have hi : IntervalIntegrable (∑ v : Three, fun s => planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b :=
    IntervalIntegrable.sum Finset.univ (fun v _ => (planeTime_intervalIntegrable A hh u d (strictRate r) (strictRate_pos r) ha hab).2 v v)
  convert hi using 1
  ext s
  simp

lemma maskedCost_interval_piece (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (ht0 : 0 < sortedTimes S hS 0) (r : Three) (k : ℕ) :
    IntervalIntegrable (maskedCost A a b h u r) volume (sortedTimes S hS k) (sortedTimes S hS (k+1)) := by
  have ht := sortedTimes_monotone S hS
  apply intervalIntegrable_of_Ico_eq (ht (Nat.le_succ k))
    (planeSumCost_intervalIntegrable (maskedArray A a b (sortedTimes S hS k)) hh u 0 r
      (ht0.trans_le (ht (Nat.zero_le k))) (ht (Nat.le_succ k)))
  intro s hs
  unfold maskedCost
  rw [maskedArray_const A a b S hS ha hb k hs]

lemma masked_cost_integral_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (a b : Matrix D D ℝ)
    (hab : ∀ i j, a i j ≤ b i j) (S : Finset ℝ) (hS : S.Nonempty)
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (hl : ∀ s ∈ S, h^2 ≤ s) (r : Three) :
    strictConstant*(∫ s in S.min' hS..S.max' hS, maskedCost A a b h (fun m => h*(m:ℤ)) r s) ≤
      maskedConstant*arrayCubic A h := by
  let t := sortedTimes S hS
  have ht : Monotone t := sortedTimes_monotone S hS
  have ht0 : h^2 ≤ t 0 := hl _ (sortedTimes_mem S hS 0)
  let B : ℕ → Matrix D D ℂ := fun k i j => windowMask (a i j) (b i j) (t k) (A 0 i j)
  have hB (k : ℕ) (i j : D) : ‖B k i j‖ ≤ ‖A 0 i j‖ := windowMask_norm_le _ _ _ _
  have hv (i j : D) : (∑ k ∈ Finset.range (S.card-1), ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖ :=
    sum_windowMask_variation t ht _ _ (hab i j) _ _
  have hin := finite_masked_dissipation D A B hB (S.card-1) hv hh t ht ht0 r
  have he (k : ℕ) : (∫ s in t k..t (k+1), ∑ v, planeIntegral (fun p => heatCost (replaceZero A (B k)) h
      (fun m => h*(m:ℤ)) p (fun z => strictRate r z*s) v v) 0) =
      ∫ s in t k..t (k+1), maskedCost A a b h (fun m => h*(m:ℤ)) r s := by
    apply intervalIntegral.integral_congr_Ioo_of_le (ht (Nat.le_succ k))
    intro s hs
    unfold maskedCost
    rw [maskedArray_const A a b S hS ha hb k ⟨hs.1.le,hs.2⟩]
    rfl
  simp_rw [he] at hin
  rw [intervalIntegral.sum_integral_adjacent_intervals] at hin
  · simpa only [t,sortedTimes_zero,sortedTimes_last] using hin
  · intro k _
    exact maskedCost_interval_piece A a b S hS ha hb hh _ ((sq_pos_of_pos hh).trans_le ht0) r k
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def signedCenter (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (s : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(signedKernel s (u i+u j+u k):ℂ)

lemma signedCenter_eq_integral (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) : signedCenter A h u s = ∫ z : ℝ×ℝ, windowTrace A h u (chart 2 0 z) s := by
  have hi (i j k : ι) : Integrable (fun z : ℝ×ℝ => (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*
      ((oddWindow s (u i-z.1)*oddWindow s (u j-z.2)*oddWindow s (u k+z.1+z.2):ℝ):ℂ)) :=
    (oddWindow_triple_integrable hs (u i) (u j) (u k)).ofReal.const_mul _
  have he (z : ℝ×ℝ) : windowTrace A h u (chart 2 0 z) s =
      ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*
        ((oddWindow s (u i-z.1)*oddWindow s (u j-z.2)*oddWindow s (u k+z.1+z.2):ℝ):ℂ) := by
    rw [windowTrace_eq A hh hs]
    congr 1
    ext i
    congr 1
    ext j
    congr 1
    ext k
    rw [show chart 2 0 z 0 = z.1 by rfl,show chart 2 0 z 1 = z.2 by rfl,
      show chart 2 0 z 2 = 0-z.1-z.2 by rfl,show u k-(0-z.1-z.2) = u k+z.1+z.2 by ring]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k)))]
  unfold signedCenter
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul,integral_complex_ofReal,integral_oddWindow_triple hs]

lemma signedCenter_norm_le (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) : ‖signedCenter A h u s‖ ≤ (440/3)*s*∑ v,
      planeIntegral (fun p => heatCost A h u p (fun z => strictRate v z*s) v v) 0 := by
  have hi (v : Three) := (heatPlane_integrable A hh u 0 (fun z => mul_pos (strictRate_pos v z) hs)).cost 2 v v
  rw [signedCenter_eq_integral A hh hs]
  have hb := norm_integral_le_of_norm_le
    ((integrable_finsetSum _ (fun v _ => hi v)).const_mul ((440/3)*s))
    (Filter.Eventually.of_forall (fun z => windowTrace_le A hh hs u (chart 2 0 z)))
  apply hb.trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun v _ => hi v)]
  rfl

lemma continuousOn_signedKernel (t : ℝ) : ContinuousOn (fun s => signedKernel s t) (Set.Ioi 0) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have hs' : 0 < s := hs
  unfold signedKernel density
  fun_prop (disch := positivity)

lemma signedKernel_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    IntervalIntegrable (fun s => signedKernel s t / s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact ((continuousOn_signedKernel t).div continuousOn_id (fun s hs => ne_of_gt hs)).mono
    (fun s hs => ha.trans_le hs.1)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory
noncomputable section

lemma intervalIntegrable_indicator {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {L U a b : ℝ} (hf : IntervalIntegrable f volume L U) :
    IntervalIntegrable ((Set.Ico a b).indicator f) volume L U :=
  ⟨hf.1.indicator measurableSet_Ico,hf.2.indicator measurableSet_Ico⟩

lemma intervalIntegral_indicator_Ico {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {L U a b : ℝ} (hLa : L ≤ a) (hab : a ≤ b) (hbU : b ≤ U) :
    (∫ s in L..U, (Set.Ico a b).indicator f s) = ∫ s in a..b, f s := by
  rw [intervalIntegral.integral_of_le (hLa.trans (hab.trans hbU)),
    ← integral_Icc_eq_integral_Ioc,integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico]
  rw [Set.inter_eq_left.mpr (show Set.Ico a b ⊆ Set.Icc L U from fun s hs =>
    ⟨hLa.trans hs.1,hs.2.le.trans hbU⟩),integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

lemma intervalIntegrable_finsetSum {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ι → ℝ → E} (S : Finset ι) {a b : ℝ}
    (hf : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun s => ∑ i ∈ S, f i s) volume a b := by
  have hh := IntervalIntegrable.sum S hf
  convert! hh using 1
  ext s
  simp
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def smoothKernel (a b t : ℝ) : ℝ := ∫ s in a..b, signedKernel s t / s

def selectedSum (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(smoothKernel (a i j) (b i j) (u i+u j+u k):ℂ)

def maskedSigned (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) (s : ℝ) : ℂ :=
  signedCenter (maskedArray A a b s) h u s / (s:ℂ)

omit [DecidableEq ι] in
lemma maskedSigned_eq (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) (s : ℝ) :
    maskedSigned A h u a b s = ∑ i, ∑ j, ∑ k,
      (Set.Ico (a i j) (b i j)).indicator
        (fun s => (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*((signedKernel s (u i+u j+u k)/s:ℝ):ℂ)) s := by
  simp only [maskedSigned,signedCenter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change (h^3:ℝ)*(windowMask (a i j) (b i j) s (A 0 i j)*A 1 j k*A 2 k i)*
    (signedKernel s (u i+u j+u k):ℂ)/(s:ℂ) = _
  by_cases hs : s ∈ Set.Ico (a i j) (b i j)
  · rw [Set.indicator_of_mem hs]
    simp only [Set.mem_Ico] at hs
    simp only [windowMask,ite_eq_left hs]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hs]
    simp only [Set.mem_Ico] at hs
    simp only [windowMask,ite_eq_right hs]
    simp

omit [DecidableEq ι] in
lemma selectedSum_eq_integral (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (ha : ∀ i j, L ≤ a i j) (hab : ∀ i j, a i j ≤ b i j)
    (hb : ∀ i j, b i j ≤ U) : selectedSum A h u a b = ∫ s in L..U, maskedSigned A h u a b s := by
  have hc (i j k : ι) : IntervalIntegrable (fun s => ((signedKernel s (u i+u j+u k)/s:ℝ):ℂ)) volume L U :=
    ⟨(signedKernel_intervalIntegrable hL hLU (u i+u j+u k)).1.ofReal,
     (signedKernel_intervalIntegrable hL hLU (u i+u j+u k)).2.ofReal⟩
  have hi (i j k : ι) := intervalIntegrable_indicator
    ((hc i j k).const_mul ((h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i))) (a := a i j) (b := b i j)
  simp_rw [maskedSigned_eq]
  rw [intervalIntegral.integral_finsetSum (fun i _ => intervalIntegrable_finsetSum _ (fun j _ => intervalIntegrable_finsetSum _ (fun k _ => hi i j k)))]
  unfold selectedSum
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => intervalIntegrable_finsetSum _ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_finsetSum (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral_indicator_Ico (ha i j) (hab i j) (hb i j),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  rfl

lemma maskedSigned_norm_le (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (a b : Matrix ι ι ℝ) :
    ‖maskedSigned A h u a b s‖ ≤ (440/3)*∑ r, maskedCost A a b h u r s := by
  have hn (r w : Three) : 0 ≤ planeIntegral (fun p => heatCost (maskedArray A a b s) h u p
      (fun z => strictRate r z*s) w w) 0 := integral_nonneg (fun _ => heatCost_nonneg _ _ _ _ _ _ _)
  have hb : (∑ v, planeIntegral (fun p => heatCost (maskedArray A a b s) h u p
      (fun z => strictRate v z*s) v v) 0) ≤ ∑ r, maskedCost A a b h u r s := by
    apply Finset.sum_le_sum
    intro v _
    exact Finset.single_le_sum (fun w _ => hn v w) (Finset.mem_univ v)
  unfold maskedSigned
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hs.le]
  apply (div_le_div_of_nonneg_right (signedCenter_norm_le _ hh hs u) hs.le).trans
  rw [mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ hs.ne']
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma maskedCost_intervalIntegrable (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (hL : 0 < S.min' hS) (r : Three) :
    IntervalIntegrable (maskedCost A a b h u r) volume (S.min' hS) (S.max' hS) := by
  have ht0 : 0 < sortedTimes S hS 0 := by simpa only [sortedTimes_zero] using hL
  have hi := IntervalIntegrable.trans_iterate (n := S.card-1)
    (fun k _ => maskedCost_interval_piece A a b S hS ha hb hh u ht0 r k)
  simpa only [sortedTimes_zero,sortedTimes_last] using hi

def selectedConstant : ℝ := (440/3)*3*maskedConstant/strictConstant
lemma selectedConstant_pos : 0 < selectedConstant := by
  unfold selectedConstant
  exact div_pos (mul_pos (by norm_num) maskedConstant_pos) strictConstant_pos

lemma selectedSum_le_cubic (D : Finset ℤ) (A : Three → Matrix D D ℂ) (a b : Matrix D D ℝ)
    (hab : ∀ i j, a i j ≤ b i j) (S : Finset ℝ) (hS : S.Nonempty)
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (hl : ∀ s ∈ S, h^2 ≤ s) :
    ‖selectedSum A h (fun m => h*(m:ℤ)) a b‖ ≤ selectedConstant*arrayCubic A h := by
  have hL : 0 < S.min' hS := (sq_pos_of_pos hh).trans_le (hl _ (Finset.min'_mem S hS))
  have hLU : S.min' hS ≤ S.max' hS := Finset.min'_le S _ (Finset.max'_mem S hS)
  have hi r := maskedCost_intervalIntegrable A a b S hS ha hb hh (fun m => h*(m:ℤ)) hL r
  rw [selectedSum_eq_integral A _ _ a b hL hLU
    (fun i j => Finset.min'_le _ _ (ha i j)) hab (fun i j => Finset.le_max' _ _ (hb i j))]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hLU
    (Filter.Eventually.of_forall (fun s hs => maskedSigned_norm_le A hh (hL.trans hs.1) _ a b))
    ((intervalIntegrable_finsetSum _ (fun r _ => hi r)).const_mul (440/3:ℝ))
  apply hbound.trans
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (fun r _ => hi r)]
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset Three)) =>
    masked_cost_integral_le D A a b hab S hS ha hb hh hl r)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Three,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  have hc : (∑ r, ∫ s in S.min' hS..S.max' hS, maskedCost A a b h (fun m => h*(m:ℤ)) r s) ≤
      (3*(maskedConstant*arrayCubic A h))/strictConstant :=
    (le_div_iff₀ strictConstant_pos).mpr (by nlinarith only [hs])
  unfold selectedConstant
  calc
    _ ≤ (440/3)*((3*(maskedConstant*arrayCubic A h))/strictConstant) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

def kernelOutput (B C : Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) (i j : ι) : ℂ :=
  ∑ k, (h:ℂ)*B j k*C k i*(K i j (u i+u j+u k):ℂ)

def kernelPairing (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) : ℂ :=
  ∑ i, ∑ j, (h^2:ℝ)*A 0 i j*kernelOutput (A 1) (A 2) h u K i j

lemma kernelPairing_eq (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) :
    kernelPairing A h u K = ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(K i j (u i+u j+u k):ℂ) := by
  simp only [kernelPairing,kernelOutput,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

lemma kernelPairing_add (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K L : ι → ι → ℝ → ℝ) :
    kernelPairing A h u (fun i j t => K i j t+L i j t) = kernelPairing A h u K+kernelPairing A h u L := by
  simp only [kernelPairing_eq,Complex.ofReal_add,mul_add,Finset.sum_add_distrib]

lemma kernelPairing_const_mul (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) (c : ℝ) :
    kernelPairing A h u (fun i j t => c*K i j t) = (c:ℂ)*kernelPairing A h u K := by
  simp only [kernelPairing_eq,Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma kernelPairing_smooth [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) :
    kernelPairing A h u (fun i j => smoothKernel (a i j) (b i j)) = selectedSum A h u a b := by
  rw [kernelPairing_eq]
  rfl
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def scalePrimitive (s t : ℝ) : ℝ :=
  2*(Real.sqrt s*((t^2/9)/s-1/3))*density (3*s) t/t

lemma density_three_hasDerivAt {s : ℝ} (hs : 0 < s) (t : ℝ) :
    HasDerivAt (fun s => density (3*s) t)
      ((1/2)*((t/(3*s))^2-(3*s)⁻¹)*density (3*s) t*3) s := by
  have hd := (weight_hasDerivAt_variance 1 t 0 (3*s) (by positivity)).comp s
    ((hasDerivAt_id s).const_mul 3)
  simpa only [weight,score,sub_zero,one_mul,mul_one,Function.comp_def] using hd

lemma scalePrimitive_hasDerivAt {s t : ℝ} (hs : 0 < s) (ht : t ≠ 0) :
    HasDerivAt (fun s => scalePrimitive s t) (signedKernel s t/s) s := by
  have hr := Real.hasDerivAt_sqrt hs.ne'
  have hq := ((hasDerivAt_const s (t^2/9)).div (hasDerivAt_id s) hs.ne').sub_const (1/3)
  have hd := ((((hr.mul hq).const_mul 2).mul (density_three_hasDerivAt hs t)).div_const t)
  convert! hd using 1
  unfold signedKernel
  dsimp
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hs.le]
  ring

lemma smoothKernel_eq_primitive {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    (∫ s in a..b, signedKernel s t/s) = scalePrimitive b t-scalePrimitive a t := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact scalePrimitive_hasDerivAt (ha.trans_le hs.1) ht
  · exact signedKernel_intervalIntegrable ha hab t

def kernelConstant : ℝ := -(2/3)*density 3 0

def kernelProfile (v : ℝ) : ℝ := kernelConstant-2*(v^2/9-1/3)*density 3 v

lemma kernelConstant_ne_zero : kernelConstant ≠ 0 := by
  unfold kernelConstant
  exact mul_ne_zero (by norm_num) (density_pos (by norm_num) 0).ne'

lemma scalePrimitive_profile {s t : ℝ} (hs : 0 < s) :
    scalePrimitive s t = (kernelConstant-kernelProfile (t/Real.sqrt s))/t := by
  have hd := density_dilation hs (by norm_num : 0 < (3:ℝ)) t
  have he : density 3 (t/Real.sqrt s) = Real.sqrt s*density (3*s) t := by
    rw [hd]
    field_simp
  unfold kernelProfile scalePrimitive
  rw [he]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

lemma smoothKernel_eq_profile {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    (∫ s in a..b, signedKernel s t/s) =
      (kernelProfile (t/Real.sqrt a)-kernelProfile (t/Real.sqrt b))/t := by
  rw [smoothKernel_eq_primitive ha hab ht,scalePrimitive_profile (ha.trans_le hab),scalePrimitive_profile ha]
  ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def errorProfile (v : ℝ) : ℝ := kernelProfile v - if 1 < |v| then kernelConstant else 0

def endpointError (r t : ℝ) : ℝ := errorProfile (t/r)/t

lemma kernelProfile_zero : kernelProfile 0 = 0 := by
  unfold kernelProfile kernelConstant
  ring

lemma profile_contDiff : ContDiff ℝ 1 kernelProfile := by
  unfold kernelProfile density
  fun_prop

lemma density_three_six (v : ℝ) :
    density 3 v = Real.sqrt 2*Real.exp (-v^2/12)*density 6 v := by
  have hp : Real.sqrt (2*Real.pi*3) ≠ 0 := by positivity
  have h2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  unfold density
  rw [show 2*Real.pi*6 = 2*(2*Real.pi*3) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have he : -v^2/(2*3) = -v^2/12 + -v^2/(2*6) := by ring
  rw [he,Real.exp_add]
  field_simp

lemma polynomial_exp_le (v : ℝ) : (v^2/9+1/3)*Real.exp (-v^2/12) ≤ 5/3 := by
  have ha := Real.add_one_le_exp (v^2/12)
  have he : Real.exp (v^2/12)*Real.exp (-v^2/12) = 1 := by
    rw [← Real.exp_add,show v^2/12+-v^2/12=0 by ring,Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_right ha (Real.exp_pos (-v^2/12)).le
  rw [he] at hm
  have hle : Real.exp (-v^2/12) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg v])
  nlinarith

lemma errorProfile_exists_bound : ∃ K : ℝ, 0 < K ∧ ∀ v,
    |errorProfile v| ≤ K*|v| *density 6 v := by
  obtain ⟨L,hL⟩ := profile_contDiff.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1:WithTop ℕ∞) ≠ 0) (convex_Icc (-1:ℝ) 1) (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  let K : ℝ := (L:ℝ)/density 6 1 + 10*Real.sqrt 2
  have hd : 0 < density 6 1 := density_pos (by norm_num) 1
  have hK : 0 < K := add_pos_of_nonneg_of_pos (div_nonneg L.coe_nonneg hd.le) (by positivity)
  refine ⟨K,hK,fun v => ?_⟩
  by_cases hv : 1 < |v|
  · have he : errorProfile v = -2*(v^2/9-1/3)*density 3 v := by
      unfold errorProfile kernelProfile
      rw [ite_eq_left hv]
      ring
    have hab : |v^2/9-1/3| ≤ v^2/9+1/3 := by
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg v],by linarith⟩
    have hb : |errorProfile v| ≤ (10/3)*Real.sqrt 2*density 6 v := by
      rw [he,abs_mul,abs_mul,abs_of_nonneg (density_nonneg (by norm_num) v)]
      norm_num only [abs_neg]
      calc
        _ ≤ 2*(v^2/9+1/3)*density 3 v := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hab (by norm_num)) (density_nonneg (by norm_num) v)
        _ = 2*Real.sqrt 2*((v^2/9+1/3)*Real.exp (-v^2/12))*density 6 v := by rw [density_three_six]; ring
        _ ≤ 2*Real.sqrt 2*(5/3)*density 6 v := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_exp_le v) (by positivity)) (density_nonneg (by norm_num) v)
        _ = _ := by ring
    apply hb.trans
    have hk : 10*Real.sqrt 2 ≤ K := le_add_of_nonneg_left (div_nonneg L.coe_nonneg hd.le)
    apply mul_le_mul_of_nonneg_right _ (density_nonneg (by norm_num) v)
    calc
      (10/3)*Real.sqrt 2 ≤ 10*Real.sqrt 2 := by gcongr; norm_num
      _ ≤ K := hk
      _ ≤ K*|v| := le_mul_of_one_le_right hK.le hv.le
  · have hv' : |v| ≤ 1 := le_of_not_gt hv
    have hmem : v ∈ Set.Icc (-1:ℝ) 1 := abs_le.mp hv'
    have hb : |kernelProfile v| ≤ (L:ℝ)*|v| := by
      have hh := hL.dist_le_mul v hmem 0 (by constructor <;> norm_num)
      simpa only [Real.dist_eq,kernelProfile_zero,sub_zero] using hh
    have hden : density 6 1 ≤ density 6 v := by
      unfold density
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hs : v^2 ≤ 1 := by nlinarith [sq_abs v,abs_nonneg v]
      nlinarith
    unfold errorProfile
    rw [ite_eq_right hv,sub_zero]
    apply hb.trans
    have hk : (L:ℝ) ≤ K*density 6 v := by
      calc
        (L:ℝ) = ((L:ℝ)/density 6 1)*density 6 1 := (div_mul_cancel₀ _ hd.ne').symm
        _ ≤ ((L:ℝ)/density 6 1)*density 6 v := mul_le_mul_of_nonneg_left hden (div_nonneg L.coe_nonneg hd.le)
        _ ≤ K*density 6 v := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by positivity)) (density_nonneg (by norm_num) v)
    nlinarith [mul_le_mul_of_nonneg_right hk (abs_nonneg v)]

def envelopeConstant : ℝ := errorProfile_exists_bound.choose
lemma envelopeConstant_pos : 0 < envelopeConstant := errorProfile_exists_bound.choose_spec.1
lemma errorProfile_bound (v : ℝ) : |errorProfile v| ≤ envelopeConstant*|v| *density 6 v :=
  errorProfile_exists_bound.choose_spec.2 v

lemma endpointError_bound {r : ℝ} (hr : 0 < r) (t : ℝ) :
    |endpointError r t| ≤ envelopeConstant*density (6*r^2) t := by
  by_cases ht : t = 0
  · subst t
    simp only [endpointError,div_zero,abs_zero]
    exact mul_nonneg envelopeConstant_pos.le (density_nonneg (by positivity) _)
  have hd := density_dilation (sq_pos_of_pos hr) (by norm_num : (0:ℝ)<6) t
  rw [Real.sqrt_sq hr.le] at hd
  unfold endpointError
  rw [abs_div]
  apply (div_le_div_of_nonneg_right (errorProfile_bound (t/r)) (abs_nonneg t)).trans_eq
  rw [abs_div,abs_of_pos hr,hd]
  field_simp

end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma errorOutput_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (i j : D) :
    ‖kernelOutput (A 1) (A 2) h (fun m => h*(m:ℤ)) (fun a b => endpointError (r a b)) i j‖ ≤
      envelopeConstant*meshMassConstant*jumpMax D A i j := by
  have hri := hh.trans_le (hr i j)
  have hs : h^2 ≤ 6*(r i j)^2 := by have hr' := hr i j; nlinarith [sq_nonneg (r i j),sq_nonneg h]
  have hed (k : D) : h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ) = h*((((k:ℤ)-(-(i:ℤ)-(j:ℤ))):ℤ):ℝ) := by
    push_cast
    ring
  have h1 := gaussian_sum_le_lineMax D (fun k => ‖A 1 j k‖^2) (fun _ => sq_nonneg _) hh hs (-(i:ℤ)-(j:ℤ))
  have h2 := gaussian_sum_le_lineMax D (fun k => ‖A 2 k i‖^2) (fun _ => sq_nonneg _) hh hs (-(i:ℤ)-(j:ℤ))
  simp_rw [← hed] at h1 h2
  unfold kernelOutput
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k, envelopeConstant*(‖A 1 j k‖^2+‖A 2 k i‖^2)*
        (h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hh.le,Real.norm_eq_abs]
      have hp : ‖A 1 j k‖*‖A 2 k i‖ ≤ ‖A 1 j k‖^2+‖A 2 k i‖^2 := by nlinarith [sq_nonneg (‖A 1 j k‖-‖A 2 k i‖)]
      have hg := endpointError_bound hri (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))
      calc
        _ ≤ h*‖A 1 j k‖*‖A 2 k i‖*(envelopeConstant*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by gcongr
        _ = envelopeConstant*(‖A 1 j k‖*‖A 2 k i‖)*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp envelopeConstant_pos.le)
          (mul_nonneg hh.le (density_nonneg (by positivity) _))
    _ = envelopeConstant*((∑ k, ‖A 1 j k‖^2*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))))+
        (∑ k, ‖A 2 k i‖^2*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))))) := by
      simp only [mul_assoc,mul_add,add_mul,Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ envelopeConstant*(meshMassConstant*lineMax D (fun k => ‖A 1 j k‖^2) (-(i:ℤ)-(j:ℤ))+
        meshMassConstant*lineMax D (fun k => ‖A 2 k i‖^2) (-(i:ℤ)-(j:ℤ))) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) envelopeConstant_pos.le
    _ ≤ _ := by
      unfold jumpMax
      have h0 := lineMax_nonneg D (fun k => ‖A 0 i k‖^2) (fun _ => sq_nonneg _) (j:ℤ)
      have h3 := lineMax_nonneg D (fun k => ‖A 0 k j‖^2) (fun _ => sq_nonneg _) (i:ℤ)
      have hC := envelopeConstant_pos
      have hM := meshMassConstant_pos
      nlinarith [mul_nonneg (mul_nonneg hC.le hM.le) h0,mul_nonneg (mul_nonneg hC.le hM.le) h3]

def errorPairingConstant : ℝ := envelopeConstant*meshMassConstant*jumpScalarConstant
lemma errorPairingConstant_pos : 0 < errorPairingConstant :=
  mul_pos (mul_pos envelopeConstant_pos meshMassConstant_pos) jumpScalarConstant_pos

lemma errorPairing_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) :
    ‖kernelPairing A h (fun m => h*(m:ℤ)) (fun i j => endpointError (r i j))‖ ≤
      errorPairingConstant*arrayCubic A h := by
  unfold kernelPairing
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, ∑ j, h^2*‖A 0 i j‖*(envelopeConstant*meshMassConstant*jumpMax D A i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg h)]
      exact mul_le_mul_of_nonneg_left (errorOutput_le D A hh r hr i j) (by positivity)
    _ = envelopeConstant*meshMassConstant*h^2*(∑ i, ∑ j, ‖A 0 i j‖*jumpMax D A i j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ envelopeConstant*meshMassConstant*h^2*(jumpScalarConstant*(∑ v,∑ i,∑ j,‖A v i j‖^3)) :=
      mul_le_mul_of_nonneg_left (sum_jumpMax_le D A) (mul_nonneg (mul_nonneg envelopeConstant_pos.le meshMassConstant_pos.le) (sq_nonneg h))
    _ = _ := by
      unfold errorPairingConstant arrayCubic
      simp only [← Finset.mul_sum]
      ring
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def hardKernel (r R t : ℝ) : ℝ :=
  ((if r < |t| then 1 else 0)-(if R < |t| then 1 else 0))/t

lemma hardKernel_decomposition {r R : ℝ} (hr : 0 < r) (hb : r ≤ R) (t : ℝ) :
    smoothKernel (r^2) (R^2) t = kernelConstant*hardKernel r R t+endpointError r t-endpointError R t := by
  have hR := hr.trans_le hb
  by_cases ht : t = 0
  · subst t
    simp [smoothKernel,signedKernel,hardKernel,endpointError]
  unfold smoothKernel
  rw [smoothKernel_eq_profile (sq_pos_of_pos hr) (by nlinarith) ht,Real.sqrt_sq hr.le,Real.sqrt_sq hR.le]
  unfold endpointError errorProfile hardKernel
  simp only [abs_div,abs_of_pos hr,abs_of_pos hR,lt_div_iff₀ hr,lt_div_iff₀ hR,one_mul]
  split_ifs <;> ring

lemma selectedSum_le_no_finset (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    ‖selectedSum A h (fun m => h*(m:ℤ)) (fun i j => (r i j)^2) (fun i j => (R i j)^2)‖ ≤
      selectedConstant*arrayCubic A h := by
  classical
  let S : Finset ℝ := insert (h^2) ((Finset.univ.image (fun p : D×D => (r p.1 p.2)^2)) ∪
    (Finset.univ.image (fun p : D×D => (R p.1 p.2)^2)))
  apply selectedSum_le_cubic D A _ _ (fun i j => by have hh' := hr i j; have hb' := hb i j; nlinarith) S
    (Finset.insert_nonempty _ _) ?_ ?_ hh ?_
  · intro i j
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩))
  · intro i j
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩))
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hs
    · rfl
    rcases Finset.mem_union.mp hs with hs|hs
    · rcases Finset.mem_image.mp hs with ⟨⟨i,j⟩,_,rfl⟩
      have hh' := hr i j
      nlinarith
    · rcases Finset.mem_image.mp hs with ⟨⟨i,j⟩,_,rfl⟩
      have hh' := (hr i j).trans (hb i j)
      nlinarith

def hardPairingConstant : ℝ := (selectedConstant+2*errorPairingConstant)/|kernelConstant|
lemma hardPairingConstant_pos : 0 < hardPairingConstant := by
  unfold hardPairingConstant
  exact div_pos (add_pos selectedConstant_pos (mul_pos (by norm_num) errorPairingConstant_pos)) (abs_pos.mpr kernelConstant_ne_zero)

lemma hardPairing_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    ‖kernelPairing A h (fun m => h*(m:ℤ)) (fun i j => hardKernel (r i j) (R i j))‖ ≤
      hardPairingConstant*arrayCubic A h := by
  classical
  let u : D → ℝ := fun m => h*(m:ℤ)
  have he : (kernelConstant:ℂ)*kernelPairing A h u (fun i j => hardKernel (r i j) (R i j)) =
      selectedSum A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)-
        kernelPairing A h u (fun i j => endpointError (r i j))+
        kernelPairing A h u (fun i j => endpointError (R i j)) := by
    have hk : (fun i j => smoothKernel ((r i j)^2) ((R i j)^2)) = (fun i j t =>
        kernelConstant*hardKernel (r i j) (R i j) t+endpointError (r i j) t+-1*endpointError (R i j) t) := by
      funext i j t
      convert hardKernel_decomposition (hh.trans_le (hr i j)) (hb i j) t using 1
      ring
    have hs := kernelPairing_smooth A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)
    rw [hk,kernelPairing_add,kernelPairing_add,kernelPairing_const_mul,kernelPairing_const_mul] at hs
    push_cast at hs
    linear_combination hs
  have hn := (norm_add_le (selectedSum A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)-
      kernelPairing A h u (fun i j => endpointError (r i j)))
      (kernelPairing A h u (fun i j => endpointError (R i j)))).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  rw [← he,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hn
  have h1 := selectedSum_le_no_finset D A hh r R hr hb
  have h2 := errorPairing_le D A hh r hr
  have h3 := errorPairing_le D A hh R (fun i j => (hr i j).trans (hb i j))
  have hden := abs_pos.mpr kernelConstant_ne_zero
  rw [hardPairingConstant,div_mul_eq_mul_div,le_div_iff₀ hden]
  dsimp [u] at hn
  nlinarith only [hn,h1,h2,h3]
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma abs_hardKernel_le {r R : ℝ} (hr : 0 < r) (hb : r ≤ R) (t : ℝ) : |hardKernel r R t| ≤ 1/r := by
  unfold hardKernel
  by_cases hrt : r < |t|
  · by_cases hRt : R < |t|
    · simp [hrt,hRt,hr.le]
    · simp only [hrt,hRt,ite_true,ite_false,sub_zero,abs_div,abs_one]
      exact one_div_le_one_div_of_le hr hrt.le
  · have hRt : ¬R < |t| := fun h => hrt (hb.trans_lt h)
    simp [hrt,hRt,hr.le]

lemma measurable_hardKernel (r R : ℝ) : Measurable (hardKernel r R) := by
  unfold hardKernel
  exact ((measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const).sub
    (measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const)).div measurable_id

lemma continuousAt_absStep (r t : ℝ) (ht : |t| ≠ r) :
    ContinuousAt (fun x : ℝ => if r < |x| then (1:ℝ) else 0) t := by
  rcases lt_or_gt_of_ne ht with h|h
  · have he : ∀ᶠ x in 𝓝 t, |x| < r := continuous_abs.continuousAt.eventually (eventually_lt_nhds h)
    apply (show ContinuousAt (fun _ : ℝ => (0:ℝ)) t from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp only [not_lt.mpr hx.le,ite_false]
  · have he : ∀ᶠ x in 𝓝 t, r < |x| := continuous_abs.continuousAt.eventually (eventually_gt_nhds h)
    apply (show ContinuousAt (fun _ : ℝ => (1:ℝ)) t from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp only [hx,ite_true]

lemma continuousAt_hardKernel (r R t : ℝ) (ht0 : t ≠ 0) (htr : |t| ≠ r) (htR : |t| ≠ R) :
    ContinuousAt (hardKernel r R) t :=
  ((continuousAt_absStep r t htr).sub (continuousAt_absStep R t htR)).div continuousAt_id ht0
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def gridCell (h : ℝ) (i : ℤ) : Set ℝ := Set.Ico (h*i) (h*(i+1))
def gridIndex (h x : ℝ) : ℤ := ⌊x/h⌋
def gridPoint (h x : ℝ) : ℝ := h*gridIndex h x

lemma gridCell_mem_iff {h x : ℝ} (hh : 0 < h) (i : ℤ) :
    x ∈ gridCell h i ↔ gridIndex h x = i := by
  unfold gridCell gridIndex
  rw [Int.floor_eq_iff]
  simp only [Set.mem_Ico]
  constructor
  · intro hx
    exact ⟨(le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hx.1),
      (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using hx.2)⟩
  · intro hx
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hh).mp hx.1,
      by simpa only [mul_comm] using (div_lt_iff₀ hh).mp hx.2⟩

lemma gridPoint_le {h : ℝ} (hh : 0 < h) (x : ℝ) : gridPoint h x ≤ x := by
  exact ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).1

lemma gridPoint_lt_add {h : ℝ} (hh : 0 < h) (x : ℝ) : x < gridPoint h x+h := by
  have hh' := ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).2
  dsimp [gridCell,gridPoint] at *
  linarith only [hh']

lemma abs_gridPoint_sub_lt {h : ℝ} (hh : 0 < h) (x : ℝ) : |gridPoint h x-x| < h := by
  rw [abs_of_nonpos (sub_nonpos.mpr (gridPoint_le hh x))]
  linarith only [gridPoint_lt_add hh x]

lemma volume_gridCell (h : ℝ) (i : ℤ) : volume (gridCell h i) = ENNReal.ofReal h := by
  rw [gridCell,Real.volume_Ico]
  congr 1
  ring

def gridRect (h : ℝ) (i j : ℤ) : Set (ℝ×ℝ) := gridCell h i ×ˢ gridCell h j

def gridLift (D : Finset ℤ) (h : ℝ) {E : Type uE} [AddCommMonoid E] (f : D → D → E) (z : ℝ×ℝ) : E :=
  ∑ i : D, ∑ j : D, (gridRect h i j).indicator (fun _ => f i j) z

lemma gridRect_mem_iff {h : ℝ} (hh : 0 < h) (z : ℝ×ℝ) (i j : ℤ) :
    z ∈ gridRect h i j ↔ gridIndex h z.1 = i ∧ gridIndex h z.2 = j := by
  exact and_congr (gridCell_mem_iff hh i) (gridCell_mem_iff hh j)

lemma gridLift_eq {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} [AddCommMonoid E]
    (f : D → D → E) (z : ℝ×ℝ) : gridLift D h f z =
      if hi : gridIndex h z.1 ∈ D then if hj : gridIndex h z.2 ∈ D then
        f ⟨gridIndex h z.1,hi⟩ ⟨gridIndex h z.2,hj⟩ else 0 else 0 := by
  classical
  unfold gridLift
  simp_rw [Set.indicator_apply,gridRect_mem_iff hh]
  split_ifs with hi hj
  · rw [Finset.sum_eq_single (⟨gridIndex h z.1,hi⟩:D)]
    · rw [Finset.sum_eq_single (⟨gridIndex h z.2,hj⟩:D)]
      · simp
      · intro j _ hj'
        have hne : gridIndex h z.2 ≠ (j:ℤ) := by intro he; exact hj' (Subtype.ext he.symm)
        simp only [hne,and_false,ite_false]
      · simp
    · intro i _ hi'
      have hne : gridIndex h z.1 ≠ (i:ℤ) := by intro he; exact hi' (Subtype.ext he.symm)
      simp only [hne,false_and,ite_false,Finset.sum_const_zero]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hne : gridIndex h z.2 ≠ (j:ℤ) := by intro he; exact hj (he ▸ j.property)
    simp only [hne,and_false,ite_false]
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hne : gridIndex h z.1 ≠ (i:ℤ) := by intro he; exact hi (he ▸ i.property)
    simp only [hne,false_and,ite_false]

lemma gridLift_comp {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} {F : Type uF} [AddCommMonoid E] [AddCommMonoid F]
    (f : D → D → E) (g : E → F) (hg : g 0 = 0) (z : ℝ×ℝ) :
    g (gridLift D h f z) = gridLift D h (fun i j => g (f i j)) z := by
  simp only [gridLift_eq hh]
  split_ifs <;> simp only [hg]

lemma measurableSet_gridRect (h : ℝ) (i j : ℤ) : MeasurableSet (gridRect h i j) :=
  measurableSet_Ico.prod measurableSet_Ico

lemma volume_gridRect (h : ℝ) (i j : ℤ) : volume (gridRect h i j) = (ENNReal.ofReal h)^2 := by
  change (volume.prod volume) (gridCell h i ×ˢ gridCell h j) = _
  rw [Measure.prod_prod,volume_gridCell,volume_gridCell,pow_two]

lemma integral_gridLift (D : Finset ℤ) (h : ℝ) {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D → D → E) (hh : 0 ≤ h) :
    (∫ z : ℝ×ℝ, gridLift D h f z) = ∑ i, ∑ j, h^2 • f i j := by
  have hi (i j : D) : Integrable ((gridRect h i j).indicator (fun _ : ℝ×ℝ => f i j)) :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := gridRect h i j) (C := f i j)
        (by rw [volume_gridRect]; finiteness)) (measurableSet_gridRect h i j)
  unfold gridLift
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (measurableSet_gridRect h i j),setIntegral_const,measureReal_def,volume_gridRect,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hh]
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_gridIndex (h : ℝ) : Measurable (gridIndex h) := by
  exact Int.measurable_floor.comp (measurable_id.div_const h)

lemma measurable_gridPoint (h : ℝ) : Measurable (gridPoint h) := by
  exact measurable_const.mul ((measurable_of_countable (fun i : ℤ => (i:ℝ))).comp (measurable_gridIndex h))

def gridSquare (h : ℝ) (z : ℝ×ℝ) : ℝ×ℝ := (gridPoint h z.1,gridPoint h z.2)

lemma measurable_gridSquare (h : ℝ) : Measurable (gridSquare h) :=
  ((measurable_gridPoint h).comp measurable_fst).prodMk ((measurable_gridPoint h).comp measurable_snd)

lemma tendsto_gridPoint {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => gridPoint (h n) x) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ht
  exact (show ‖gridPoint (h n) x-x‖ < h n by simpa only [Real.norm_eq_abs] using abs_gridPoint_sub_lt (hh n) x).le

lemma tendsto_gridSquare {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (z : ℝ×ℝ) :
    Tendsto (fun n => gridSquare (h n) z) atTop (𝓝 z) :=
  (tendsto_gridPoint hh ht z.1).prodMk_nhds (tendsto_gridPoint hh ht z.2)

def sampleIndices (h M : ℝ) : Finset ℤ := Finset.Icc ⌈-M/h⌉ ⌊M/h⌋

lemma mem_sampleIndices {h : ℝ} (hh : 0 < h) (M : ℝ) (i : ℤ) :
    i ∈ sampleIndices h M ↔ |h*i| ≤ M := by
  rw [sampleIndices,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor
  · rintro ⟨hi,hj⟩
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hh).mp hi,
      by simpa only [mul_comm] using (le_div_iff₀ hh).mp hj⟩
  · rintro ⟨hi,hj⟩
    exact ⟨(div_le_iff₀ hh).mpr (by simpa only [mul_comm] using hi),
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hj)⟩

def sampledMatrix {E : Type uE} (f : ℝ×ℝ → E) (h M : ℝ) :
    sampleIndices h M → sampleIndices h M → E := fun i j => f (h*(i:ℤ),h*(j:ℤ))

lemma gridLift_sampled {E : Type uE} [AddCommMonoid E] (f : ℝ×ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hf : ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M) (z : ℝ×ℝ) :
    gridLift (sampleIndices h M) h (sampledMatrix f h M) z = f (gridSquare h z) := by
  rw [gridLift_eq hh]
  split_ifs with hi hj
  · rfl
  · symm
    by_contra hn
    exact hj ((mem_sampleIndices hh M _).mpr (hf _ hn).2)
  · symm
    by_contra hn
    exact hi ((mem_sampleIndices hh M _).mpr (hf _ hn).1)

lemma sampled_support {E : Type uE} [Zero E] (f : ℝ×ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hf : ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M)
    (z : ℝ×ℝ) (hz : f (gridSquare h z) ≠ 0) :
    |z.1| ≤ M+1 ∧ |z.2| ≤ M+1 := by
  have ha := hf _ hz
  have h1 := abs_gridPoint_sub_lt hh z.1
  have h2 := abs_gridPoint_sub_lt hh z.2
  have e1 := abs_add_le (z.1-gridPoint h z.1) (gridPoint h z.1)
  have e2 := abs_add_le (z.2-gridPoint h z.2) (gridPoint h z.2)
  simp only [sub_add_cancel] at e1 e2
  rw [abs_sub_comm] at h1 h2
  dsimp [gridSquare] at ha
  exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def gridLine (D : Finset ℤ) (h : ℝ) {E : Type uE} [AddCommMonoid E] (f : D → E) (x : ℝ) : E :=
  ∑ i : D, (gridCell h i).indicator (fun _ => f i) x

lemma gridLine_eq {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} [AddCommMonoid E]
    (f : D → E) (x : ℝ) : gridLine D h f x =
      if hi : gridIndex h x ∈ D then f ⟨gridIndex h x,hi⟩ else 0 := by
  classical
  unfold gridLine
  simp_rw [Set.indicator_apply,gridCell_mem_iff hh]
  split_ifs with hi
  · rw [Finset.sum_eq_single (⟨gridIndex h x,hi⟩:D)]
    · simp
    · intro i _ hi'
      have hne : gridIndex h x ≠ (i:ℤ) := by intro he; exact hi' (Subtype.ext he.symm)
      simp only [hne,ite_false]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hne : gridIndex h x ≠ (i:ℤ) := by intro he; exact hi (he ▸ i.property)
    simp only [hne,ite_false]

lemma gridLine_sampled {E : Type uE} [AddCommMonoid E] (f : ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hf : ∀ x, f x ≠ 0 → |x| ≤ M) (x : ℝ) :
    gridLine (sampleIndices h M) h (fun i => f (h*(i:ℤ))) x = f (gridPoint h x) := by
  rw [gridLine_eq hh]
  split_ifs with hi
  · rfl
  · symm
    by_contra hn
    exact hi ((mem_sampleIndices hh M _).mpr (hf _ hn))

lemma integral_gridLine (D : Finset ℤ) (h : ℝ) {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D → E) (hh : 0 ≤ h) :
    (∫ x : ℝ, gridLine D h f x) = ∑ i, h • f i := by
  have hi (i : D) : Integrable ((gridCell h i).indicator (fun _ : ℝ => f i)) :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := gridCell h i) (C := f i)
        (by rw [volume_gridCell]; finiteness)) measurableSet_Ico
  unfold gridLine
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (show MeasurableSet (gridCell h i) from measurableSet_Ico),setIntegral_const,measureReal_def,volume_gridCell,
    ENNReal.toReal_ofReal hh]

lemma integral_sampled_line {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {h M : ℝ} (hh : 0 < h) (hf : ∀ x, f x ≠ 0 → |x| ≤ M) :
    (∫ x : ℝ, f (gridPoint h x)) = ∑ i : sampleIndices h M, h • f (h*(i:ℤ)) := by
  have he : (fun x => f (gridPoint h x)) = gridLine (sampleIndices h M) h (fun i => f (h*(i:ℤ))) :=
    funext (fun x => (gridLine_sampled f hh hf x).symm)
  rw [he,integral_gridLine _ _ _ hh.le]
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

def closedBox (M : ℝ) : Set (ℝ×ℝ) := Set.Icc (-M) M ×ˢ Set.Icc (-M) M
lemma mem_closedBox (M : ℝ) (z : ℝ×ℝ) : z ∈ closedBox M ↔ |z.1| ≤ M ∧ |z.2| ≤ M := by
  simp only [closedBox,Set.mem_prod,Set.mem_Icc,abs_le]
lemma measurableSet_closedBox (M : ℝ) : MeasurableSet (closedBox M) := measurableSet_Icc.prod measurableSet_Icc
lemma isCompact_closedBox (M : ℝ) : IsCompact (closedBox M) := isCompact_Icc.prod isCompact_Icc
lemma volume_closedBox_ne_top (M : ℝ) : volume (closedBox M) ≠ ⊤ := (isCompact_closedBox M).measure_ne_top

def BoxSupport {E : Type uE} [Zero E] (f : ℝ×ℝ → E) (M : ℝ) : Prop :=
  ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M

lemma compactSupport_box {E : Type uE} [Zero E] (f : ℝ×ℝ → E) (hf : HasCompactSupport f) :
    ∃ M > 0, BoxSupport f M := by
  obtain ⟨M,hM,hm⟩ := hf.isBounded.exists_pos_norm_le
  refine ⟨M,hM,fun z hz => ?_⟩
  have hb := hm z (subset_tsupport f hz)
  have hleft : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hright : |z.2| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le z
  exact ⟨hleft.trans hb,hright.trans hb⟩

lemma sampled_cubic_tendsto (f : ℝ×ℝ → ℂ) (hf : Continuous f) {M C : ℝ}
    (hs : BoxSupport f M) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖f (gridSquare (h n) z)‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by
  let b : ℝ×ℝ → ℝ := (closedBox (M+1)).indicator (fun _ => C^3)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact (((hf.measurable.comp (measurable_gridSquare (h n))).norm).pow_const 3).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := closedBox (M+1)) (C := C^3)
      (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)
  · intro n
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    by_cases hz : f (gridSquare (h n) z) = 0
    · simp only [hz,norm_zero,zero_pow (by norm_num : 3 ≠ 0),b]
      exact Set.indicator_nonneg (fun _ _ => pow_nonneg hC _) _
    · dsimp only [b]
      rw [Set.indicator_of_mem ((mem_closedBox _ _).mpr (sampled_support f (hh n) (hh1 n) hs z hz))]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _) _
  · filter_upwards [] with z
    exact (((hf.tendsto _).comp (tendsto_gridSquare hh ht z)).norm).pow 3
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (K : ℝ → ℝ) (z : ℝ×ℝ) : ℂ :=
  ∫ c : ℝ, B (z.2,c)*C (c,z.1)*(K (z.1+z.2+c):ℂ)

def sampledIntegrand (B C : ℝ×ℝ → ℂ) (h : ℝ) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ) : ℂ :=
  B (gridPoint h z.2,gridPoint h c)*C (gridPoint h c,gridPoint h z.1)*
    (K (gridPoint h z.1+gridPoint h z.2+gridPoint h c):ℂ)

def sampledKernelOutput (B C : ℝ×ℝ → ℂ) (h : ℝ) (K : ℝ → ℝ) (z : ℝ×ℝ) : ℂ :=
  ∫ c : ℝ, sampledIntegrand B C h K z c

lemma sampledKernelOutput_eq_sum (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hB : BoxSupport B M) (K : ℝ → ℝ) (z : ℝ×ℝ) :
    sampledKernelOutput B C h K z = ∑ k : sampleIndices h M,
      (h:ℂ)*B (gridPoint h z.2,h*(k:ℤ))*C (h*(k:ℤ),gridPoint h z.1)*
        (K (gridPoint h z.1+gridPoint h z.2+h*(k:ℤ)):ℂ) := by
  have hs (c : ℝ) (hc : B (gridPoint h z.2,c)*C (c,gridPoint h z.1)*
      (K (gridPoint h z.1+gridPoint h z.2+c):ℂ) ≠ 0) : |c| ≤ M := by
    exact (hB (gridPoint h z.2,c) (fun he => hc (by simp only [he,zero_mul]))).2
  have he := integral_sampled_line (fun c => B (gridPoint h z.2,c)*C (c,gridPoint h z.1)*
      (K (gridPoint h z.1+gridPoint h z.2+c):ℂ)) hh hs
  rw [show sampledKernelOutput B C h K z = _ from he]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.real_smul]
  ring

lemma gridLift_kernelOutput_eq (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) :
    gridLift (sampleIndices h M) h (kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h
      (fun m => h*(m:ℤ)) (fun _ _ => K)) z = sampledKernelOutput B C h K z := by
  rw [gridLift_eq hh,sampledKernelOutput_eq_sum B C hh hB K z]
  split_ifs with hi hj
  · rfl
  · symm
    apply Finset.sum_eq_zero
    intro k _
    have he : B (gridPoint h z.2,h*(k:ℤ)) = 0 := by
      by_contra he
      exact hj ((mem_sampleIndices hh M _).mpr (hB _ he).1)
    simp only [he,mul_zero,zero_mul]
  · symm
    apply Finset.sum_eq_zero
    intro k _
    have he : C (h*(k:ℤ),gridPoint h z.1) = 0 := by
      by_contra he
      exact hi ((mem_sampleIndices hh M _).mpr (hC _ he).2)
    simp only [he,mul_zero,zero_mul]

lemma measurable_sampledIntegrand (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) :
    Measurable (fun q : (ℝ×ℝ)×ℝ => sampledIntegrand B C h K q.1 q.2) := by
  have ha : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.1) := (measurable_gridPoint h).comp (measurable_fst.comp measurable_fst)
  have hb : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.2) := (measurable_gridPoint h).comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.2) := (measurable_gridPoint h).comp measurable_snd
  exact ((hB.comp (hb.prodMk hc)).mul (hC.comp (hc.prodMk ha))).mul
    (Complex.measurable_ofReal.comp (hK.comp ((ha.add hb).add hc)))

lemma measurable_sampledKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) : Measurable (sampledKernelOutput B C h K) :=
  (measurable_sampledIntegrand B C hB hC h K hK).stronglyMeasurable.integral_prod_right'.measurable

lemma sampledIntegrand_support_c (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ)
    (hc : sampledIntegrand B C h K z c ≠ 0) : |c| ≤ M+1 := by
  have hne : B (gridSquare h (z.2,c)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  exact (sampled_support B hh hh1 hB (z.2,c) hne).2

lemma sampledIntegrand_support_z (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ)
    (hc : sampledIntegrand B C h K z c ≠ 0) : z ∈ closedBox (M+1) := by
  apply (mem_closedBox _ _).mpr
  have hneB : B (gridSquare h (z.2,c)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  have hneC : C (gridSquare h (c,z.1)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  exact ⟨(sampled_support C hh hh1 hC (c,z.1) hneC).2,(sampled_support B hh hh1 hB (z.2,c) hneB).1⟩

lemma sampledKernelOutput_support (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (hz : z ∉ closedBox (M+1)) :
    sampledKernelOutput B C h K z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with c
  by_contra hc
  exact hz (sampledIntegrand_support_z B C hh hh1 hB hC K z c hc)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
noncomputable section

def CubicSliceGood (B C : ℝ×ℝ → ℂ) (z : ℝ×ℝ) : Prop :=
  AEStronglyMeasurable (fun c => B (z.2,c)) volume ∧
  AEStronglyMeasurable (fun c => C (c,z.1)) volume ∧
  Integrable (fun c : ℝ => ‖B (z.2,c)‖^3) ∧
  Integrable (fun c : ℝ => ‖C (c,z.1)‖^3)

lemma ae_cubicSliceGood (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    ∀ᵐ z : ℝ×ℝ, CubicSliceGood B C z := by
  have hb := hB.aestronglyMeasurable.prodMk_left
  have hc := hC.aestronglyMeasurable.prodMk_right
  have hbi := (hB.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).prod_right_ae
  have hci := (hC.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).prod_left_ae
  filter_upwards [quasiMeasurePreserving_snd.ae hb,quasiMeasurePreserving_fst.ae hc,
    quasiMeasurePreserving_snd.ae hbi,quasiMeasurePreserving_fst.ae hci] with z hzB hzC hiB hiC
  exact ⟨hzB,hzC,hiB,hiC⟩

lemma hardKernel_shift_support {r R : ℝ} (hr : r ≤ R) (a c : ℝ)
    (hc : c ∉ Set.Icc (-(R+|a|)) (R+|a|)) : hardKernel r R (a+c) = 0 := by
  have hR : R < |a+c| := by
    by_contra hR
    apply hc
    apply abs_le.mp
    have hh : |c| ≤ |a+c|+|a| := by
      calc
        |c| = |(a+c)-a| := by congr 1; ring
        _ ≤ |a+c|+|a| := abs_sub _ _
    linarith [le_of_not_gt hR]
  simp only [hardKernel,hr.trans_lt hR,hR,ite_true,sub_self,zero_div]

lemma CubicSliceGood.integrable_hard {B C : ℝ×ℝ → ℂ} {z : ℝ×ℝ} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    Integrable (fun c : ℝ => B (z.2,c)*C (c,z.1)*(hardKernel r R (z.1+z.2+c):ℂ)) := by
  apply integrable_product_bounded_kernel _ _ _ hz.1 hz.2.1
    ((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)) hz.2.2.1 hz.2.2.2
    (Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)) measurableSet_Icc isCompact_Icc.measure_ne_top
    (show 0 ≤ 1/r by positivity) (fun c => abs_hardKernel_le hr hR _)
  exact hardKernel_shift_support hR (z.1+z.2)

lemma tendsto_cyclicKernelOutput_of_cubic_dom (B C : ℝ×ℝ → ℂ) (F G : ℕ → ℝ×ℝ → ℂ)
    (hF : ∀ n, Continuous (F n)) (hG : ∀ n, Continuous (G n))
    {D E : ℝ×ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hb : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖F n z‖^3 ≤ D z) ∧ Tendsto (fun n => F n z) atTop (𝓝 (B z)))
    (hc : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖G n z‖^3 ≤ E z) ∧ Tendsto (fun n => G n z) atTop (𝓝 (C z))) :
    ∀ᵐ z : ℝ×ℝ, ∀ r R : ℝ, 0 < r → r ≤ R →
      Tendsto (fun n => cyclicKernelOutput (F n) (G n) (hardKernel r R) z) atTop
        (𝓝 (cyclicKernelOutput B C (hardKernel r R) z)) := by
  have hb' := ae_ae_of_ae_prod hb
  have hc' := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hc)
  filter_upwards [quasiMeasurePreserving_snd.ae hb',quasiMeasurePreserving_fst.ae hc',
    quasiMeasurePreserving_snd.ae hD.prod_right_ae,quasiMeasurePreserving_fst.ae hE.prod_left_ae]
    with z hzb hzc hzD hzE
  intro r R hr hR
  apply tendsto_integral_product_bounded_kernel _ _ _ _ _
    (s := Set.Icc (-(R+|z.1+z.2|)) (R+|z.1+z.2|)) (L := 1/r)
    (fun n => ((hF n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun n => ((hG n).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    ((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)) hzD hzE
  · filter_upwards [hzb,hzc] with c hb hc
    exact fun n => ⟨hb.1 n,hc.1 n⟩
  · filter_upwards [hzb,hzc] with c hb hc
    exact ⟨hb.2,hc.2⟩
  · exact measurableSet_Icc
  · exact isCompact_Icc.measure_ne_top
  · exact show 0 ≤ 1/r by positivity
  · exact fun c => abs_hardKernel_le hr hR _
  · exact hardKernel_shift_support hR (z.1+z.2)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma continuousAt_threshold (u v : ℝ) (hu : u ≠ v) :
    ContinuousAt (fun r : ℝ => if r < v then (1:ℝ) else 0) u := by
  rcases lt_or_gt_of_ne hu with h|h
  · have he : ∀ᶠ r in 𝓝 u, r < v := eventually_lt_nhds h
    apply (show ContinuousAt (fun _ : ℝ => (1:ℝ)) u from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [hr,ite_true]
  · have he : ∀ᶠ r in 𝓝 u, v < r := eventually_gt_nhds h
    apply (show ContinuousAt (fun _ : ℝ => (0:ℝ)) u from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [not_lt.mpr hr.le,ite_false]

lemma continuousAt_hardKernel_endpoints (r R t : ℝ) (hr : r ≠ |t|) (hR : R ≠ |t|) :
    ContinuousAt (fun p : ℝ×ℝ => hardKernel p.1 p.2 t) (r,R) := by
  have h1 : ContinuousAt (fun p : ℝ×ℝ => if p.1 < |t| then (1:ℝ) else 0) (r,R) := by
    simpa only [Function.comp_def] using (continuousAt_threshold r |t| hr).comp (continuousAt_fst (p := (r,R)))
  have h2 : ContinuousAt (fun p : ℝ×ℝ => if p.2 < |t| then (1:ℝ) else 0) (r,R) := by
    simpa only [Function.comp_def] using (continuousAt_threshold R |t| hR).comp (continuousAt_snd (p := (r,R)))
  exact (h1.sub h2).div_const t

lemma ae_continuousAt_hardKernel_endpoints (r R a : ℝ) :
    ∀ᵐ c : ℝ, ContinuousAt (fun p : ℝ×ℝ => hardKernel p.1 p.2 (a+c)) (r,R) := by
  have hne (x : ℝ) : ∀ᵐ c : ℝ, c ≠ x := by simp [ae_iff]
  filter_upwards [hne (r-a),hne (-r-a),hne (R-a),hne (-R-a)] with c h1 h2 h3 h4
  apply continuousAt_hardKernel_endpoints
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he.symm with he|he
    · apply h1; linarith
    · apply h2; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he.symm with he|he
    · apply h3; linarith
    · apply h4; linarith

lemma continuousAt_cyclicHard {B C : ℝ×ℝ → ℂ} {z : ℝ×ℝ} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ContinuousAt (fun p : ℝ×ℝ => cyclicKernelOutput B C (hardKernel p.1 p.2) z) (r,R) := by
  let s := Set.Icc (-(R+1+|z.1+z.2|)) (R+1+|z.1+z.2|)
  let L := 1/(r/2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let D (c : ℝ) := ‖B (z.2,c)‖^3
  let E (c : ℝ) := ‖C (c,z.1)‖^3
  have hdom : Integrable (s.indicator (fun c => (D c+E c+2)*L)) :=
    IntegrableOn.integrable_indicator
      (((hz.2.2.1.integrableOn.add hz.2.2.2.integrableOn).add
        (integrableOn_const (C := (2:ℝ)) isCompact_Icc.measure_ne_top)).mul_const L) measurableSet_Icc
  have hnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), r/2 < p.1 ∧ p.1 < p.2 ∧ p.2 < R+1 := by
    have h1 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), r/2 < p.1 :=
      (continuous_fst.tendsto (r,R)) (eventually_gt_nhds (show r/2 < r by linarith))
    have h2 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), 0 < p.2-p.1 :=
      ((continuous_snd.sub continuous_fst).tendsto (r,R)) (eventually_gt_nhds (show 0 < R-r by linarith))
    have h3 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), p.2 < R+1 :=
      (continuous_snd.tendsto (r,R)) (eventually_lt_nhds (show R < R+1 by linarith))
    filter_upwards [h1,h2,h3] with p hp1 hp2 hp3
    exact ⟨hp1,by linarith,hp3⟩

  apply tendsto_integral_filter_of_dominated_convergence (s.indicator (fun c => (D c+E c+2)*L))
  · exact Eventually.of_forall (fun p => (hz.1.mul hz.2.1).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)).aestronglyMeasurable)))
  · filter_upwards [hnear] with p hp
    filter_upwards [] with c
    by_cases hc : c ∈ s
    · rw [Set.indicator_of_mem hc]
      exact norm_product_kernel_le (fun c => B (z.2,c)) (fun c => C (c,z.1))
        (fun c => hardKernel p.1 p.2 (z.1+z.2+c)) (D := D) (E := E) hL (c := c) le_rfl le_rfl
        ((abs_hardKernel_le (by linarith [hp.1]) hp.2.1.le _).trans
          (one_div_le_one_div_of_le (by positivity) hp.1.le))
    · have he : hardKernel p.1 p.2 (z.1+z.2+c) = 0 := by
        apply hardKernel_shift_support hp.2.1.le
        intro hh
        apply hc
        exact ⟨by linarith [hh.1,hp.2.2],by linarith [hh.2,hp.2.2]⟩
      simp only [he,Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem hc,le_refl]
  · exact hdom
  · filter_upwards [ae_continuousAt_hardKernel_endpoints r R (z.1+z.2)] with c hc
    exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hc.tendsto)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

abbrev RatEndpoints := {p : ℚ×ℚ // 0 < p.1 ∧ p.1 < p.2}
instance : Inhabited RatEndpoints := ⟨⟨(1,2),by norm_num⟩⟩

def RatEndpoints.toEndpoints (q : RatEndpoints) : Endpoints where
  lower := q.1.1
  upper := q.1.2
  lower_pos := by exact_mod_cast q.2.1
  lower_lt_upper := by exact_mod_cast q.2.2

def cyclicMax (B C : Plane → ℂ) (z : Plane) : ℝ≥0∞ :=
  ⨆ q : RatEndpoints, ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z‖

lemma cyclicHard_le_cyclicMax {B C : Plane → ℂ} {z : Plane} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel r R) z‖ ≤ cyclicMax B C z := by
  obtain ⟨u,_,hu,htu⟩ := Real.exists_seq_rat_strictMono_tendsto r
  obtain ⟨v,_,hv,htv⟩ := Real.exists_seq_rat_strictAnti_tendsto R
  have ht := (continuousAt_cyclicHard hz hr hR).tendsto.comp (htu.prodMk_nhds htv)
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
  filter_upwards [htu (eventually_gt_nhds hr)] with n hn
  have hq : 0 < u n ∧ u n < v n := by
    constructor
    · exact_mod_cast (show (0:ℝ) < (u n:ℝ) from hn)
    · exact_mod_cast ((hu n).trans (hR.trans (hv n)))
  exact le_iSup (fun q : RatEndpoints => ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z‖)
    ⟨(u n,v n),hq⟩

lemma cyclicMax_eq_iSup {B C : Plane → ℂ} {z : Plane} (hz : CubicSliceGood B C z) :
    cyclicMax B C z = ⨆ E : Endpoints, ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel E.lower E.upper) z‖ := by
  apply le_antisymm
  · apply iSup_le
    intro q
    exact le_iSup (fun E : Endpoints => ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel E.lower E.upper) z‖) q.toEndpoints
  · apply iSup_le
    intro E
    exact cyclicHard_le_cyclicMax hz E.lower_pos E.lower_lt_upper

def RatEndpoints.sequence (n : ℕ) : RatEndpoints := (Encodable.decode (α := RatEndpoints) n).getD default
lemma RatEndpoints.sequence_surjective : Function.Surjective RatEndpoints.sequence := by
  intro q
  exact ⟨Encodable.encode q,by simp [RatEndpoints.sequence,Encodable.encodek]⟩
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma norm_sampledIntegrand_le (B C : ℝ×ℝ → ℂ) {CB CC L : ℝ}
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) (K : ℝ → ℝ)
    (hk : ∀ t, |K t| ≤ L) (h : ℝ) (z : ℝ×ℝ) (c : ℝ) :
    ‖sampledIntegrand B C h K z c‖ ≤ CB*CC*L := by
  unfold sampledIntegrand
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul (hb _) (hc _) (norm_nonneg _) ((norm_nonneg (B 0)).trans (hb 0)))
    (hk _) (abs_nonneg _) (mul_nonneg ((norm_nonneg (B 0)).trans (hb 0)) ((norm_nonneg (C 0)).trans (hc 0)))

lemma sampledIntegrand_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ) (hk : ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledIntegrand B C (h n) K z c) atTop
      (𝓝 (B (z.2,c)*C (c,z.1)*(K (z.1+z.2+c):ℂ))) := by
  have ha := tendsto_gridPoint hh ht z.1
  have hb := tendsto_gridPoint hh ht z.2
  have hc := tendsto_gridPoint hh ht c
  exact (((hB.tendsto _).comp (hb.prodMk_nhds hc)).mul
    ((hC.tendsto _).comp (hc.prodMk_nhds ha))).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hk.tendsto.comp ((ha.add hb).add hc)))

lemma sampledKernelOutput_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (hK : Measurable K) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ)
    (hcont : ∀ᵐ c : ℝ, ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledKernelOutput B C (h n) K z) atTop (𝓝 (cyclicKernelOutput B C K z)) := by
  let b : ℝ → ℝ := (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact ((measurable_sampledIntegrand B C hB.measurable hC.measurable (h n) K hK).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  · intro n
    filter_upwards [] with c
    by_cases he : sampledIntegrand B C (h n) K z c = 0
    · rw [he,norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) _
    · have hmem : c ∈ Set.Icc (-(M+1)) (M+1) := abs_le.mp (sampledIntegrand_support_c B C (hh n) (hh1 n) hs K z c he)
      dsimp only [b]
      rw [Set.indicator_of_mem hmem]
      exact norm_sampledIntegrand_le B C hb hc K hk _ _ _
  · filter_upwards [hcont] with c hct
    exact sampledIntegrand_tendsto B C hB hC hh ht K z c hct

lemma ae_continuousAt_hardKernel (r R a : ℝ) : ∀ᵐ c : ℝ, ContinuousAt (hardKernel r R) (a+c) := by
  have hne (x : ℝ) : ∀ᵐ c : ℝ, c ≠ x := by simp [ae_iff]
  filter_upwards [hne (-a),hne (r-a),hne (-r-a),hne (R-a),hne (-R-a)] with c h0 h1 h2 h3 h4
  apply continuousAt_hardKernel
  · intro he; apply h0; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · apply h1; linarith
    · apply h2; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · apply h3; linarith
    · apply h4; linarith
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

def complexMoment (z : ℂ) : ℝ := ‖z‖*Real.sqrt ‖z‖
lemma complexMoment_nonneg (z : ℂ) : 0 ≤ complexMoment z := by unfold complexMoment; positivity
@[simp] lemma complexMoment_zero : complexMoment 0 = 0 := by simp [complexMoment]
lemma continuous_complexMoment : Continuous complexMoment := continuous_norm.mul (Real.continuous_sqrt.comp continuous_norm)
lemma complexMoment_le {z : ℂ} {b : ℝ} (hz : ‖z‖ ≤ b) : complexMoment z ≤ b*Real.sqrt b :=
  mul_le_mul hz (Real.sqrt_le_sqrt hz) (Real.sqrt_nonneg _) ((norm_nonneg _).trans hz)

def finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k => complexMoment (f k))
lemma finiteMoment_eq {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ∃ k, finiteMoment f = complexMoment (f k) := by
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => complexMoment (f k))
  exact ⟨k,hk⟩
lemma le_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) (k : κ) :
    complexMoment (f k) ≤ finiteMoment f  := by
  exact Finset.le_sup' (fun k => complexMoment (f k)) (Finset.mem_univ k)
lemma finiteMoment_nonneg {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    0 ≤ finiteMoment f := by
  obtain ⟨k,hk⟩ := finiteMoment_eq f
  rw [hk]
  exact complexMoment_nonneg _
lemma finiteMoment_le {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) {b : ℝ}
    (hb : ∀ k, ‖f k‖ ≤ b) : finiteMoment f ≤ b*Real.sqrt b :=
  Finset.sup'_le _ _ (fun k _ => complexMoment_le (hb k))
@[simp] lemma finiteMoment_zero {κ : Type uκ} [Fintype κ] [Nonempty κ] : finiteMoment (fun _ : κ => (0:ℂ)) = 0 := by
  simp [finiteMoment]
lemma continuous_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] : Continuous (finiteMoment (κ := κ)) := by
  unfold finiteMoment
  exact Continuous.finset_sup'_apply _ (fun k _ => continuous_complexMoment.comp (continuous_apply k))
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

def outputBound (M CB CC L : ℝ) : ℝ := ∫ c : ℝ,
  (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L) c

lemma outputBound_nonneg (M : ℝ) {CB CC L : ℝ} (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L) :
    0 ≤ outputBound M CB CC L :=
  integral_nonneg (fun c => Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) c)

lemma sampledKernelOutput_bound (B C : ℝ×ℝ → ℂ) {M CB CC L h : ℝ}
    (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ → ℝ) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ) :
    ‖sampledKernelOutput B C h K z‖ ≤ outputBound M CB CC L := by
  apply norm_integral_le_of_norm_le
    ((integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc)
  filter_upwards [] with c
  by_cases he : sampledIntegrand B C h K z c = 0
  · rw [he,norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) c
  · rw [Set.indicator_of_mem (show c ∈ Set.Icc (-(M+1)) (M+1) from
      abs_le.mp (sampledIntegrand_support_c B C hh hh1 hs K z c he))]
    exact norm_sampledIntegrand_le B C hb hc K hk _ _ _

lemma sampled_moment_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ)
    (hK : ∀ k, Measurable (K k)) (hk : ∀ k t, |K k t| ≤ L)
    (hcont : ∀ k (z : ℝ×ℝ), ∀ᵐ c : ℝ, ContinuousAt (K k) (z.1+z.2+c)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C (h n) (K k) z)) atTop
      (𝓝 (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (K k) z))) := by
  let T := outputBound M CB CC L
  have hT : 0 ≤ T := outputBound_nonneg M hCB hCC hL
  let b : ℝ×ℝ → ℝ := (closedBox (M+1)).indicator (fun _ => T*Real.sqrt T)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact (continuous_finiteMoment.measurable.comp (Measurable.of_eval
      (fun k => measurable_sampledKernelOutput B C hB.measurable hC.measurable (h n) (K k) (hK k)))).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := closedBox (M+1)) (C := T*Real.sqrt T)
      (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)
  · intro n
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (finiteMoment_nonneg _)]
    by_cases hz : z ∈ closedBox (M+1)
    · dsimp only [b]
      rw [Set.indicator_of_mem hz]
      exact finiteMoment_le _ (fun k => sampledKernelOutput_bound B C hsB hCB hCC hL hb hc (hh n) (hh1 n) (K k) (hk k) z)
    · have he : (fun k => sampledKernelOutput B C (h n) (K k) z) = fun _ : κ => (0:ℂ) :=
        funext (fun k => sampledKernelOutput_support B C (hh n) (hh1 n) hsB hsC (K k) z hz)
      rw [he,finiteMoment_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hT (Real.sqrt_nonneg _)) z
  · filter_upwards [] with z
    apply continuous_finiteMoment.continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr (fun k => sampledKernelOutput_tendsto B C hB hC hsB hCB hCC hL hb hc
      hh hh1 ht (K k) (hK k) (hk k) z (hcont k z))
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def dualRoot (z : ℂ) : ℂ := (Real.sqrt ‖z‖:ℂ)*star z/(‖z‖:ℂ)

lemma dualRoot_mul (z : ℂ) : dualRoot z*z = (‖z‖*Real.sqrt ‖z‖:ℝ) := by
  by_cases hz : z = 0
  · subst z
    simp [dualRoot]
  have hn : (‖z‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  unfold dualRoot
  rw [div_mul_eq_mul_div, mul_assoc, RCLike.star_def,Complex.conj_mul']
  push_cast
  field_simp

lemma norm_dualRoot (z : ℂ) : ‖dualRoot z‖ = Real.sqrt ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp [dualRoot]
  unfold dualRoot
  rw [norm_div,norm_mul,norm_star,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hz)]

lemma cube_norm_dualRoot (z : ℂ) : ‖dualRoot z‖^3 = ‖z‖*Real.sqrt ‖z‖ := by
  rw [norm_dualRoot,pow_succ,Real.sq_sqrt (norm_nonneg _)]

lemma finite_cubic_dual {ι : Type uι} [Fintype ι] (u : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {K b : ℝ} (hK : 0 < K)
    (H : ∀ f : ι → ℂ, ‖∑ i, (w i:ℂ)*f i*u i‖ ≤ K*((∑ i, w i*‖f i‖^3)+b)) :
    (∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖)) ≤ 4*K*(K+1)*b := by
  let d : ℝ := 1/(2*(K+1))
  let m : ℝ := ∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖)
  have hd : 0 < d := by dsimp [d]; positivity
  have hm : 0 ≤ m := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by positivity))
  have hd1 : d ≤ 1 := by
    dsimp [d]
    rw [div_le_one (by positivity)]
    linarith
  have hk1 : K*d ≤ 1/2 := by
    dsimp [d]
    rw [← mul_div_assoc, mul_one,div_le_iff₀ (by positivity)]
    linarith
  have hk2 : K*d^3 ≤ d/2 := by
    have ha := mul_le_mul_of_nonneg_right hk1 (sq_nonneg d)
    nlinarith [mul_le_mul_of_nonneg_left hd1 hd.le]
  let f : ι → ℂ := fun i => (d:ℂ)*dualRoot (u i)
  have hprod (i : ι) : (w i:ℂ)*f i*u i = (d*(w i*(‖u i‖*Real.sqrt ‖u i‖)):ℝ) := by
    dsimp [f]
    rw [mul_assoc,mul_assoc,dualRoot_mul]
    push_cast
    ring
  have hnorm (i : ι) : w i*‖f i‖^3 = d^3*(w i*(‖u i‖*Real.sqrt ‖u i‖)) := by
    dsimp [f]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hd.le,mul_pow,cube_norm_dualRoot]
    ring
  have hp : (∑ i, (w i:ℂ)*f i*u i) = (d*m:ℝ) := by
    simp_rw [hprod]
    rw [← Complex.ofReal_sum,← Finset.mul_sum]
  have ha := H f
  rw [hp,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hd.le hm)] at ha
  simp_rw [hnorm] at ha
  rw [← Finset.mul_sum] at ha
  change d*m ≤ K*(d^3*m+b) at ha
  have hb : m ≤ (2*K/d)*b := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_right hk2 hm]
  apply hb.trans_eq
  dsimp [d]
  field_simp
  ring
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def matrixCubic {ι : Type uι} [Fintype ι] (B : Matrix ι ι ℂ) (h : ℝ) : ℝ := ∑ i, ∑ j, h^2*‖B i j‖^3

def momentConstant : ℝ := 4*hardPairingConstant*(hardPairingConstant+1)
lemma momentConstant_pos : 0 < momentConstant := by
  unfold momentConstant
  have hp := hardPairingConstant_pos
  positivity

lemma hardOutput_moment (D : Finset ℤ) (B C : Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    (∑ i, ∑ j, h^2*complexMoment (kernelOutput B C h (fun m => h*(m:ℤ))
      (fun i j => hardKernel (r i j) (R i j)) i j)) ≤
      momentConstant*(matrixCubic B h+matrixCubic C h) := by
  classical
  let u : D×D → ℂ := fun p => kernelOutput B C h (fun m => h*(m:ℤ))
    (fun i j => hardKernel (r i j) (R i j)) p.1 p.2
  have HH (f : D×D → ℂ) : ‖∑ p, (h^2:ℝ)*f p*u p‖ ≤ hardPairingConstant*
      ((∑ p, h^2*‖f p‖^3)+(matrixCubic B h+matrixCubic C h)) := by
    let A : Three → Matrix D D ℂ := ![fun i j => f (i,j),B,C]
    have ha := hardPairing_le D A hh r R hr hb
    have hA0 : A 0 = fun i j => f (i,j) := rfl
    have hA1 : A 1 = B := rfl
    have hA2 : A 2 = C := rfl
    simpa only [kernelPairing,arrayCubic,Fin.sum_univ_three,hA0,hA1,hA2,
      Fintype.sum_prod_type,matrixCubic,u,add_assoc] using ha
  have hh' := finite_cubic_dual u (fun _ => h^2) (fun _ => sq_nonneg h) hardPairingConstant_pos HH
  simpa only [Fintype.sum_prod_type,u,complexMoment,momentConstant] using hh'

lemma finiteHardOutput_moment (D : Finset ℤ) (B C : Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ)
    (hr : ∀ k, h ≤ r k) (hb : ∀ k, r k ≤ R k) :
    (∑ i, ∑ j, h^2*finiteMoment (fun k => kernelOutput B C h (fun m => h*(m:ℤ))
      (fun _ _ => hardKernel (r k) (R k)) i j)) ≤
      momentConstant*(matrixCubic B h+matrixCubic C h) := by
  classical
  let U (i j : D) (k : κ) := kernelOutput B C h (fun m => h*(m:ℤ))
    (fun _ _ => hardKernel (r k) (R k)) i j
  choose s hs using (fun i j : D => finiteMoment_eq (U i j))
  have ha := hardOutput_moment D B C hh (fun i j => r (s i j)) (fun i j => R (s i j))
    (fun i j => hr (s i j)) (fun i j => hb (s i j))
  have he (i j : D) : finiteMoment (U i j) = complexMoment (kernelOutput B C h (fun m => h*(m:ℤ))
      (fun i j => hardKernel (r (s i j)) (R (s i j))) i j) := hs i j
  simp_rw [← he] at ha
  exact ha
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MeasureTheory Filter MatrixEnergy
open scoped Topology BigOperators
noncomputable section

lemma gridLift_pi (D : Finset ℤ) {h : ℝ} (hh : 0 < h) {κ : Type uκ}
    (U : κ → D → D → ℂ) (z : ℝ×ℝ) :
    gridLift D h (fun i j k => U k i j) z = fun k => gridLift D h (U k) z := by
  funext k
  simp only [gridLift_eq hh]
  split_ifs <;> rfl

lemma sampled_moment_integral_eq (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C h (K k) z)) =
      ∑ i, ∑ j, h^2*finiteMoment (fun k => kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h
        (fun m => h*(m:ℤ)) (fun _ _ => K k) i j) := by
  have he (z : ℝ×ℝ) : finiteMoment (fun k => sampledKernelOutput B C h (K k) z) =
      gridLift (sampleIndices h M) h (fun i j => finiteMoment (fun k =>
        kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h (fun m => h*(m:ℤ))
          (fun _ _ => K k) i j)) z := by
    simp_rw [← gridLift_kernelOutput_eq B C hh hsB hsC]
    rw [← gridLift_pi _ hh,gridLift_comp hh _ finiteMoment finiteMoment_zero]
  simp_rw [he]
  rw [integral_gridLift _ _ _ hh.le]
  rfl

lemma sampled_cubic_integral_eq (B : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) :
    (∫ z : ℝ×ℝ, ‖B (gridSquare h z)‖^3) = matrixCubic (sampledMatrix B h M) h := by
  simp_rw [← gridLift_sampled B hh hsB,gridLift_comp hh _ (fun w : ℂ => ‖w‖^3) (by simp)]
  rw [integral_gridLift _ _ _ hh.le]
  rfl

lemma sampled_moment_le (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ)
    (hr : ∀ k, h ≤ r k) (hb : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C h (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B (gridSquare h z)‖^3)+(∫ z : ℝ×ℝ, ‖C (gridSquare h z)‖^3)) := by
  rw [sampled_moment_integral_eq B C hh hsB hsC,sampled_cubic_integral_eq B hh hsB,sampled_cubic_integral_eq C hh hsC]
  exact finiteHardOutput_moment (sampleIndices h M) (sampledMatrix B h M) (sampledMatrix C h M) hh r R hr hb
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MeasureTheory Filter MatrixEnergy
open scoped Topology BigOperators
noncomputable section

lemma continuum_moment_le_box (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3)) := by
  classical
  let δ : ℝ := min 1 (Finset.univ.inf' Finset.univ_nonempty r)
  have hδ : 0 < δ := lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr (fun k _ => hr k))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδr (k : κ) : δ ≤ r k := (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ k))
  let h : ℕ → ℝ := fun n => δ/((n:ℝ)+1)
  have hh (n : ℕ) : 0 < h n := div_pos hδ (by positivity)
  have hhδ (n : ℕ) : h n ≤ δ := (div_le_self hδ.le (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hh1 (n : ℕ) : h n ≤ 1 := (hhδ n).trans hδ1
  have ht : Tendsto h atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using (tendsto_const_nhds (x := δ)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs := sampled_moment_tendsto B C hB hC hsB hsC hCB hCC (show 0 ≤ 1/δ by positivity) hb hc
    hh hh1 ht (fun k => hardKernel (r k) (R k)) (fun k => measurable_hardKernel _ _)
    (fun k t => (abs_hardKernel_le (hr k) (hR k) t).trans (one_div_le_one_div_of_le hδ (hδr k)))
    (fun k z => ae_continuousAt_hardKernel (r k) (R k) (z.1+z.2))
  have hsB' := sampled_cubic_tendsto B hB hsB hCB hb hh hh1 ht
  have hsC' := sampled_cubic_tendsto C hC hsC hCC hc hh hh1 ht
  exact le_of_tendsto_of_tendsto hs (tendsto_const_nhds.mul (hsB'.add hsC'))
    (Filter.Eventually.of_forall (fun n => sampled_moment_le B C (hh n) hsB hsC r R
      (fun k => (hhδ n).trans (hδr k)) hR))

lemma continuum_moment_le_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3)) := by
  obtain ⟨MB,hMB,hb⟩ := compactSupport_box B hsB
  obtain ⟨MC,hMC,hc⟩ := compactSupport_box C hsC
  obtain ⟨CB,hCB⟩ := hB.bounded_above_of_compact_support hsB
  obtain ⟨CC,hCC⟩ := hC.bounded_above_of_compact_support hsC
  have hCB0 : 0 ≤ CB := (norm_nonneg (B 0)).trans (hCB 0)
  have hCC0 : 0 ≤ CC := (norm_nonneg (C 0)).trans (hCC 0)
  exact continuum_moment_le_box B C hB hC
    (M := max MB MC) (fun z hz => ⟨(hb z hz).1.trans (le_max_left _ _),(hb z hz).2.trans (le_max_left _ _)⟩)
    (fun z hz => ⟨(hc z hz).1.trans (le_max_right _ _),(hc z hz).2.trans (le_max_right _ _)⟩)
    hCB0 hCC0 hCB hCC r R hr hR
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (K : ℝ → ℝ) (hK : Measurable K) : Measurable (cyclicKernelOutput B C K) := by
  have hm : Measurable (fun q : (ℝ×ℝ)×ℝ => B (q.1.2,q.2)*C (q.2,q.1.1)*(K (q.1.1+q.1.2+q.2):ℂ)) := by
    apply Measurable.mul
    · exact (hB.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        (hC.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    · exact Complex.measurable_ofReal.comp (hK.comp
        (((measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst)).add measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma cyclicKernelOutput_support (B C : ℝ×ℝ → ℂ) {M : ℝ}
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (hz : z ∉ closedBox M) :
    cyclicKernelOutput B C K z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with c
  by_cases hb : B (z.2,c) = 0
  · simp only [hb,zero_mul,Pi.zero_apply]
  · have hc : C (c,z.1) = 0 := by
      by_contra hc
      exact hz ((mem_closedBox _ _).mpr ⟨(hC _ hc).2,(hB _ hb).1⟩)
    simp only [hc,mul_zero,zero_mul,Pi.zero_apply]

lemma cyclicKernelOutput_bound (B C : ℝ×ℝ → ℂ) {M CB CC L : ℝ}
    (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (_hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    (K : ℝ → ℝ) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ) :
    ‖cyclicKernelOutput B C K z‖ ≤ outputBound M CB CC L := by
  apply norm_integral_le_of_norm_le
    ((integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc)
  filter_upwards [] with c
  by_cases hmem : c ∈ Set.Icc (-(M+1)) (M+1)
  · rw [Set.indicator_of_mem hmem,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul (hb _) (hc _) (norm_nonneg _) hCB) (hk _) (abs_nonneg _)
      (mul_nonneg hCB hCC)
  · have he : B (z.2,c) = 0 := by
      by_contra he
      apply hmem
      exact abs_le.mp ((hs _ he).2.trans (by linarith))
    simp only [he,zero_mul,norm_zero,Set.indicator_of_notMem hmem,le_refl]

lemma integrable_cyclic_moment_box (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    {M CB CC L : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ)
    (hK : ∀ k, Measurable (K k)) (hk : ∀ k t, |K k t| ≤ L) :
    Integrable (fun z : ℝ×ℝ => finiteMoment (fun k => cyclicKernelOutput B C (K k) z)) := by
  let T := outputBound M CB CC L
  have hT : 0 ≤ T := outputBound_nonneg M hCB hCC hL
  apply ((integrableOn_const (μ := volume) (s := closedBox M) (C := T*Real.sqrt T)
    (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)).mono'
  · exact (continuous_finiteMoment.measurable.comp (Measurable.of_eval
      (fun k => measurable_cyclicKernelOutput B C hB hC (K k) (hK k)))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (finiteMoment_nonneg _)]
    by_cases hz : z ∈ closedBox M
    · rw [Set.indicator_of_mem hz]
      exact finiteMoment_le _ (fun k => cyclicKernelOutput_bound B C hsB hCB hCC hL hb hc (K k) (hk k) z)
    · have he : (fun k => cyclicKernelOutput B C (K k) z) = fun _ : κ => (0:ℂ) :=
        funext (fun k => cyclicKernelOutput_support B C hsB hsC (K k) z hz)
      rw [he,finiteMoment_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hT (Real.sqrt_nonneg _)) z
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma integrable_cyclic_moment_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    Integrable (fun z : ℝ×ℝ => finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) := by
  classical
  obtain ⟨MB,_,hb⟩ := compactSupport_box B hsB
  obtain ⟨MC,_,hc⟩ := compactSupport_box C hsC
  obtain ⟨CB,hCB⟩ := hB.bounded_above_of_compact_support hsB
  obtain ⟨CC,hCC⟩ := hC.bounded_above_of_compact_support hsC
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty r
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun k _ => hr k)
  have hδr (k : κ) : δ ≤ r k := Finset.inf'_le _ (Finset.mem_univ k)
  apply integrable_cyclic_moment_box B C hB.measurable hC.measurable
    (M := max MB MC) (fun z hz => ⟨(hb z hz).1.trans (le_max_left _ _),(hb z hz).2.trans (le_max_left _ _)⟩)
    (fun z hz => ⟨(hc z hz).1.trans (le_max_right _ _),(hc z hz).2.trans (le_max_right _ _)⟩)
    ((norm_nonneg (B 0)).trans (hCB 0)) ((norm_nonneg (C 0)).trans (hCC 0))
    (show 0 ≤ 1/δ by positivity) hCB hCC (fun k => hardKernel (r k) (R k))
    (fun k => measurable_hardKernel _ _)
  exact fun k t => (abs_hardKernel_le (hr k) (hR k) t).trans (one_div_le_one_div_of_le hδ (hδr k))

lemma lintegral_cyclic_moment_le_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z))) ≤
      ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cyclic_moment_compact B C hB hC hsB hsC r R hr hR)
    (Eventually.of_forall (fun z => finiteMoment_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (continuum_moment_le_compact B C hB hC hsB hsC r R hr hR)
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
noncomputable section

lemma lintegral_enorm_cube {α : Type uα} [MeasurableSpace α] (f : α → ℂ) (μ : Measure α)
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ^3 ∂μ) = eLpNorm f 3 μ ^ (3:ℕ) := by
  simpa only [ENNReal.rpow_ofNat,NNReal.coe_ofNat,ENNReal.coe_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := (3:ℝ≥0)) (by norm_num)).symm

lemma norm_cube_le_four_sub (u v : ℂ) : ‖u‖^3 ≤ 4*(‖v‖^3+‖u-v‖^3) := by
  have ht : ‖u‖ ≤ ‖v‖+‖u-v‖ := by
    calc
      ‖u‖ = ‖(u-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ ‖u-v‖+‖v‖ := norm_add_le _ _
      _ = ‖v‖+‖u-v‖ := add_comm _ _
  have hp := pow_le_pow_left₀ (norm_nonneg u) ht 3
  have hn := mul_nonneg (sq_nonneg (‖v‖-‖u-v‖)) (add_nonneg (norm_nonneg v) (norm_nonneg (u-v)))
  nlinarith

lemma tendsto_of_enorm_cube {α : Type uα} {l : Filter α} {f : α → ℂ} {z : ℂ}
    (h : Tendsto (fun n => ‖f n-z‖ₑ^3) l (𝓝 0)) : Tendsto f l (𝓝 z) := by
  have he : Tendsto (fun n => ‖f n-z‖ₑ) l (𝓝 0) := by
    have ht := ((ENNReal.continuous_rpow_const (y := (1:ℝ)/3)).tendsto (0:ℝ≥0∞)).comp h
    have hp (x : ℝ≥0∞) : (x^(3:ℕ))^((1:ℝ)/3) = x := by
      rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
      norm_num
    simpa only [Function.comp_def,hp,ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1:ℝ)/3)] using ht
  have hr := (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).tendsto.comp he
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,ENNReal.toReal_zero,enorm_eq_nnnorm,ENNReal.coe_toReal,coe_nnnorm] using hr

lemma exists_cubic_approximation (f : ℝ×ℝ → ℂ) (hf : MemLp f 3 volume) :
    ∃ g : ℕ → ℝ×ℝ → ℂ, (∀ n, Continuous (g n) ∧ HasCompactSupport (g n) ∧ MemLp (g n) 3 volume) ∧
      ∃ D : ℝ×ℝ → ℝ, Integrable D ∧ (∀ z, 0 ≤ D z) ∧
        (∀ᵐ z : ℝ×ℝ, (∀ n, ‖g n z‖^3 ≤ D z) ∧ Tendsto (fun n => g n z) atTop (𝓝 (f z))) := by
  have hex (n : ℕ) : ∃ g : ℝ×ℝ → ℂ, HasCompactSupport g ∧
      eLpNorm (f-g) 3 volume ≤ (2⁻¹:ℝ≥0∞)^n ∧ Continuous g ∧ MemLp g 3 volume :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) (by simp)
  choose g hgs hge hgc hgm using hex
  let S (z : ℝ×ℝ) : ℝ≥0∞ := ∑' n, ‖f z-g n z‖ₑ^3
  have hm (n : ℕ) : AEMeasurable (fun z => ‖f z-g n z‖ₑ^3) volume :=
    ((hf.aestronglyMeasurable.sub (hgc n).aestronglyMeasurable).enorm).pow_const 3
  have hS : AEMeasurable S volume := AEMeasurable.tsum hm
  have hSint : (∫⁻ z, S z) < ⊤ := by
    rw [show (∫⁻ z, S z) = ∑' n, ∫⁻ z, ‖f z-g n z‖ₑ^3 from lintegral_tsum hm]
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_))
      ((tsum_geometric_lt_top).mpr (show ((2⁻¹:ℝ≥0∞)^3) < 1 by
        apply pow_lt_one₀ zero_le _ (by norm_num)
        exact ENNReal.inv_lt_one.mpr (show (1:ℝ≥0∞) < 2 by norm_num)))
    rw [lintegral_enorm_cube (fun point => f point - g n point) _
      (hf.aestronglyMeasurable.sub (hgc n).aestronglyMeasurable)]
    exact (ENNReal.pow_le_pow_left (hge n)).trans_eq (by rw [← pow_mul,← pow_mul,Nat.mul_comm])
  have hSfinite : ∀ᵐ z, S z < ⊤ := ae_lt_top' hS hSint.ne
  let D (z : ℝ×ℝ) : ℝ := 4*(‖f z‖^3+(S z).toReal)
  refine ⟨g,fun n => ⟨hgc n,hgs n,hgm n⟩,D,?_,?_,?_⟩
  · exact ((hf.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).add
      (integrable_toReal_of_lintegral_ne_top hS hSint.ne)).const_mul 4
  · intro z; exact mul_nonneg (by norm_num) (add_nonneg (by positivity) ENNReal.toReal_nonneg)
  · filter_upwards [hSfinite] with z hz
    refine ⟨fun n => ?_,?_⟩
    · have he : ‖g n z-f z‖^3 ≤ (S z).toReal := by
        have hh := ENNReal.toReal_mono hz.ne
          (ENNReal.le_tsum (f := fun index => ‖f z-g index z‖ₑ^3) n : ‖f z-g n z‖ₑ^3 ≤ S z)
        simpa only [ENNReal.toReal_pow,enorm_eq_nnnorm,ENNReal.coe_toReal,coe_nnnorm,norm_sub_rev] using hh
      exact (norm_cube_le_four_sub (g n z) (f z)).trans (by dsimp [D]; linarith)
    · apply tendsto_of_enorm_cube
      simpa only [enorm_sub_rev] using ENNReal.tendsto_atTop_zero_of_tsum_ne_top hz.ne
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma tendsto_integral_cubes (f : ℝ×ℝ → ℂ) (g : ℕ → ℝ×ℝ → ℂ) (hg : ∀ n, Continuous (g n))
    {D : ℝ×ℝ → ℝ} (hD : Integrable D)
    (hb : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖g n z‖^3 ≤ D z) ∧ Tendsto (fun n => g n z) atTop (𝓝 (f z))) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖g n z‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by
  apply tendsto_integral_of_dominated_convergence D (fun n => (hg n).norm.pow 3 |>.aestronglyMeasurable) hD
  · intro n
    filter_upwards [hb] with z hz
    simpa only [Pi.pow_apply,Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)] using hz.1 n
  · filter_upwards [hb] with z hz
    exact hz.2.norm.pow 3

lemma lintegral_le_of_ae_tendsto {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} {b : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hm : ∀ n, AEMeasurable (F n) μ) (ht : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a)))
    (hb : ∀ n, (∫⁻ a, F n a ∂μ) ≤ b n) (hc : Tendsto b atTop (𝓝 c)) :
    (∫⁻ a, f a ∂μ) ≤ c := by
  calc
    (∫⁻ a, f a ∂μ) = ∫⁻ a, liminf (fun n => F n a) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with a ha
      exact ha.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le' hm
    _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hb)
    _ = c := hc.liminf_eq
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma aemeasurable_cyclic_hard (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : AEMeasurable (cyclicKernelOutput B C (hardKernel r R)) volume := by
  obtain ⟨F,hF,D,hD,_,hb⟩ := exists_cubic_approximation B hB
  obtain ⟨G,hG,E,hE,_,hc⟩ := exists_cubic_approximation C hC
  have ht := tendsto_cyclicKernelOutput_of_cubic_dom B C F G (fun n => (hF n).1) (fun n => (hG n).1) hD hE hb hc
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_cyclicKernelOutput (F n) (G n) (hF n).1.measurable (hG n).1.measurable _
      (measurable_hardKernel r R)).aemeasurable)
  filter_upwards [ht] with z hz
  exact hz r R hr hR

lemma lintegral_cyclic_moment_le (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z))) ≤
      ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3))) := by
  obtain ⟨F,hF,D,hD,_,hb⟩ := exists_cubic_approximation B hB
  obtain ⟨G,hG,E,hE,_,hc⟩ := exists_cubic_approximation C hC
  have ht := tendsto_cyclicKernelOutput_of_cubic_dom B C F G (fun n => (hF n).1) (fun n => (hG n).1) hD hE hb hc
  apply lintegral_le_of_ae_tendsto
    (F := fun n z => ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput (F n) (G n) (hardKernel (r k) (R k)) z)))
    (b := fun n => ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖F n z‖^3)+(∫ z : ℝ×ℝ, ‖G n z‖^3))))
  · intro n
    exact (ENNReal.continuous_ofReal.comp continuous_finiteMoment).measurable.comp
      (Measurable.of_eval (fun k => measurable_cyclicKernelOutput (F n) (G n)
        (hF n).1.measurable (hG n).1.measurable _ (measurable_hardKernel _ _))) |>.aemeasurable
  · filter_upwards [ht] with z hz
    exact (ENNReal.continuous_ofReal.comp continuous_finiteMoment).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (fun k => hz (r k) (R k) (hr k) (hR k)))
  · intro n
    exact lintegral_cyclic_moment_le_compact (F n) (G n) (hF n).1 (hG n).1 (hF n).2.1 (hG n).2.1 r R hr hR
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((tendsto_integral_cubes B F (fun n => (hF n).1) hD hb).add
        (tendsto_integral_cubes C G (fun n => (hG n).1) hE hc)))
end
end TriangularHilbert.Heat
end

end OAI
end
end

section
section
namespace OAI


section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

lemma real_three_halves (x : ℝ) (hx : 0 ≤ x) : x^((3:ℝ)/2) = x*Real.sqrt x := by
  by_cases he : x = 0
  · subst x; norm_num
  · rw [show (3:ℝ)/2 = 1+(1:ℝ)/2 by norm_num,Real.rpow_add (lt_of_le_of_ne hx (Ne.symm he)),Real.rpow_one,Real.sqrt_eq_rpow]

lemma ofReal_complexMoment (z : ℂ) : ENNReal.ofReal (complexMoment z) = ENNReal.ofReal ‖z‖^((3:ℝ)/2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),real_three_halves _ (norm_nonneg _)]
  rfl

lemma ofReal_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ENNReal.ofReal (finiteMoment f) = ⨆ k, ENNReal.ofReal (complexMoment (f k)) := by
  apply le_antisymm
  · obtain ⟨k,hk⟩ := finiteMoment_eq f
    rw [hk]
    exact le_iSup (fun k => ENNReal.ofReal (complexMoment (f k))) k
  · exact iSup_le (fun k => ENNReal.ofReal_le_ofReal (le_finiteMoment f k))
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

lemma aemeasurable_cyclicMax (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    AEMeasurable (cyclicMax B C) volume := by
  apply AEMeasurable.iSup
  intro q
  exact (aemeasurable_cyclic_hard B C hB hC q.toEndpoints.lower_pos q.toEndpoints.lower_lt_upper.le).norm.ennreal_ofReal

def rationalMoment (B C : Plane → ℂ) (n : ℕ) (z : Plane) : ℝ≥0∞ :=
  ⨆ k : Fin (n+1), ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
    (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z))

lemma rationalMoment_mono (B C : Plane → ℂ) (z : Plane) : Monotone (fun n => rationalMoment B C n z) := by
  intro n m hnm
  apply iSup_le
  intro k
  exact le_iSup (fun k : Fin (m+1) => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
    (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z)))
    ⟨k,lt_of_lt_of_le k.2 (Nat.add_le_add_right hnm 1)⟩

lemma cyclicMax_rpow_eq (B C : Plane → ℂ) (z : Plane) :
    cyclicMax B C z ^ ((3:ℝ)/2) = ⨆ n, rationalMoment B C n z := by
  rw [cyclicMax]
  change (ENNReal.orderIsoRpow ((3:ℝ)/2) (by norm_num)) _ = _
  rw [OrderIso.map_iSup]
  simp only [ENNReal.orderIsoRpow_apply, ← ofReal_complexMoment]
  apply le_antisymm
  · apply iSup_le
    intro q
    obtain ⟨n,rfl⟩ := RatEndpoints.sequence_surjective q
    exact le_iSup_of_le n (le_iSup (fun k : Fin (n+1) => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
      (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z)))
      ⟨n,Nat.lt_succ_self n⟩)
  · apply iSup_le
    intro n
    apply iSup_le
    intro k
    exact le_iSup (fun q : RatEndpoints => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
      (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z))) (RatEndpoints.sequence k)

lemma aemeasurable_rationalMoment (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) (n : ℕ) :
    AEMeasurable (rationalMoment B C n) volume := by
  unfold rationalMoment
  simp_rw [ofReal_complexMoment]
  apply AEMeasurable.iSup
  intro k
  exact ((aemeasurable_cyclic_hard B C hB hC (RatEndpoints.sequence k).toEndpoints.lower_pos
    (RatEndpoints.sequence k).toEndpoints.lower_lt_upper.le).norm.ennreal_ofReal).pow_const _

lemma lintegral_cyclicMax_moment_le (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    (∫⁻ z : Plane, cyclicMax B C z ^ ((3:ℝ)/2)) ≤
      ENNReal.ofReal (momentConstant*((∫ z : Plane, ‖B z‖^3)+(∫ z : Plane, ‖C z‖^3))) := by
  simp_rw [cyclicMax_rpow_eq]
  rw [lintegral_iSup' (aemeasurable_rationalMoment B C hB hC)
    (Eventually.of_forall (rationalMoment_mono B C))]
  apply iSup_le
  intro n
  have h := lintegral_cyclic_moment_le B C hB hC
    (fun k : Fin (n+1) => (RatEndpoints.sequence k).toEndpoints.lower)
    (fun k : Fin (n+1) => (RatEndpoints.sequence k).toEndpoints.upper)
    (fun k => (RatEndpoints.sequence k).toEndpoints.lower_pos)
    (fun k => (RatEndpoints.sequence k).toEndpoints.lower_lt_upper.le)
  simpa only [ofReal_finiteMoment,rationalMoment] using h
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat Filter
open scoped ENNReal
noncomputable section

def cyclicNorm (B C : Plane → ℂ) : ℝ≥0∞ :=
  (∫⁻ z : Plane, cyclicMax B C z ^ ((3:ℝ)/2)) ^ ((2:ℝ)/3)

lemma cyclicKernelOutput_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    ∀ᵐ z : Plane, ∀ K : ℝ → ℝ, cyclicKernelOutput B C K z = cyclicKernelOutput B' C' K z := by
  filter_upwards [quasiMeasurePreserving_snd.ae (ae_ae_of_ae_prod hb),
    quasiMeasurePreserving_fst.ae (ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hc))]
    with z hzB hzC
  intro K
  apply integral_congr_ae
  filter_upwards [hzB,hzC] with c hB hC
  change C (c,z.1) = C' (c,z.1) at hC
  simp only [hB,hC]

lemma cyclicMax_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    cyclicMax B C =ᵐ[volume] cyclicMax B' C' := by
  filter_upwards [cyclicKernelOutput_congr_ae hb hc] with z hz
  simp only [cyclicMax,hz]

lemma cyclicNorm_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    cyclicNorm B C = cyclicNorm B' C' := by
  unfold cyclicNorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [cyclicMax_congr_ae hb hc] with z hz
  rw [hz]

@[simp] lemma cyclicNorm_zero_left (C : Plane → ℂ) : cyclicNorm 0 C = 0 := by
  simp [cyclicNorm,cyclicMax,cyclicKernelOutput]
@[simp] lemma cyclicNorm_zero_right (B : Plane → ℂ) : cyclicNorm B 0 = 0 := by
  simp [cyclicNorm,cyclicMax,cyclicKernelOutput]

lemma cyclicKernelOutput_smul (B C : Plane → ℂ) (u v : ℂ) (K : ℝ → ℝ) (z : Plane) :
    cyclicKernelOutput (u • B) (v • C) K z = (u*v)*cyclicKernelOutput B C K z := by
  rw [cyclicKernelOutput,cyclicKernelOutput,← integral_const_mul]
  congr 1
  funext c
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma cyclicMax_smul (B C : Plane → ℂ) (u v : ℂ) (z : Plane) :
    cyclicMax (u • B) (v • C) z = (‖u‖ₑ*‖v‖ₑ)*cyclicMax B C z := by
  simp only [cyclicMax,cyclicKernelOutput_smul,ofReal_norm,enorm_mul]
  rw [ENNReal.mul_iSup]

lemma cyclicNorm_smul (B C : Plane → ℂ) (u v : ℂ) :
    cyclicNorm (u • B) (v • C) = (‖u‖ₑ*‖v‖ₑ)*cyclicNorm B C := by
  have he : (fun z : Plane => cyclicMax (u • B) (v • C) z ^ ((3:ℝ)/2)) =
      (fun z : Plane => (‖u‖ₑ*‖v‖ₑ)^((3:ℝ)/2)*cyclicMax B C z^((3:ℝ)/2)) := by
    funext z
    rw [cyclicMax_smul,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [cyclicNorm,cyclicNorm,he,
    lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul]
  norm_num
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
open scoped ENNReal NNReal
noncomputable section

def mainConstant : ℝ≥0 := ⟨(2*momentConstant)^((2:ℝ)/3),Real.rpow_nonneg (mul_nonneg (by norm_num) momentConstant_pos.le) _⟩

lemma coe_mainConstant : (mainConstant : ℝ≥0∞) = ENNReal.ofReal (2*momentConstant)^((2:ℝ)/3) := by
  rw [ENNReal.coe_nnreal_eq]
  exact (ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by norm_num) momentConstant_pos.le) (by norm_num)).symm

lemma ofReal_integral_cube (B : Plane → ℂ) (hB : MemLp B 3 volume) :
    ENNReal.ofReal (∫ z : Plane, ‖B z‖^3) = eLpNorm B 3 volume ^ (3:ℕ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hB.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0))
    (Eventually.of_forall (fun z => pow_nonneg (norm_nonneg (B z)) 3))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  exact lintegral_enorm_cube B volume hB.aestronglyMeasurable

lemma integral_cube_eq_one (B : Plane → ℂ) (hB : MemLp B 3 volume) (hn : eLpNorm B 3 volume = 1) :
    (∫ z : Plane, ‖B z‖^3) = 1 := by
  have h := congrArg ENNReal.toReal (ofReal_integral_cube B hB)
  simpa only [hn,one_pow,ENNReal.toReal_one,
    ENNReal.toReal_ofReal (integral_nonneg (fun z => pow_nonneg (norm_nonneg (B z)) 3))] using h

lemma cyclicNorm_le_unit (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    (hnB : eLpNorm B 3 volume = 1) (hnC : eLpNorm C 3 volume = 1) :
    cyclicNorm B C ≤ (mainConstant : ℝ≥0∞) := by
  rw [cyclicNorm,coe_mainConstant]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have h := lintegral_cyclicMax_moment_le B C hB hC
  rw [integral_cube_eq_one B hB hnB,integral_cube_eq_one C hC hnC] at h
  simpa only [show momentConstant*((1:ℝ)+1) = 2*momentConstant by ring] using h

lemma cyclicNorm_le (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    cyclicNorm B C ≤ (mainConstant : ℝ≥0∞)*eLpNorm B 3 volume*eLpNorm C 3 volume := by
  by_cases hb0 : eLpNorm B 3 volume = 0
  · have hb := (eLpNorm_eq_zero_iff hB.1 (by norm_num)).mp hb0
    rw [cyclicNorm_congr_ae hb (EventuallyEq.refl _ _),cyclicNorm_zero_left]
    exact bot_le
  by_cases hc0 : eLpNorm C 3 volume = 0
  · have hc := (eLpNorm_eq_zero_iff hC.1 (by norm_num)).mp hc0
    rw [cyclicNorm_congr_ae (EventuallyEq.refl _ _) hc,cyclicNorm_zero_right]
    exact bot_le
  let u : ℂ := (eLpNorm B 3 volume).toReal
  let v : ℂ := (eLpNorm C 3 volume).toReal
  have hu : ‖u‖ₑ = eLpNorm B 3 volume := by
    rw [← ofReal_norm]
    simp only [u,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hB.eLpNorm_ne_top]
  have hv : ‖v‖ₑ = eLpNorm C 3 volume := by
    rw [← ofReal_norm]
    simp only [v,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hC.eLpNorm_ne_top]
  have hu0 : u ≠ 0 := by
    intro he
    exact hb0 (by simpa only [he,enorm_zero] using hu.symm)
  have hv0 : v ≠ 0 := by
    intro he
    exact hc0 (by simpa only [he,enorm_zero] using hv.symm)
  have hiB : MemLp (u⁻¹ • B) 3 volume := hB.const_smul _
  have hiC : MemLp (v⁻¹ • C) 3 volume := hC.const_smul _
  have hnB : eLpNorm (u⁻¹ • B) 3 volume = 1 := by
    rw [eLpNorm_const_smul,enorm_inv hu0,hu,ENNReal.inv_mul_cancel hb0 hB.eLpNorm_ne_top]
  have hnC : eLpNorm (v⁻¹ • C) 3 volume = 1 := by
    rw [eLpNorm_const_smul,enorm_inv hv0,hv,ENNReal.inv_mul_cancel hc0 hC.eLpNorm_ne_top]
  calc
    cyclicNorm B C = cyclicNorm (u • (u⁻¹ • B)) (v • (v⁻¹ • C)) := by
      rw [smul_smul,smul_smul,mul_inv_cancel₀ hu0,mul_inv_cancel₀ hv0,one_smul,one_smul]
    _ = (‖u‖ₑ*‖v‖ₑ)*cyclicNorm (u⁻¹ • B) (v⁻¹ • C) := cyclicNorm_smul _ _ _ _
    _ ≤ (‖u‖ₑ*‖v‖ₑ)*(mainConstant : ℝ≥0∞) := by
      gcongr
      exact cyclicNorm_le_unit _ _ hiB hiC hnB hnC
    _ = (mainConstant : ℝ≥0∞)*eLpNorm B 3 volume*eLpNorm C 3 volume := by
      rw [hu,hv]
      ac_rfl
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat
open scoped ENNReal
noncomputable section

def chartB (z : Plane) : Plane := (z.1+z.2,-z.1)
def chartC (z : Plane) : Plane := (-z.2,z.1+z.2)
def cyclicB (F : Plane → ℂ) : Plane → ℂ := F ∘ chartB
def cyclicC (G : Plane → ℂ) : Plane → ℂ := G ∘ chartC

lemma measurePreserving_chartB : MeasurePreserving chartB volume volume := by
  exact measurePreserving_add_prod_neg_right (volume : Measure ℝ) volume

lemma measurePreserving_chartC : MeasurePreserving chartC volume volume := by
  have hs : MeasurePreserving (Prod.swap : Plane → Plane) volume volume := measurePreserving_swap
  have h := (hs.comp measurePreserving_chartB).comp hs
  convert h using 1
  funext z
  simp only [Function.comp_apply,chartC,chartB,Prod.swap,add_comm]

lemma measurePreserving_reflect : MeasurePreserving (fun z : Plane => -z) volume volume :=
  volume.measurePreserving_neg

lemma memLp_cyclicB {F : Plane → ℂ} (hF : MemLp F 3 volume) : MemLp (cyclicB F) 3 volume :=
  hF.comp_measurePreserving measurePreserving_chartB
lemma memLp_cyclicC {G : Plane → ℂ} (hG : MemLp G 3 volume) : MemLp (cyclicC G) 3 volume :=
  hG.comp_measurePreserving measurePreserving_chartC

lemma eLpNorm_cyclicB {F : Plane → ℂ} (hF : MemLp F 3 volume) :
    eLpNorm (cyclicB F) 3 volume = eLpNorm F 3 volume :=
  eLpNorm_comp_measurePreserving hF.aestronglyMeasurable measurePreserving_chartB
lemma eLpNorm_cyclicC {G : Plane → ℂ} (hG : MemLp G 3 volume) :
    eLpNorm (cyclicC G) 3 volume = eLpNorm G 3 volume :=
  eLpNorm_comp_measurePreserving hG.aestronglyMeasurable measurePreserving_chartC

lemma measurableSet_annulus (r R : ℝ) : MeasurableSet (annulus r R) :=
  (isOpen_lt continuous_const continuous_abs).measurableSet.inter
    (isOpen_lt continuous_abs continuous_const).measurableSet

lemma hardKernel_eq_indicator_ae {r R : ℝ} (hR : r ≤ R) :
    (fun t => hardKernel r R t) =ᵐ[volume]
      (annulus r R).indicator (fun t : ℝ => 1/t) := by
  have hne (x : ℝ) : ∀ᵐ t : ℝ, t ≠ x := by simp [ae_iff]
  filter_upwards [hne R,hne (-R)] with t ht1 ht2
  have ht : |t| ≠ R := by
    intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · exact ht1 he
    · exact ht2 he
  classical
  by_cases h1 : r < |t|
  · by_cases h2 : |t| < R
    · simp only [hardKernel,h1,ite_true,not_lt.mpr h2.le,ite_false,sub_zero,
        Set.indicator_of_mem (show t ∈ annulus r R from ⟨h1,h2⟩)]
    · have h3 : R < |t| := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm ht)
      simp only [hardKernel,h1,h3,ite_true,sub_self,zero_div,
        Set.indicator_of_notMem (show t ∉ annulus r R from fun h => h2 h.2)]
  · have h2 : ¬ R < |t| := not_lt.mpr ((le_of_not_gt h1).trans hR)
    simp only [hardKernel,h1,h2,ite_false,sub_self,zero_div,
      Set.indicator_of_notMem (show t ∉ annulus r R from fun h => h1 h.1)]

lemma cyclicHard_coordinate_integrand (F G : Plane → ℂ) (z : Plane) (r R t : ℝ) :
    cyclicB F ((-z).2,t+z.1+z.2) * cyclicC G (t+z.1+z.2,(-z).1) *
      (hardKernel r R ((-z).1+(-z).2+(t+z.1+z.2)):ℂ) =
    F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ) := by
  change F (-z.2+(t+z.1+z.2),-(-z.2))*G (-(-z.1),(t+z.1+z.2)+(-z.1))*
    (hardKernel r R (-z.1 + -z.2+(t+z.1+z.2)):ℂ) = _
  rw [show -z.2+(t+z.1+z.2) = z.1+t by ring,
    show (t+z.1+z.2)+(-z.1) = z.2+t by ring,
    show -z.1 + -z.2+(t+z.1+z.2) = t by ring]
  simp only [neg_neg]
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
noncomputable section

lemma cyclicHard_coordinate_output (F G : Plane → ℂ) (z : Plane) (r R : ℝ) :
    cyclicKernelOutput (cyclicB F) (cyclicC G) (hardKernel r R) (-z) =
      ∫ t : ℝ, F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ) := by
  rw [cyclicKernelOutput,← integral_add_right_eq_self _ (z.1+z.2)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by simpa only [add_assoc] using cyclicHard_coordinate_integrand F G z r R t)

lemma hardIntegrand_eq_indicator_ae (F G : Plane → ℂ) (z : Plane) {r R : ℝ} (hR : r ≤ R) :
    (fun t : ℝ => F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ)) =ᵐ[volume]
      (annulus r R).indicator (integrand F G z) := by
  filter_upwards [hardKernel_eq_indicator_ae hR] with t ht
  classical
  by_cases hm : t ∈ annulus r R
  · rw [Set.indicator_of_mem hm] at ht
    rw [ht,Set.indicator_of_mem hm]
    simp only [integrand,div_eq_mul_inv,one_mul,Complex.ofReal_inv]
  · rw [Set.indicator_of_notMem hm] at ht
    simp only [ht,Complex.ofReal_zero,mul_zero,Set.indicator_of_notMem hm]

lemma truncation_eq_cyclicHard (F G : Plane → ℂ) (z : Plane) (E : Endpoints) :
    truncation F G E z = cyclicKernelOutput (cyclicB F) (cyclicC G) (hardKernel E.lower E.upper) (-z) := by
  rw [cyclicHard_coordinate_output,integral_congr_ae (hardIntegrand_eq_indicator_ae F G z E.lower_lt_upper.le),
    integral_indicator (measurableSet_annulus E.lower E.upper)]
  rfl

lemma Heat.CubicSliceGood.integrableOn_annulus {F G : Plane → ℂ} {z : Plane}
    (hz : CubicSliceGood (cyclicB F) (cyclicC G) (-z))
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : IntegrableOn (integrand F G z) (annulus r R) := by
  have hi := hz.integrable_hard hr hR
  have ht := ((measurePreserving_add_right (volume : Measure ℝ) (z.1+z.2)).integrable_comp hi.aestronglyMeasurable).mpr hi
  have hi' : Integrable (fun t : ℝ => F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ)) := by
    convert ht using 1
    funext t
    simpa only [Function.comp_apply,add_assoc] using (cyclicHard_coordinate_integrand F G z r R t).symm
  exact (integrable_indicator_iff (measurableSet_annulus r R)).mp
    (hi'.congr (hardIntegrand_eq_indicator_ae F G z hR))

lemma Heat.CubicSliceGood.goodPoint {F G : Plane → ℂ} {z : Plane}
    (hz : CubicSliceGood (cyclicB F) (cyclicC G) (-z)) : GoodPoint F G z := by
  intro n
  apply hz.integrableOn_annulus
  · positivity
  · apply (div_le_iff₀ (show (0:ℝ) < n+2 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma ae_goodPoint (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    ∀ᵐ z : Plane, GoodPoint F G z := by
  filter_upwards [measurePreserving_reflect.quasiMeasurePreserving.ae
    (ae_cubicSliceGood (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG))] with z hz
  exact hz.goodPoint
end
end TriangularHilbert
end

end OAI
end
end

section
section
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
open scoped ENNReal
noncomputable section

lemma maximal_eq_cyclicMax_ae (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    maximal F G =ᵐ[volume] (fun z => cyclicMax (cyclicB F) (cyclicC G) (-z)) := by
  filter_upwards [measurePreserving_reflect.quasiMeasurePreserving.ae
    (ae_cubicSliceGood (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG))] with z hz
  rw [maximal,ite_eq_left hz.goodPoint]
  simp_rw [truncation_eq_cyclicHard]
  exact (cyclicMax_eq_iSup hz).symm

lemma aemeasurable_maximal (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    AEMeasurable (maximal F G) volume := by
  have h := (aemeasurable_cyclicMax (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG)).comp_quasiMeasurePreserving
    measurePreserving_reflect.quasiMeasurePreserving
  exact h.congr (maximal_eq_cyclicMax_ae F G hF hG).symm

lemma maximalNorm_eq_cyclicNorm (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    maximalNorm F G = cyclicNorm (cyclicB F) (cyclicC G) := by
  unfold maximalNorm cyclicNorm
  congr 1
  calc
    (∫⁻ z : Plane, maximal F G z ^ ((3:ℝ)/2)) =
        ∫⁻ z : Plane, cyclicMax (cyclicB F) (cyclicC G) (-z)^((3:ℝ)/2) := by
      apply lintegral_congr_ae
      filter_upwards [maximal_eq_cyclicMax_ae F G hF hG] with z hz
      rw [hz]
    _ = _ := measurePreserving_reflect.lintegral_comp_emb (Homeomorph.neg Plane).measurableEmbedding
      (fun z => cyclicMax (cyclicB F) (cyclicC G) z^((3:ℝ)/2))

theorem main_estimate_oai : MainEstimate := by
  refine ⟨mainConstant,fun F G hF hG => ⟨ae_goodPoint F G hF hG,aemeasurable_maximal F G hF hG,?_⟩⟩
  rw [maximalNorm_eq_cyclicNorm F G hF hG]
  simpa only [eLpNorm_cyclicB hF,eLpNorm_cyclicC hG] using
    cyclicNorm_le (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG)
end
end TriangularHilbert
end

end OAI
end
end

theorem solution : type_of% @OAI.TriangularHilbert.main_estimate_oai := @OAI.TriangularHilbert.main_estimate_oai
