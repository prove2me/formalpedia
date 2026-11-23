-- Prove2me | solution 1 for GrothendieckLB.theorem_8_5
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:11:16.494391+00:00
-- url     : https://prove2.me/submissions/9e72f76e-ec80-40a0-b72c-b603cafeef28

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_GrothendieckLB_p3NormSq
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_Pfun
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8

section

-- Gaussian projection, contraction, and integrability lemmas adapted from LG’s symmetric-scheme proof.
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace KG

/-- Standard Gaussian density on `Fin k → ℝ`. -/
noncomputable def phiK (k : ℕ) (x : Fin k → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma phiK_nonneg (k : ℕ) (x : Fin k → ℝ) : 0 ≤ phiK k x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma measurable_phiK (k : ℕ) : Measurable (phiK k) := by
  unfold phiK
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

lemma pi_gauss (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity (fun x => ENNReal.ofReal (phiK k x)) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : Fin k → ℝ, (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (phiK k x)) x
      = ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      unfold phiK
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  have hint : Integrable (fun x : Fin k → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun i =>
      (integrable_gaussianPDFReal 0 1).indicator (hs i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
      Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_indicator (hs i), gaussianReal_apply 0 one_ne_zero (s i)]
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
    (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg 0 1 y)]
  rfl

/-- Integrals against the Gaussian density equal integrals against the product measure. -/
lemma integral_phiK (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    ∫ x, phiK k x * F x = ∫ x, F x ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  rw [pi_gauss, integral_withDensity_eq_integral_toReal_smul (measurable_phiK k).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (phiK_nonneg k x)]

end KG

namespace KG

open scoped RealInnerProductSpace

/-- One-dimensional absolute moments of the standard Gaussian. -/
lemma gauss_abs_moment (q : ℝ) (hq : -1 < q) :
    ∫ t, |t| ^ q ∂(gaussianReal 0 1) =
      2 * ((1 / Real.sqrt (2 * π)) * ((1 / 2 : ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Gamma ((q + 1) / 2))) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h1 : ∀ t : ℝ, gaussianPDFReal 0 1 t • |t| ^ q =
      (fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ)))) |t| := by
    intro t
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [Real.rpow_two, sq_abs]
    ring_nf
  simp_rw [h1]
  rw [integral_comp_abs (f := fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ))))]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num)]

lemma gauss_abs_one : ∫ t, |t| ∂(gaussianReal 0 1) = Real.sqrt (2 / π) := by
  have h := gauss_abs_moment 1 (by norm_num)
  simp only [Real.rpow_one] at h
  rw [h]
  norm_num [Real.Gamma_one]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt π ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith [hs]

/-- Projection law: for a unit vector `v`, `x ↦ ∑ v i * x i` is standard normal under the product measure. -/
lemma proj_law (k : ℕ) (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, v i * x i) = gaussianReal 0 1 := by
  set u : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 v
  have hu : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simpa [u, Real.norm_eq_abs, sq_abs] using hv
  have hfun : (fun x : Fin k → ℝ => ∑ i, v i * x i) = (fun y : EuclideanSpace ℝ (Fin k) => ⟪y, u⟫) ∘ (WithLp.toLp 2) := by
    funext x
    simp [u, PiLp.inner_apply]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian]
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin k)) := innerSL ℝ u
  have hL : ‖L‖ = 1 := by simp [L, hu]
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin k))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hL]
    norm_num
  convert hm using 1
  congr 1
  ext y
  simpa [L] using (real_inner_comm u y)

end KG

namespace KG

/-- Polynomial times `exp (-A/4)` is dominated by a multiple of `exp (-A/8)`. -/
lemma poly_exp_le (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4))
      ≤ 2000 * ((1 + k) ^ 3 + 3072) * Real.exp (-(A / 8)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcube : (1 + A + k) ^ 3 ≤ 4 * ((1 + k) ^ 3 + A ^ 3) := by
    nlinarith [sq_nonneg (1 + k - A), mul_nonneg (add_nonneg zero_le_one hk) hA,
      mul_nonneg (mul_nonneg (add_nonneg zero_le_one hk) hA) (sq_nonneg (1 + k - A))]
  have hA3 : A ^ 3 ≤ 3072 * Real.exp (A / 8) := by
    have := Real.pow_div_factorial_le_exp (A / 8) (by positivity) 3
    norm_num [Nat.factorial] at this
    nlinarith
  have he1 : 1 ≤ Real.exp (A / 8) := Real.one_le_exp (by positivity)
  have hsplit : Real.exp (-(A / 4)) = (Real.exp (A / 8))⁻¹ * Real.exp (-(A / 8)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (-(A / 8)) := Real.exp_pos _
  have key : (1 + A + k) ^ 3 * (Real.exp (A / 8))⁻¹ ≤ 4 * ((1 + k) ^ 3 + 3072) := by
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]
    have : (0:ℝ) ≤ (1 + k) ^ 3 := by positivity
    nlinarith
  rw [hsplit]
  have := mul_le_mul_of_nonneg_right key hpos.le
  nlinarith

end KG

namespace KG

open Finset

/-- `H3 x i j l = x_i x_j x_l - δ_ij x_l - δ_il x_j - δ_jl x_i`. -/
def H3 {k : ℕ} (x : Fin k → ℝ) (i j l : Fin k) : ℝ :=
  x i * x j * x l - (if i = j then x l else 0) - (if i = l then x j else 0)
    - (if j = l then x i else 0)

end KG

open Real MeasureTheory Filter ProbabilityTheory Finset

set_option linter.unusedSectionVars false

namespace KG

lemma gaussianPDFReal_std (s : ℝ) :
    gaussianPDFReal 0 1 s = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(s ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

lemma phiK_le_exp {k : ℕ} (x : Fin k → ℝ) : phiK k x ≤ Real.exp (-((∑ i, x i ^ 2) / 2)) := by
  unfold phiK
  rw [show -((∑ i, x i ^ 2) / 2) = ∑ i, -(x i ^ 2 / 2) by rw [sum_div, sum_neg_distrib],
    Real.exp_sum]
  refine prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _) fun i _ => ?_
  rw [gaussianPDFReal_std]
  have : 1 ≤ Real.sqrt (2 * π) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  calc (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x i ^ 2 / 2)) ≤ 1 * Real.exp (-(x i ^ 2 / 2)) := by
        gcongr; exact inv_le_one_of_one_le₀ this
    _ = _ := one_mul _

lemma integrable_exp_Q (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Fin k → ℝ => Real.exp (-(b * ∑ i, x i ^ 2))) := by
  have h1 : Integrable (fun x : Fin k → ℝ => ∏ i, Real.exp (-b * x i ^ 2)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ s => Real.exp (-b * s ^ 2))
      fun _ => integrable_exp_neg_mul_sq hb
  refine h1.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [← Real.exp_sum, mul_sum, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring

/-- A bounded function times a cubic-growth weight times the Gaussian density is integrable. -/
lemma integrable_poly_phi {k : ℕ} (h p : (Fin k → ℝ) → ℝ) (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) (hp : Measurable p) (C : ℝ) (hC : 0 ≤ C)
    (hpC : ∀ x, |p x| ≤ C * (1 + ∑ i, x i ^ 2) ^ 3) :
    Integrable (fun x => h x * p x * phiK k x) := by
  refine ((integrable_exp_Q k (1 / 4) (by norm_num)).const_mul (C * (2000 * 3073 / 500))).mono'
    ((hh.mul hp).mul (measurable_phiK k)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  set Q := ∑ i, x i ^ 2
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg _
  have hphi := phiK_le_exp x
  have hphi0 := phiK_nonneg k x
  have key := poly_exp_le 0 (A := 2 * Q) (by positivity)
  simp only [Nat.cast_zero, add_zero] at key
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hphi0]
  have h1 : (1 + Q) ^ 3 ≤ (1 + 2 * Q) ^ 3 := by gcongr; linarith
  have e1 : -(2 * Q / 4) = -(Q / 2) := by ring
  have e2 : -(2 * Q / 8) = -(1 / 4 * Q) := by ring
  rw [e1, e2] at key
  calc |h x| * |p x| * phiK k x ≤ 1 * (C * (1 + Q) ^ 3) * Real.exp (-(Q / 2)) := by
        gcongr
        · exact hb x
        · exact hpC x
    _ ≤ C * ((1 + 2 * Q) ^ 3 * Real.exp (-(Q / 2))) := by
        rw [one_mul, mul_assoc]; gcongr
    _ ≤ C * (2000 * (1 + 3072) / 500 * Real.exp (-(1 / 4 * Q))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        norm_num at key ⊢; linarith
    _ = _ := by norm_num; ring

lemma abs_coord_le {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 + ∑ j, x j ^ 2 := by
  have : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + 1 / 2), sq_nonneg (x i - 1 / 2)]

lemma one_le_oneQ {k : ℕ} (x : Fin k → ℝ) : 1 ≤ 1 + ∑ j, x j ^ 2 := by
  have := sum_nonneg (s := univ) fun j _ => sq_nonneg (x j); linarith

lemma abs_coord_le3 {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  have h1 := one_le_oneQ x
  have := abs_coord_le x i
  nlinarith [pow_le_pow_right₀ h1 (show 1 ≤ 3 by norm_num), pow_one (1 + ∑ j, x j ^ 2)]

section scheme
variable {k : ℕ}

/-- First moments `E[h(X) X_i]`. -/
noncomputable def mom1 (h : (Fin k → ℝ) → ℝ) (i : Fin k) : ℝ := ∫ x, h x * x i * phiK k x

lemma integrable_mom1 (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i : Fin k) : Integrable (fun x => h x * x i * phiK k x) :=
  integrable_poly_phi h (fun x => x i) hh hb (measurable_pi_apply i) 1 zero_le_one
    fun x => abs_coord_le3 x i

end scheme

end KG

open Real MeasureTheory Filter ProbabilityTheory Finset

set_option linter.unusedSectionVars false

namespace KG

variable {k : ℕ}

noncomputable def proj (v x : Fin k → ℝ) : ℝ := ∑ i, v i * x i

lemma measurable_proj (v : Fin k → ℝ) : Measurable (proj v) := by
  unfold proj; fun_prop

lemma sum_mom1_eq (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) :
    ∑ i, v i * mom1 h i = ∫ x, h x * proj v x ^ 1 * phiK k x := by
  unfold mom1
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (integrable_mom1 h hh hb i).const_mul (v i)]
  congr 1; ext x
  simp only [proj, pow_one, mul_sum, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  ring

end KG

end

section

open Finset Equiv MulAction

namespace CubicChaos

noncomputable def counts {n d : ℕ} (v : Fin n → Fin d) (i : Fin d) : ℕ :=
  Fintype.card {a // v a = i}

noncomputable def weights {d : ℕ} (κ : Fin d → ℕ) : ℕ := ∏ i, (κ i).factorial

private lemma orbit_counts {n d : ℕ} (v u : Fin n → Fin d) :
    u ∈ MulAction.orbit (DomMulAct (Perm (Fin n))) v ↔ counts u = counts v := by
  classical
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    funext i
    exact Fintype.card_congr (Equiv.subtypeEquiv (DomMulAct.mk.symm g) (fun a => Iff.rfl))
  · intro h
    let e (i : Fin d) : {a // u a = i} ≃ {a // v a = i} :=
      Fintype.equivOfCardEq (congrFun h i)
    exact ⟨DomMulAct.mk (Equiv.ofFiberEquiv e), funext (Equiv.ofFiberEquiv_map e)⟩

private lemma fiber_count {n d : ℕ} (v : Fin n → Fin d) :
    (univ.filter (fun u : Fin n → Fin d => counts u = counts v)).card *
      weights (counts v) = n.factorial := by
  classical
  let G := DomMulAct (Perm (Fin n))
  letI : Fintype G := Fintype.ofEquiv _ (DomMulAct.mk : Perm (Fin n) ≃ G)
  letI : Fintype (stabilizer G v) := Fintype.ofFinite _
  letI : Fintype (orbit G v) := Fintype.ofFinite _
  have hs : Fintype.card (stabilizer G v) = weights (counts v) := by
    calc Fintype.card (stabilizer G v)
        = Fintype.card {g : Perm (Fin n) // v ∘ g = v} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquiv (p := fun g => g ∈ stabilizer G v)
            (q := fun g : Perm (Fin n) => v ∘ g = v) DomMulAct.mk.symm
            (fun _ => Iff.rfl)
      _ = _ := DomMulAct.stabilizer_card v
  have ho : Fintype.card (orbit G v) =
      (univ.filter (fun u : Fin n → Fin d => counts u = counts v)).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun u => by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.refl_apply] using
        orbit_counts v u))
  have ha := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G v
  rw [hs, ho] at ha
  exact ha.trans ((Fintype.card_congr DomMulAct.mk.symm).trans (by simp [Fintype.card_perm]))

lemma weighted_sum {n d : ℕ} (B : (Fin d → ℕ) → ℝ) :
    ∑ p : Fin n → Fin d, (weights (counts p) : ℝ) * B (counts p) =
      (n.factorial : ℝ) * ∑ κ ∈ univ.image (counts (n := n) (d := d)), B κ := by
  classical
  rw [Finset.sum_comp (f := fun κ => (weights κ : ℝ) * B κ) (g := counts),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hκ
  rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, fiber_count]

def tupleEquiv (d : ℕ) : (Fin 3 → Fin d) ≃ Fin d × Fin d × Fin d where
  toFun p := (p 0, p 1, p 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv p := funext fun i => by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨i,j,l⟩; rfl

lemma sum_triples {d : ℕ} (B : Fin d → Fin d → Fin d → ℝ) :
    ∑ p : Fin 3 → Fin d, B (p 0) (p 1) (p 2) = ∑ i, ∑ j, ∑ l, B i j l := by
  let f := fun p : Fin d × Fin d × Fin d => B p.1 p.2.1 p.2.2
  have h := (tupleEquiv d).sum_comp f
  simpa [f, tupleEquiv, Fintype.sum_prod_type] using h

lemma counts_three {d : ℕ} (v : Fin 3 → Fin d) (i : Fin d) :
    counts v i = (if v 0 = i then 1 else 0) + (if v 1 = i then 1 else 0) +
      (if v 2 = i then 1 else 0) := by
  classical
  rw [counts, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]

end CubicChaos

end

section

open MeasureTheory ProbabilityTheory Real Filter Finset KG GrothendieckLB
open PrivateAgnosticHalfspace.Gaussian
open scoped RealInnerProductSpace

namespace CubicChaos

private noncomputable def rawH (n : ℕ) (s : ℝ) : ℝ :=
  ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval s

@[simp] private lemma raw0 (z : ℝ) : rawH 0 z = 1 := by
  simp [rawH, Polynomial.hermite]
@[simp] private lemma raw1 (z : ℝ) : rawH 1 z = z := by
  simp [rawH, Polynomial.hermite_one]
@[simp] private lemma raw2 (z : ℝ) : rawH 2 z = z ^ 2 - 1 := by
  norm_num [rawH, Polynomial.hermite, Polynomial.derivative_mul] <;> ring
@[simp] private lemma raw3 (z : ℝ) : rawH 3 z = z ^ 3 - 3 * z := by
  norm_num [rawH, Polynomial.hermite, Polynomial.derivative_mul] <;> ring

private lemma raw_triple {d : ℕ} (z : Fin d → ℝ) (i j l : Fin d) :
    (∏ m : Fin d, rawH ((if i = m then 1 else 0) + (if j = m then 1 else 0) +
      (if l = m then 1 else 0)) (z m)) = H3 z i j l := by
  classical
  rw [← Finset.prod_subset (Finset.subset_univ ({i,j,l} : Finset (Fin d))) (by
    intro m _ hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp [Ne.symm hm.1, Ne.symm hm.2.1, Ne.symm hm.2.2])]
  by_cases h : i = j
  · subst j
    by_cases h : i = l
    · subst l; simp [H3] <;> ring
    · simp [H3, h, Ne.symm h] <;> ring
  · by_cases hi : i = l
    · subst l; simp [H3, h, Ne.symm h] <;> ring
    · by_cases hj : j = l
      · subst l; simp [H3, h, Ne.symm h] <;> ring
      · simp [H3, h, hi, hj, Ne.symm h, Ne.symm hi, Ne.symm hj] <;> ring

noncomputable def factor {d : ℕ} (κ : Fin d → ℕ) :=
  ∏ m, Real.sqrt ((κ m).factorial : ℝ)

theorem factor_sq {d : ℕ} (κ : Fin d → ℕ) : factor κ ^ 2 = (weights κ : ℝ) := by
  simp [factor, weights, ← Finset.prod_pow, Real.sq_sqrt]

theorem tensor_basis {d : ℕ} (v : Fin 3 → Fin d) (z : Fin d → ℝ) :
    H3 z (v 0) (v 1) (v 2) = factor (counts v) * hermite d (counts v) (WithLp.toLp 2 z) := by
  have norm_id (n : ℕ) (s : ℝ) : Real.sqrt (n.factorial : ℝ) *
      AMPLowDeg.RankOne.hermNorm n s = rawH n s := by
    unfold AMPLowDeg.RankOne.hermNorm rawH
    have h : 0 < Real.sqrt (n.factorial : ℝ) := by positivity
    field_simp
  unfold factor hermite
  rw [← Finset.prod_mul_distrib]
  simp only [norm_id, counts_three]
  exact (raw_triple z (v 0) (v 1) (v 2)).symm

private lemma exp_to_euclidean {d : ℕ} (F : Vec d → ℝ) (hm : Measurable F) :
    gaussExp (fun z => F (WithLp.toLp 2 z)) = ∫ z, F z ∂(gaussian d) := by
  change (∫ z : Fin d → ℝ, F (WithLp.toLp 2 z) * phiK d z) = _
  simp_rw [mul_comm (F _) (phiK _ _)]
  rw [integral_phiK]
  change _ = ∫ z, F z ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
  rw [← map_pi_eq_stdGaussian]
  exact (integral_map (by fun_prop) hm.aestronglyMeasurable).symm

theorem cubic_bessel {d : ℕ} (u : (Fin d → ℝ) → ℝ)
    (hu : Measurable u) (ub : ∀ z, |u z| ≤ 1) :
    p3NormSq u ≤ gaussExp (fun z => u z ^ 2) := by
  classical
  let U : Vec d → ℝ := fun z => u (WithLp.ofLp z)
  have hU : Measurable U := hu.comp (by fun_prop)
  let μ := gaussian d
  letI : IsProbabilityMeasure μ := (inferInstance : IsProbabilityMeasure (stdGaussian (Vec d)))
  have hU2 : MemLp U 2 μ := MemLp.of_bound hU.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using ub (WithLp.ofLp z))
  let X := hU2.toLp U
  have hX : (fun z => X z) =ᵐ[μ] U := hU2.coeFn_toLp
  obtain ⟨b, hb⟩ := (lemma_B_8 d).2.2.1
  let A := fun κ => ⟪b κ, X⟫
  have hherm (κ : Fin d → ℕ) : Measurable (hermite d κ) := by
    unfold hermite AMPLowDeg.RankOne.hermNorm
    fun_prop
  have hA (κ : Fin d → ℕ) : A κ =
      gaussExp (fun z => u z * hermite d κ (WithLp.toLp 2 z)) := by
    rw [exp_to_euclidean (fun z => U z * hermite d κ z) (hU.mul (hherm κ))]
    change ⟪b κ, X⟫ = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hb κ, hX] with z hz hzx
    rw [hz, hzx]
    rfl
  have hNorm : ‖X‖ ^ 2 = gaussExp (fun z => u z ^ 2) := by
    rw [exp_to_euclidean (fun z => U z ^ 2) (hU.pow_const _),
      ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hX] with z hz
    rw [hz]
    simp [sq, U, real_inner_self_eq_norm_sq]
  have hcoeff (p : Fin 3 → Fin d) :
      cubicMoment u (p 0) (p 1) (p 2) = factor (counts p) * A (counts p) := by
    change (∫ z, u z * H3 z (p 0) (p 1) (p 2) * phiK d z) = _
    rw [hA, gaussExp, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    change u z * H3 z (p 0) (p 1) (p 2) * phiK d z = _
    rw [tensor_basis p]
    change u z * (factor _ * _) * phiK d z = factor _ * (u z * _ * phiK d z)
    ring
  have hsum :
      ∑ p : Fin 3 → Fin d, cubicMoment u (p 0) (p 1) (p 2) * cubicMoment u (p 0) (p 1) (p 2) =
      6 * ∑ κ ∈ univ.image (counts (n := 3) (d := d)), A κ ^ 2 := by
    have h6 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    simpa only [hcoeff, ← sq, mul_pow, factor_sq, h6] using
      (weighted_sum (n := 3) (d := d) (fun κ => A κ ^ 2))
  rw [sum_triples (B := fun i j l => cubicMoment u i j l * cubicMoment u i j l)] at hsum
  have hB := b.orthonormal.sum_inner_products_le X
    (s := univ.image (counts (n := 3) (d := d)))
  change (∑ κ ∈ _, ‖A κ‖ ^ 2) ≤ _ at hB
  simp only [Real.norm_eq_abs, sq_abs, hNorm] at hB
  unfold p3NormSq p3Inner
  linarith only [hsum, hB]

end CubicChaos

end

section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

namespace GaussianBand

noncomputable def band (r s : ℝ) : ℝ := if |s| ≤ r then 1 else 0

lemma measurable_band (r : ℝ) : Measurable (band r) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const measurable_const

lemma band_bound (r s : ℝ) : 0 ≤ band r s ∧ band r s ≤ 1 := by
  unfold band; split_ifs <;> norm_num

lemma central_mass (r : ℝ) (hr : 0 ≤ r) :
    ∫ s, band r s ∂(gaussianReal 0 1) = 2 * cdf (gaussianReal 0 1) r - 1 := by
  let μ := gaussianReal 0 1
  have hsym : μ.map (fun s : ℝ => -s) = μ := by simp [μ, gaussianReal_map_neg]
  have ht : μ.real (Iio (-r)) = μ.real (Ioi r) := by
    calc μ.real (Iio (-r)) = (μ.map (fun s : ℝ => -s)).real (Iio (-r)) := by rw [hsym]
      _ = _ := by
        rw [measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iio, measureReal_def]
        congr 2
        ext s
        simp
  have hd : Disjoint (Iio (-r)) (Icc (-r) r) :=
    Set.disjoint_left.mpr fun _ h1 h2 => (not_lt_of_ge h2.1) h1
  have hu := measureReal_union (μ := μ) hd measurableSet_Icc
  rw [Iio_union_Icc_eq_Iic (by linarith : -r ≤ r), ht] at hu
  have hc := measureReal_add_measureReal_compl (μ := μ) (measurableSet_Iic (a := r))
  rw [compl_Iic] at hc
  change _ = 2 * cdf μ r - 1
  rw [cdf_eq_real]
  have eqb : band r = (Icc (-r) r).indicator (1 : ℝ → ℝ) := by
    funext s
    simp only [band, Set.indicator, Set.mem_Icc, abs_le, Pi.one_apply]
  rw [eqb, integral_indicator_one measurableSet_Icc]
  change μ.real (Icc (-r) r) = _
  have hone : μ.real Set.univ = 1 := by simp [μ]
  linarith

lemma weighted_mass (r : ℝ) (hr : 0 ≤ r) :
    ∫ s : ℝ, |s| * band r s ∂(gaussianReal 0 1) =
      ABPOnline.cG * (1 - Real.exp (-(r ^ 2 / 2))) := by
  let w := fun t : ℝ => t * Real.exp (-(t ^ 2 / 2))
  have hw : Continuous w := by dsimp [w]; fun_prop
  have dw (t : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-(t ^ 2 / 2))) (w t) t := by
    convert! (((hasDerivAt_pow 2 t).div_const 2).neg.exp.neg) using 1 <;> dsimp [w] <;> ring
  have hfront : (∫ t in Set.Ioi (0 : ℝ), (Set.Iic r).indicator w t) =
      1 - Real.exp (-(r ^ 2 / 2)) := by
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.inter_comm, Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le hr,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => dw t) (hw.intervalIntegrable _ _)]
    simp; ring
  have hfun (s : ℝ) : gaussianPDFReal 0 1 s • (|s| * band r s) =
      (Real.sqrt (2 * Real.pi))⁻¹ * (Set.Iic r).indicator w |s| := by
    by_cases hs : |s| ≤ r
    · rw [Set.indicator_of_mem (show |s| ∈ Set.Iic r from hs)]
      simp only [band, if_pos hs, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
        w, sq_abs]
      ring
    · rw [Set.indicator_of_notMem (show |s| ∉ Set.Iic r from hs)]
      simp [band, hs]
  have hconst : (Real.sqrt (2 * π))⁻¹ * 2 = ABPOnline.cG := by
    unfold ABPOnline.cG
    have hpos : 0 < Real.sqrt (2 * π) := by positivity
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * π)
    have hs' := Real.sq_sqrt (by positivity : 0 ≤ 2 / π)
    rw [← div_eq_inv_mul, div_eq_iff hpos.ne']
    nlinarith [Real.sqrt_nonneg (2 / π), mul_nonneg (Real.sqrt_nonneg (2 / π)) hpos.le,
      show (Real.sqrt (2 / π) * Real.sqrt (2 * π)) ^ 2 = 4 by
        rw [mul_pow, hs, hs']; field_simp <;> ring]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [hfun, integral_const_mul]
  rw [integral_comp_abs, hfront, ← mul_assoc, hconst]

end GaussianBand

end

section

open GrothendieckLB MeasureTheory ProbabilityTheory Real Set Filter
namespace GaussianBand

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {w : Ω → ℝ} (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) : Integrable w μ :=
  memLp_one_iff_integrable.mp (MemLp.of_bound hw.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z))

theorem bathtub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S w : Ω → ℝ} (hS : Measurable S) (hlaw : HasLaw S (gaussianReal 0 1) μ)
    (hw : Measurable w) (hb : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (budget : ∫ z, |S z| * w z ∂μ ≤ ABPOnline.cG * (1 - x)) :
    ∫ z, w z ∂μ ≤ Pfun x := by
  have hwb (z) : ‖w z‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hb z).1]; exact (hb z).2
  have hwi : Integrable w μ := bounded_integrable hw hwb
  have hSi : Integrable (fun z => |S z|) μ :=
    (hlaw.measurePreserving hS).integrable_comp_of_integrable
      (show Integrable (fun s : ℝ => |s|) (gaussianReal 0 1) from IsGaussian.integrable_id.abs)
  have hWS := hSi.mul_bdd hw.aestronglyMeasurable (Eventually.of_forall hwb)
  let r := Real.sqrt (-2 * Real.log x)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = -2 * Real.log x :=
    Real.sq_sqrt (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (Real.log_nonpos hx.le hx1))
  have he : Real.exp (-(r ^ 2 / 2)) = x := by
    rw [hr2, show -(-2 * Real.log x / 2) = Real.log x by ring, Real.exp_log hx]
  let b := fun z => band r (S z)
  have hbm : Measurable b := (measurable_band r).comp hS
  have hbb (z) : ‖b z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (band_bound _ _).1]; exact (band_bound _ _).2
  have hbi : Integrable b μ := bounded_integrable hbm hbb
  have hBS := hSi.mul_bdd hbm.aestronglyMeasurable (Eventually.of_forall hbb)
  have hB : (∫ z, b z ∂μ) = Pfun x := by
    unfold Pfun
    rw [if_neg hx.ne']
    exact (hlaw.integral_comp (measurable_band r).aestronglyMeasurable).trans (central_mass r hr)
  have hBS' : (∫ z, |S z| * b z ∂μ) = ABPOnline.cG * (1 - x) := by
    rw [← he]
    exact (hlaw.integral_comp (measurable_abs.mul (measurable_band r)).aestronglyMeasurable).trans
      (weighted_mass r hr)
  by_cases hpos : 0 < r
  · have point (z) : r * w z - r * b z ≤ |S z| * w z - |S z| * b z := by
      have h : 0 ≤ (|S z| - r) * (w z - b z) := by
        by_cases hz : |S z| ≤ r
        · apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hz)
          simpa [b, band, hz] using (sub_nonpos.mpr (hb z).2)
        · apply mul_nonneg (sub_nonneg.mpr (le_of_not_ge hz))
          simpa [b, band, hz] using (hb z).1
      linarith
    have hi := integral_mono ((hwi.const_mul r).sub (hbi.const_mul r)) (hWS.sub hBS) point
    simp only [Pi.sub_apply] at hi
    rw [integral_sub (hwi.const_mul r) (hbi.const_mul r), integral_sub hWS hBS,
      integral_const_mul, integral_const_mul, hB, hBS'] at hi
    exact (mul_le_mul_iff_right₀ hpos).mp (by linarith only [hi, budget])
  · have hr0 := le_antisymm (le_of_not_gt hpos) hr
    have hx' : x = 1 := by rw [← he, hr0]; norm_num
    rw [hx'] at budget
    have hIntZero : (∫ z, |S z| * w z ∂μ) = 0 := le_antisymm
      (by linarith only [budget]) (integral_nonneg fun z => mul_nonneg (abs_nonneg _) (hb z).1)
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun z => mul_nonneg (abs_nonneg (S z)) (hb z).1) hWS).mp hIntZero
    letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    have hne : ∀ᵐ z ∂μ, S z ≠ 0 := (hlaw.ae_iff (p := fun s => s ≠ 0)
      (measurableSet_setOfPred.mp (measurableSet_singleton (0 : ℝ)).compl)).mpr
        ((gaussianReal 0 1).ae_ne 0)
    have hw0 : w =ᵐ[μ] 0 := by
      filter_upwards [hae, hne] with z hz hNz
      exact (mul_eq_zero.mp hz).resolve_left (abs_ne_zero.mpr hNz)
    rw [integral_congr_ae hw0, ← hB]
    simp only [Pi.zero_apply, integral_zero]
    exact integral_nonneg fun z => (band_bound _ _).1

end GaussianBand

end

section

open MeasureTheory ProbabilityTheory Real Filter Finset GrothendieckLB KG

namespace DisagreementBounds

noncomputable abbrev prodGauss (d : ℕ) := Measure.pi fun _ : Fin d => gaussianReal 0 1

lemma gaussExp_eq {d : ℕ} (F : (Fin d → ℝ) → ℝ) :
    gaussExp F = ∫ z, F z ∂(prodGauss d) := by
  change (∫ z, F z * phiK d z) = _
  simp_rw [mul_comm (F _) (phiK _ _)]
  exact integral_phiK d F

lemma aligned_direction {d : ℕ} (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1) (hα : 0 < p1Norm h) :
    ∃ v : Fin d → ℝ, (∑ i, v i ^ 2 = 1) ∧
      (∫ z, h z * proj v z ∂(prodGauss d)) = p1Norm h := by
  let α := p1Norm h
  have hαsq : α ^ 2 = ∑ i, mom1 h i * mom1 h i :=
    Real.sq_sqrt (sum_nonneg fun i _ => mul_self_nonneg _)
  let v : Fin d → ℝ := fun i => mom1 h i / α
  have hv : ∑ i, v i ^ 2 = 1 := by
    simp only [v, div_pow, ← sum_div]
    rw [div_eq_one_iff_eq (pow_ne_zero _ hα.ne'), hαsq]
    exact sum_congr rfl fun i _ => sq _
  have hva : ∑ i, v i * mom1 h i = α := by
    simp only [v, div_mul_eq_mul_div, ← sum_div]
    rw [← hαsq]; field_simp
  refine ⟨v, hv, ?_⟩
  change _ = α
  rw [← hva, sum_mom1_eq h hm hb, ← gaussExp_eq]
  simp only [pow_one]
  rfl

lemma sign_budget {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g)
    (v : Fin d → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    (∫ z, |proj v z| * disagreePart f g z ^ 2 ∂(prodGauss d)) +
      (∫ z, agreePart f g z * proj v z ∂(prodGauss d)) ≤ ABPOnline.cG := by
  let μ := prodGauss d
  let S := proj v
  let h := agreePart f g
  let w := fun z => disagreePart f g z ^ 2
  have hS : Measurable S := measurable_proj v
  have hlaw : HasLaw S (gaussianReal 0 1) μ := ⟨hS.aemeasurable, proj_law d v hv⟩
  have hm : Measurable h := (hf.1.add hg.1).div_const 2
  have wm : Measurable w := ((hf.1.sub hg.1).div_const 2).pow_const _
  have hsign (z) : |h z| + w z = 1 ∧ |h z| ≤ 1 ∧ 0 ≤ w z ∧ w z ≤ 1 := by
    rcases hf.2 z with hf' | hf' <;> rcases hg.2 z with hg' | hg' <;>
      norm_num [h, w, agreePart, disagreePart, hf', hg']
  have hSi : Integrable S μ := (hlaw.measurePreserving hS).integrable_comp_of_integrable
    (IsGaussian.integrable_id : Integrable id (gaussianReal 0 1))
  have hWS := hSi.abs.mul_bdd wm.aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hsign z).2.2.1]
      using (hsign z).2.2.2)
  have hHS := hSi.bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall fun z => (hsign z).2.1)
  change (∫ z, |S z| * w z ∂μ) + (∫ z, h z * S z ∂μ) ≤ _
  rw [← integral_add hWS hHS]
  calc _ ≤ ∫ z, |S z| ∂μ := by
              apply integral_mono (hWS.add hHS) hSi.abs
              intro z
              have hm' := le_abs_self (h z * S z)
              rw [abs_mul] at hm'
              have h' := congrArg (fun t => t * |S z|) (hsign z).1
              change |S z| * w z + h z * S z ≤ |S z|
              nlinarith only [hm', h']
    _ = ABPOnline.cG := (hlaw.integral_comp measurable_abs.aestronglyMeasurable).trans gauss_abs_one

end DisagreementBounds

open DisagreementBounds

theorem solution {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    p3NormSq (disagreePart f g) ≤ Pfun (p1Norm (agreePart f g) / ABPOnline.cG) := by
  let h := agreePart f g
  let k := disagreePart f g
  let α := p1Norm h
  let ν := ABPOnline.cG
  have hν : 0 < ν := Real.sqrt_pos.mpr (by positivity)
  have hm : Measurable h := (hf.1.add hg.1).div_const 2
  have km : Measurable k := (hf.1.sub hg.1).div_const 2
  have kbm (z) : |h z| ≤ 1 ∧ |k z| ≤ 1 ∧ k z ^ 2 ≤ 1 := by
    rcases hf.2 z with hf' | hf' <;> rcases hg.2 z with hg' | hg' <;>
      norm_num [h, k, disagreePart, agreePart, hf', hg']
  have bes := CubicChaos.cubic_bessel k km fun z => (kbm z).2.1
  rw [gaussExp_eq] at bes
  let w := fun z => k z ^ 2
  have wm : Measurable w := km.pow_const 2
  have wb (z) : 0 ≤ w z ∧ w z ≤ 1 := ⟨sq_nonneg _, (kbm z).2.2⟩
  apply bes.trans
  change (∫ z, w z ∂(prodGauss d)) ≤ Pfun (α / ν)
  by_cases hz : α = 0
  · rw [hz, zero_div, Pfun, if_pos rfl]
    have wi : Integrable w (prodGauss d) := GaussianBand.bounded_integrable wm
      (fun z => by rw [abs_of_nonneg (wb z).1]; exact (wb z).2)
    simpa using integral_mono (g := fun _ => (1 : ℝ)) wi (integrable_const 1) (fun z => (wb z).2)
  · have hα : 0 < α := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    obtain ⟨v, hv, ha⟩ := aligned_direction h hm (fun z => (kbm z).1) hα
    have hs := sign_budget hf hg v hv
    change (∫ z, |proj v z| * w z ∂(prodGauss d)) +
      (∫ z, h z * proj v z ∂(prodGauss d)) ≤ ν at hs
    rw [ha] at hs
    change (∫ z, |proj v z| * w z ∂(prodGauss d)) + α ≤ ν at hs
    have hbudget0 : 0 ≤ ∫ z, |proj v z| * w z ∂(prodGauss d) := integral_nonneg fun z => mul_nonneg (abs_nonneg (proj v z)) (wb z).1
    have hx1 : α / ν ≤ 1 := (div_le_one hν).mpr (by linarith only [hs, hbudget0])
    apply GaussianBand.bathtub (measurable_proj v) ⟨(measurable_proj v).aemeasurable, proj_law d v hv⟩
      wm wb (α / ν) (div_pos hα hν) hx1
    have he : ν * (1 - α / ν) = ν - α := by field_simp
    change _ ≤ ν * (1 - α / ν)
    rw [he]
    linarith only [hs]

end
