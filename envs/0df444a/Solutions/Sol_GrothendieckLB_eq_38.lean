-- Prove2me | solution 1 for GrothendieckLB.eq_38
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:19:58.342983+00:00
-- url     : https://prove2.me/submissions/13cb43e3-309a-407d-a96f-8d6f936b164d

import Mathlib
import Definitions.Def_GrothendieckLB_IsTernaryFn
import Definitions.Def_GrothendieckLB_p3NormSq
import Definitions.Def_GrothendieckLB_gaussExp
import Definitions.Def_GrothendieckLB_V
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

open Finset

/-- `H3 x i j l = x_i x_j x_l - δ_ij x_l - δ_il x_j - δ_jl x_i`. -/
def H3 {k : ℕ} (x : Fin k → ℝ) (i j l : Fin k) : ℝ :=
  x i * x j * x l - (if i = j then x l else 0) - (if i = l then x j else 0)
    - (if j = l then x i else 0)

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


end CubicChaos

end

section

open GrothendieckLB CubicChaos KG MeasureTheory ProbabilityTheory Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian
open scoped RealInnerProductSpace

namespace FiberChaos

noncomputable abbrev G (d : ℕ) := Measure.pi fun _ : Fin d => gaussianReal 0 1

lemma gauss_eq {d : ℕ} (F : (Fin d → ℝ) → ℝ) :
    gaussExp F = ∫ z, F z ∂(G d) := by
  change (∫ z, F z * phiK d z) = _
  simp_rw [mul_comm (F _) (phiK _ _)]
  exact integral_phiK d F

noncomputable def coordH {d : ℕ} (κ : Fin d → ℕ) (z : Fin d → ℝ) :=
  hermite d κ (WithLp.toLp 2 z)
noncomputable def coef {d : ℕ} (u : (Fin d → ℝ) → ℝ) (κ : Fin d → ℕ) :=
  gaussExp (fun z => u z * coordH κ z)

lemma coordH_meas {d : ℕ} (κ : Fin d → ℕ) : Measurable (coordH κ) := by
  unfold coordH hermite AMPLowDeg.RankOne.hermNorm
  fun_prop

lemma coordH_int {d : ℕ} (κ : Fin d → ℕ) : Integrable (coordH κ) (G d) := by
  letI : IsProbabilityMeasure (gaussian d) := (inferInstance : IsProbabilityMeasure (stdGaussian (Vec d)))
  have hp : MeasurePreserving (WithLp.toLp 2) (G d) (gaussian d) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact hp.integrable_comp_of_integrable (((lemma_B_8 d).2.1 κ).integrable (by norm_num))

lemma exp_to_vec {d : ℕ} (F : Vec d → ℝ) (hm : Measurable F) :
    gaussExp (fun z => F (WithLp.toLp 2 z)) = ∫ z, F z ∂(gaussian d) := by
  have hl : HasLaw (WithLp.toLp 2) (gaussian d) (G d) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact (gauss_eq _).trans (hl.integral_comp hm.aestronglyMeasurable)

theorem coeffs_bessel {d : ℕ} (u : (Fin d → ℝ) → ℝ) (C : ℝ)
    (hu : Measurable u) (ub : ∀ z, |u z| ≤ C) (s : Finset (Fin d → ℕ)) :
    ∑ κ ∈ s, coef u κ ^ 2 ≤ gaussExp (fun z => u z ^ 2) := by
  classical
  let U : Vec d → ℝ := fun z => u (WithLp.ofLp z)
  have hU : Measurable U := hu.comp (by fun_prop)
  let μ := gaussian d
  letI : IsProbabilityMeasure μ := (inferInstance : IsProbabilityMeasure (stdGaussian (Vec d)))
  have hU2 : MemLp U 2 μ := MemLp.of_bound hU.aestronglyMeasurable C
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
    rw [exp_to_vec (fun z => U z * hermite d κ z) (hU.mul (hherm κ))]
    change ⟪b κ, X⟫ = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hb κ, hX] with z hz hzx
    rw [hz, hzx]
    rfl
  have hNorm : ‖X‖ ^ 2 = gaussExp (fun z => u z ^ 2) := by
    rw [exp_to_vec (fun z => U z ^ 2) (hU.pow_const _),
      ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hX] with z hz
    rw [hz]
    simp [sq, U]
  have hB := b.orthonormal.sum_inner_products_le X (s := s)
  change (∑ κ ∈ s, ‖A κ‖ ^ 2) ≤ _ at hB
  simpa only [Real.norm_eq_abs, sq_abs, hA, hNorm, coef, coordH] using hB

theorem p3_expansion {d : ℕ} (u : (Fin d → ℝ) → ℝ) :
    p3NormSq u = ∑ κ ∈ univ.image (counts (n := 3) (d := d)), coef u κ ^ 2 := by
  classical
  have hcoeff (p : Fin 3 → Fin d) :
      cubicMoment u (p 0) (p 1) (p 2) = factor (counts p) * coef u (counts p) := by
    change (∫ z, u z * H3 z (p 0) (p 1) (p 2) * phiK d z) = _
    rw [coef, gaussExp, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    change u z * H3 z (p 0) (p 1) (p 2) * phiK d z = _
    rw [tensor_basis p]
    change u z * (factor _ * _) * phiK d z = factor _ * (u z * _ * phiK d z)
    unfold coordH
    ring
  have hsum :
      ∑ p : Fin 3 → Fin d, cubicMoment u (p 0) (p 1) (p 2) * cubicMoment u (p 0) (p 1) (p 2) =
      6 * ∑ κ ∈ univ.image (counts (n := 3) (d := d)), coef u κ ^ 2 := by
    have h6 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    simpa only [hcoeff, ← sq, mul_pow, factor_sq, h6] using
      (weighted_sum (n := 3) (d := d) (fun κ => coef u κ ^ 2))
  rw [sum_triples (B := fun i j l => cubicMoment u i j l * cubicMoment u i j l)] at hsum
  unfold p3NormSq p3Inner
  linarith only [hsum]

end FiberChaos

end

section

open MeasureTheory ProbabilityTheory GrothendieckLB KG FiberChaos Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian

namespace FiberChaos

lemma cons_preserving (n : ℕ) : MeasurePreserving
    (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2)
    ((gaussianReal 0 1).prod (G n)) (G (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).symm
  have he : (fun p : ℝ × (Fin n → ℝ) => e.symm p) = fun p => Fin.cons p.1 p.2 := by
    funext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  rw [← he]
  exact hm

lemma integral_cons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} (hm : Measurable F)
    (hi : Integrable F (G (n+1))) :
    (∫ z, F z ∂(G (n+1))) = ∫ t, ∫ s, F (Fin.cons s t) ∂(gaussianReal 0 1) ∂(G n) := by
  let c : ℝ × (Fin n → ℝ) → (Fin (n+1) → ℝ) := fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2
  have hp := cons_preserving n
  have law : HasLaw c (G (n+1)) ((gaussianReal 0 1).prod (G n)) :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  exact (law.integral_comp hm.aestronglyMeasurable).symm.trans
    (integral_prod_symm (F ∘ c) (hp.integrable_comp_of_integrable hi))

lemma stdExp_eq (F : ℝ → ℝ) : stdExp F = ∫ s, F s ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  unfold stdExp
  simp only [smul_eq_mul]
  exact integral_congr_ae (Eventually.of_forall fun s => mul_comm _ _)

lemma he_eq_normalized (j : Fin 4) (s : ℝ) : he j s = AMPLowDeg.RankOne.hermNorm j.val s := by
  fin_cases j <;> norm_num [he, AMPLowDeg.RankOne.hermNorm, Polynomial.hermite,
    Polynomial.derivative_mul, Nat.factorial] <;> ring

lemma he_meas (j : Fin 4) : Measurable (he j) := by
  simp_rw [funext (he_eq_normalized j)]
  unfold AMPLowDeg.RankOne.hermNorm; fun_prop

lemma he_int (j : Fin 4) : Integrable (he j) (gaussianReal 0 1) := by
  let μ := gaussianReal 0 1
  have T := (measurePreserving_funUnique μ (Fin 1)).symm.integrable_comp_of_integrable
    (coordH_int (d := 1) (fun _ => j.val))
  apply T.congr
  exact Eventually.of_forall fun s => by
    simpa [Function.comp_def, coordH, hermite, Fintype.prod_unique] using (he_eq_normalized j s).symm

lemma product_cons {n : ℕ} (j : Fin 4) (κ : Fin n → ℕ) (s : ℝ) (t : Fin n → ℝ) :
    coordH (Fin.cons j.val κ) (Fin.cons s t) = he j s * coordH κ t := by
  unfold coordH hermite
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, he_eq_normalized]

noncomputable def fiber {n : ℕ} (k : (Fin (n+1) → ℝ) → ℝ) (j : Fin 4) (t : Fin n → ℝ) :=
  ∫ s, k (Fin.cons s t) * he j s ∂(gaussianReal 0 1)

lemma measurable_fiber {n : ℕ} {k : (Fin (n+1) → ℝ) → ℝ} (hm : Measurable k) (j : Fin 4) :
    Measurable (fiber k j) := by
  have h : Measurable (fun p : ℝ × (Fin n → ℝ) => k (Fin.cons p.1 p.2) * he j p.1) :=
    (hm.comp (cons_preserving n).measurable).mul ((he_meas j).comp measurable_fst)
  exact (h.stronglyMeasurable.integral_prod_left' (μ := gaussianReal 0 1)).measurable

lemma fiber_bound {n : ℕ} {k : (Fin (n+1) → ℝ) → ℝ} (hm : Measurable k)
    (hb : ∀ z, |k z| ≤ 1) (j : Fin 4) (t : Fin n → ℝ) :
    |fiber k j t| ≤ ∫ s, |he j s| ∂(gaussianReal 0 1) := by
  have hst : Measurable (fun s => k (Fin.cons s t)) :=
    hm.comp ((cons_preserving n).measurable.comp (measurable_id.prodMk measurable_const))
  have hi := (he_int j).bdd_mul hst.aestronglyMeasurable
    (Eventually.of_forall fun s => hb (Fin.cons s t))
  calc _ ≤ ∫ s, ‖k (Fin.cons s t) * he j s‖ ∂(gaussianReal 0 1) := norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono hi.norm (he_int j).abs (fun s => by
      simp only [Real.norm_eq_abs, abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hb (Fin.cons s t)) (abs_nonneg (he j s)))

lemma coeff_cons {n : ℕ} {k : (Fin (n+1) → ℝ) → ℝ} (hm : Measurable k)
    (hb : ∀ z, |k z| ≤ 1) (j : Fin 4) (κ : Fin n → ℕ) :
    coef k (Fin.cons j.val κ) = coef (fiber k j) κ := by
  let κ' : Fin (n+1) → ℕ := Fin.cons j.val κ
  have hi := (coordH_int κ').bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hb)
  unfold coef
  rw [gauss_eq, gauss_eq, integral_cons (F := fun z => k z * coordH (Fin.cons j.val κ) z)
    (hm.mul (coordH_meas κ')) hi]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change (∫ s, k (Fin.cons s t) * coordH (Fin.cons j.val κ) (Fin.cons s t) ∂(gaussianReal 0 1)) =
    (∫ s, k (Fin.cons s t) * he j s ∂(gaussianReal 0 1)) * coordH κ t
  simp_rw [product_cons, ← mul_assoc]
  exact integral_mul_const _ _

end FiberChaos

end

section

open GrothendieckLB FiberChaos CubicChaos MeasureTheory ProbabilityTheory Filter Finset

private theorem sum_split {n : ℕ} (I : Finset (Fin (n+1) → ℕ)) (hx : ∀ κ ∈ I, κ 0 < 4)
    (F : (Fin (n+1) → ℕ) → ℝ) (hF : ∀ κ, 0 ≤ F κ) :
    ∑ κ ∈ I, F κ ≤ ∑ j : Fin 4, ∑ τ ∈ I.image Fin.tail, F (Fin.cons j.val τ) := by
  classical
  let T := I.image Fin.tail
  let J := (univ : Finset (Fin 4)).product T
  let join : Fin 4 × (Fin n → ℕ) → (Fin (n+1) → ℕ) := fun p : Fin 4 × (Fin n → ℕ) => Fin.cons p.1.val p.2
  have sub : I ⊆ J.image join := by
    intro κ hκ
    let j : Fin 4 := ⟨κ 0, hx κ hκ⟩
    refine mem_image.mpr ⟨(j, Fin.tail κ), mem_product.mpr ⟨mem_univ _, mem_image_of_mem _ hκ⟩, ?_⟩
    exact Fin.cons_self_tail κ
  have inj : Function.Injective join := by
    rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    apply Prod.ext
    · exact Fin.ext (congrFun h 0)
    · exact funext fun i => by simpa [join] using congrFun h i.succ
  calc ∑ κ ∈ I, F κ ≤ ∑ κ ∈ J.image join, F κ :=
          sum_le_sum_of_subset_of_nonneg sub (fun x _ _ => hF x)
    _ = ∑ p ∈ J, F (join p) := sum_image (fun _ _ _ _ h => inj h)
    _ = _ := Finset.sum_product (univ : Finset (Fin 4)) T (fun p => F (join p))

theorem solution {n : ℕ} {k : (Fin (n + 1) → ℝ) → ℝ} (hk : IsTernaryFn k) :
    p3NormSq k ≤ gaussExp fun t : Fin n → ℝ => V fun s => k (Fin.cons s t) := by
  classical
  have hb (z) : |k z| ≤ 1 := by rcases hk.2 z with h | h | h <;> norm_num [h]
  let I := univ.image (counts (n := 3) (d := n+1))
  let T := I.image Fin.tail
  have hH (κ) (hκ : κ ∈ I) : κ 0 < 4 := by
    obtain ⟨p, _, rfl⟩ := mem_image.mp hκ
    have hle : counts p 0 ≤ Fintype.card (Fin 3) := Fintype.card_subtype_le _
    simpa using (Nat.lt_succ_of_le hle)
  have hfmi (j : Fin 4) : MemLp (fiber k j) 2 (G n) :=
    MemLp.of_bound (measurable_fiber hk.1 j).aestronglyMeasurable _
      (Eventually.of_forall fun t => fiber_bound hk.1 hb j t)
  rw [p3_expansion, gauss_eq]
  calc ∑ κ ∈ I, coef k κ ^ 2 ≤ ∑ j : Fin 4, ∑ τ ∈ T, coef k (Fin.cons j.val τ) ^ 2 :=
            sum_split I hH _ (fun _ => sq_nonneg _)
    _ ≤ ∑ j : Fin 4, ∫ t, fiber k j t ^ 2 ∂(G n) := by
            refine sum_le_sum fun j _ => ?_
            simp only [coeff_cons hk.1 hb]
            exact (coeffs_bessel (fiber k j) _ (measurable_fiber hk.1 j) (fiber_bound hk.1 hb j) T).trans_eq
              (gauss_eq _)
    _ = ∫ t, V (fun s => k (Fin.cons s t)) ∂(G n) := by
            rw [← integral_finsetSum _ fun j _ => (hfmi j).integrable_sq]
            refine integral_congr_ae (Eventually.of_forall fun t => ?_)
            unfold V
            simp only [stdExp_eq, fiber]

end
