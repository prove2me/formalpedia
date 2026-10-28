-- Prove2me | solution 1 for OAI.LogBrunnMinkowski.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:16:19.913981+00:00
-- url     : https://prove2.me/submissions/e7c09a8d-363e-4f72-97b2-f054529e790b

import Mathlib
import Definitions.Def_LogBrunnMinkowski
import Definitions.Def_OAIW2LB000
import Theorems.Thm_OAI_LogBrunnMinkowski_softVariance

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Real

open MeasureTheory
open scoped Topology

open MeasureTheory FourierTransform Convolution
open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology

open MeasureTheory TemperedDistribution FourierTransform LineDeriv
open scoped SchwartzMap ContDiff

open Filter Function
open scoped SchwartzMap Topology ContDiff

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology ContDiff

open MeasureTheory
open scoped Topology ContDiff

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

open scoped ContDiff Topology

open Matrix
open scoped BigOperators Kronecker

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace GaussianPolynomial
section
variable {ι : Type*} [Fintype ι]

lemma gaussian_product (b : ℝ) (x : ι → ℝ) :
    Real.exp (-b * ∑ i, x i ^ 2) = ∏ i, Real.exp (-b * x i ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

lemma monomial_integrable {b : ℝ} (hb : 0 < b) (d : ι → ℕ) :
    Integrable (fun x : ι → ℝ => (∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2)) := by
  have hi (i : ι) : Integrable (fun x : ℝ => x ^ d i * Real.exp (-b * x^2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq hb (by have := Nat.cast_nonneg (α := ℝ) (d i); linarith : (-1:ℝ) < (d i : ℝ))
  have hp := Integrable.fintype_prod hi
  have he : (fun x : ι → ℝ => (∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2)) =
      (fun x : ι → ℝ => ∏ i, x i ^ d i * Real.exp (-b * x i^2)) := by
    funext x
    rw [gaussian_product, Finset.prod_mul_distrib]
  rw [he]
  exact hp

lemma polynomial_integrable {b : ℝ} (hb : 0 < b) (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P * Real.exp (-b * ∑ i, x i^2)) := by
  have hi : Integrable (fun x : ι → ℝ => ∑ d ∈ P.support,
      P.coeff d * ((∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2))) := by
    exact integrable_finsetSum _ (fun d _ => (monomial_integrable hb d).const_mul _)
  convert hi using 1
  funext x
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

lemma dominated_polynomial {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x)
    (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P * Real.exp (-V x)) := by
  have hmaj := (polynomial_integrable hb P).norm.const_mul (Real.exp c)
  apply hmaj.mono' (((MvPolynomial.continuous_eval P).mul (Real.continuous_exp.comp hV.neg)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖MvPolynomial.eval x P * Real.exp (-V x)‖ ≤
    Real.exp c * ‖MvPolynomial.eval x P * Real.exp (-b * ∑ i, x i^2)‖
  simp only [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-V x) ≤ Real.exp c * Real.exp (-b * ∑ i, x i^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hlower x]
  calc
    _ ≤ ‖MvPolynomial.eval x P‖ * (Real.exp c * Real.exp (-b * ∑ i, x i^2)) :=
      mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = _ := by ring

end

open MeasureTheory

end GaussianPolynomial

end

open scoped BigOperators InnerProductSpace Topology

end
section


open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LogBrunnMinkowski

lemma body_nonempty {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K) :
    K.Nonempty := hK.2.2.mono interior_subset

lemma support_attained {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (u : Space n) : ∃ x ∈ K, ⟪x, u⟫_ℝ = support K u := by
  have hc : Continuous (fun x : Space n => ⟪x, u⟫_ℝ) :=
    continuous_id.inner continuous_const
  exact (hK.1.image hc).sSup_mem ((body_nonempty hK).image _)

lemma inner_le_support {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    {x : Space n} (hx : x ∈ K) (u : Space n) : ⟪x, u⟫_ℝ ≤ support K u := by
  apply le_csSup
  · exact hK.1.bddAbove_image (continuous_id.inner continuous_const).continuousOn
  · exact mem_image_of_mem _ hx

lemma support_le_iff {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (u : Space n) (a : ℝ) : support K u ≤ a ↔ ∀ x ∈ K, ⟪x, u⟫_ℝ ≤ a := by
  constructor
  · intro h x hx
    exact (inner_le_support hK hx u).trans h
  · intro h
    exact csSup_le ((body_nonempty hK).image _) (by
      rintro y ⟨x, hx, rfl⟩
      exact h x hx)

lemma support_zero {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K) :
    support K 0 = 0 := by
  obtain ⟨x, hx, h⟩ := support_attained hK 0
  simpa using h.symm

lemma support_smul {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (u : Space n) {a : ℝ} (ha : 0 ≤ a) : support K (a • u) = a * support K u := by
  apply le_antisymm
  · apply (support_le_iff hK _ _).2
    intro x hx
    simpa only [inner_smul_right] using mul_le_mul_of_nonneg_left
      (inner_le_support hK hx u) ha
  · obtain ⟨x, hx, h⟩ := support_attained hK u
    have h' := inner_le_support hK hx (a • u)
    simpa only [inner_smul_right, h] using h'

lemma interior_neg_mem {n : ℕ} {K : Set (Space n)} (hK : OriginSymmetric K)
    {x : Space n} (hx : x ∈ interior K) : -x ∈ interior K := by
  have hsub : (fun y : Space n => -y) ⁻¹' interior K ⊆ interior K := by
    apply interior_maximal
    · intro y hy
      exact (hK y).mpr (interior_subset hy)
    · exact isOpen_interior.preimage continuous_neg
  apply hsub
  simpa only [mem_preimage, neg_neg] using hx

lemma zero_mem_interior {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (hsK : OriginSymmetric K) : (0 : Space n) ∈ interior K := by
  obtain ⟨x, hx⟩ := hK.2.2
  have h := hK.2.1.interior hx (interior_neg_mem hsK hx)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa only [smul_neg, add_neg_cancel] using h

lemma positive_support {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (hsK : OriginSymmetric K) {u : Space n} (hu : ‖u‖ = 1) : 0 < support K u := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 (zero_mem_interior hK hsK)
  have hru : (r / 2) • u ∈ Metric.ball (0 : Space n) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  have h := inner_le_support hK (interior_subset (hball hru)) u
  have huu : ⟪u,u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  rw [inner_smul_left, huu] at h
  norm_num at h
  exact lt_of_lt_of_le (by positivity : 0 < r / 2) h

lemma mem_wulff_support_iff {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (x : Space n) : x ∈ wulff (support K) ↔ x ∈ K := by
  constructor
  · intro hx
    by_contra hnot
    obtain ⟨f, a, hf, hfx⟩ := geometric_hahn_banach_closed_point hK.2.1 hK.1.isClosed hnot
    let u := (InnerProductSpace.toDual ℝ (Space n)).symm f
    have hu : ∀ y, ⟪y,u⟫_ℝ = f y := by
      intro y
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hsep : support K u < ⟪x,u⟫_ℝ := by
      obtain ⟨y, hy, heq⟩ := support_attained hK u
      rw [← heq, hu, hu]
      exact (hf y hy).trans hfx
    have hune : u ≠ 0 := by
      intro hz
      simp only [hz, support_zero hK, inner_zero_right, lt_self_iff_false] at hsep
    have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hune
    have hv : ‖‖u‖⁻¹ • u‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
        inv_mul_cancel₀ hnorm.ne']
    have hbound := hx (‖u‖⁻¹ • u) hv
    rw [inner_smul_right, support_smul hK u (le_of_lt (inv_pos.mpr hnorm))] at hbound
    have hp : 0 < ‖u‖⁻¹ := inv_pos.mpr hnorm
    nlinarith
  · intro hx u _
    exact inner_le_support hK hx u

lemma wulff_support {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K) :
    wulff (support K) = K := by
  ext x
  exact mem_wulff_support_iff hK x

lemma body_volume_ne_top {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K) :
    volume K ≠ ⊤ := hK.1.measure_ne_top

lemma support_continuous {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K) :
    Continuous (support K) := by
  exact hK.1.continuous_sSup (continuous_snd.inner continuous_fst)

lemma support_neg {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (hsK : OriginSymmetric K) (u : Space n) : support K (-u) = support K u := by
  apply le_antisymm
  · apply (support_le_iff hK _ _).2
    intro x hx
    simpa only [inner_neg_left, inner_neg_right] using
      inner_le_support hK ((hsK x).mp hx) u
  · apply (support_le_iff hK _ _).2
    intro x hx
    simpa only [inner_neg_left, inner_neg_right, neg_neg] using
      inner_le_support hK ((hsK x).mp hx) (-u)

lemma unitSphere_nonempty {n : ℕ} (hn : 1 ≤ n) : Nonempty (UnitSphere n) := by
  let i : Fin n := ⟨0, hn⟩
  exact ⟨⟨EuclideanSpace.basisFun (Fin n) ℝ i,
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i⟩⟩

lemma finiteSlabs_closed {n : ℕ} (D : Finset (Space n)) (f : Space n → ℝ) :
    IsClosed (finiteSlabs D f) := by
  simp only [finiteSlabs, ofPred_forall]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_le (continuous_id.inner continuous_const).abs continuous_const

lemma finiteSlabs_compact {n : ℕ} (D : Finset (Space n)) (f : Space n → ℝ)
    (hD : ∀ i : Fin n, EuclideanSpace.basisFun (Fin n) ℝ i ∈ D) :
    IsCompact (finiteSlabs D f) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let box : Set (Fin n → ℝ) := {x | ∀ i, x i ∈ Icc (-f (b i)) (f (b i))}
  have hc : IsCompact box := isCompact_pi_infinite fun _ => isCompact_Icc
  apply ((PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr hc).of_isClosed_subset
    (finiteSlabs_closed D f)
  intro x hx i
  have hi := hx (b i) (hD i)
  rw [EuclideanSpace.inner_basisFun_real] at hi
  exact abs_le.mp hi

lemma basis_mem_directions {n : ℕ} (d : ℕ → UnitSphere n) (m : ℕ) (i : Fin n) :
    EuclideanSpace.basisFun (Fin n) ℝ i ∈ directions d m := by
  classical
  simp only [directions, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨i, rfl⟩

lemma dense_mem_directions {n : ℕ} (d : ℕ → UnitSphere n) (i : ℕ) :
    (d i).val ∈ directions d (i + 1) := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_self i), rfl⟩

lemma directions_unit {n : ℕ} (d : ℕ → UnitSphere n) (m : ℕ)
    {u : Space n} (hu : u ∈ directions d m) : ‖u‖ = 1 := by
  classical
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact (d i).property

lemma directions_mono {n : ℕ} (d : ℕ → UnitSphere n) : Monotone (directions d) := by
  classical
  intro i j hij
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.image_subset_image (Finset.range_mono hij))

lemma finiteSlabs_antitone {n : ℕ} (d : ℕ → UnitSphere n) (f : Space n → ℝ) :
    Antitone (fun m => finiteSlabs (directions d m) f) := by
  intro i j hij x hx u hu
  exact hx u (directions_mono d hij hu)

lemma iInter_finiteSlabs_eq_wulff {n : ℕ} {d : ℕ → UnitSphere n} (hd : DenseRange d)
    {f : Space n → ℝ} (hf : Continuous (fun u : UnitSphere n => f u.val))
    (heven : ∀ u, f (-u) = f u) :
    (⋂ m, finiteSlabs (directions d m) f) = wulff f := by
  ext x
  constructor
  · intro hx u hu
    have hclosed : IsClosed {u : UnitSphere n | |⟪x, u.val⟫_ℝ| ≤ f u.val} :=
      isClosed_le (continuous_const.inner continuous_subtype_val).abs hf
    have hall : ∀ u : UnitSphere n, |⟪x, u.val⟫_ℝ| ≤ f u.val := by
      intro u
      exact hd.induction_on u hclosed (fun i =>
        (mem_iInter.mp hx (i + 1)) (d i).val (dense_mem_directions d i))
    exact (le_abs_self _).trans (hall ⟨u, hu⟩)
  · intro hx
    apply mem_iInter.mpr
    intro m u hu
    have hunit := directions_unit d m hu
    apply abs_le.mpr
    constructor
    · have hneg := hx (-u) (by simpa using hunit)
      rw [inner_neg_right, heven] at hneg
      linarith
    · exact hx u hunit

lemma tendsto_volume_finiteSlabs {n : ℕ} {d : ℕ → UnitSphere n} (hd : DenseRange d)
    {f : Space n → ℝ} (hf : Continuous (fun u : UnitSphere n => f u.val))
    (heven : ∀ u, f (-u) = f u) :
    Filter.Tendsto (fun m => volume (finiteSlabs (directions d m) f)) Filter.atTop
      (nhds (volume (wulff f))) := by
  rw [← iInter_finiteSlabs_eq_wulff hd hf heven]
  exact tendsto_measure_iInter_atTop
    (fun m => (finiteSlabs_closed (directions d m) f).measurableSet.nullMeasurableSet)
    (finiteSlabs_antitone d f)
    ⟨0, (finiteSlabs_compact _ f (basis_mem_directions d 0)).measure_ne_top⟩

lemma interpolatedSupport_sphere_continuous {n : ℕ} {K L : Set (Space n)}
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L) (t : ℝ) :
    Continuous (fun u : UnitSphere n => interpolatedSupport K L t u.val) := by
  apply Continuous.mul
  · exact ((support_continuous hK).comp continuous_subtype_val).rpow_const
      (fun u => Or.inl (positive_support hK hsK u.property).ne')
  · exact ((support_continuous hL).comp continuous_subtype_val).rpow_const
      (fun u => Or.inl (positive_support hL hsL u.property).ne')

lemma interpolatedSupport_even {n : ℕ} {K L : Set (Space n)}
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L) (t : ℝ) (u : Space n) :
    interpolatedSupport K L t (-u) = interpolatedSupport K L t u := by
  simp only [interpolatedSupport, support_neg hK hsK, support_neg hL hsL]

lemma main_of_finite_slabs {n : ℕ} (hn : 1 ≤ n)
    {K L : Set (Space n)} (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hslabs : ∀ D : Finset (Space n),
      (∀ i : Fin n, EuclideanSpace.basisFun (Fin n) ℝ i ∈ D) →
      (∀ u ∈ D, ‖u‖ = 1) →
      volume (finiteSlabs D (support K)) ^ (1 - t) *
        volume (finiteSlabs D (support L)) ^ t ≤
          volume (finiteSlabs D (interpolatedSupport K L t))) :
    volume K ^ (1 - t) * volume L ^ t ≤ volume (logCombination K L t) := by
  let : Nonempty (UnitSphere n) := unitSphere_nonempty hn
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (UnitSphere n)
  have hKlim := tendsto_volume_finiteSlabs hd
    ((support_continuous hK).comp continuous_subtype_val) (support_neg hK hsK)
  have hLlim := tendsto_volume_finiteSlabs hd
    ((support_continuous hL).comp continuous_subtype_val) (support_neg hL hsL)
  rw [wulff_support hK] at hKlim
  rw [wulff_support hL] at hLlim
  have hTlim := tendsto_volume_finiteSlabs hd
    (interpolatedSupport_sphere_continuous hK hL hsK hsL t)
    (interpolatedSupport_even hK hL hsK hsL t)
  have hprod := ENNReal.Tendsto.mul (hKlim.ennrpow_const (1 - t))
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg ht0 (body_volume_ne_top hL)))
    (hLlim.ennrpow_const t)
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr ht1) (body_volume_ne_top hK)))
  exact le_of_tendsto_of_tendsto hprod hTlim
    (Filter.Eventually.of_forall (fun m => hslabs _ (basis_mem_directions d m)
      (fun _ hu => directions_unit d m hu)))

lemma oneDirection_norm : ‖oneDirection‖ = 1 := by
  simp [oneDirection]

lemma inner_oneDirection (x : Space 1) : ⟪x, oneDirection⟫_ℝ = oneEquiv x := by
  rw [← oneEquiv.inner_map_map]
  simp [oneDirection]

lemma sphere_one_cases {u : Space 1} (hu : ‖u‖ = 1) :
    u = oneDirection ∨ u = -oneDirection := by
  have habs : |oneEquiv u| = 1 := by rw [← Real.norm_eq_abs, oneEquiv.norm_map, hu]
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
  · left
    apply oneEquiv.injective
    simpa [oneDirection] using h
  · right
    apply oneEquiv.injective
    simpa [oneDirection] using h

lemma wulff_one_eq {f : Space 1 → ℝ} (heven : ∀ u, f (-u) = f u) :
    wulff f = oneEquiv ⁻¹' Icc (-f oneDirection) (f oneDirection) := by
  ext x
  constructor
  · intro hx
    have hp := hx oneDirection oneDirection_norm
    have hn := hx (-oneDirection) (by simpa using oneDirection_norm)
    rw [inner_oneDirection] at hp
    rw [inner_neg_right, inner_oneDirection, heven] at hn
    exact ⟨by linarith, hp⟩
  · intro hx u hu
    rcases sphere_one_cases hu with rfl | rfl
    · simpa only [inner_oneDirection] using hx.2
    · rw [inner_neg_right, inner_oneDirection, heven]
      linarith [hx.1]

lemma volume_wulff_one {f : Space 1 → ℝ} (heven : ∀ u, f (-u) = f u) :
    volume (wulff f) = ENNReal.ofReal (2 * f oneDirection) := by
  rw [wulff_one_eq heven,
    oneEquiv.measurePreserving.measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc]
  congr 1
  ring

lemma main_dimension_one {K L : Set (Space 1)}
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (logCombination K L t) = volume K ^ (1 - t) * volume L ^ t := by
  have ha := positive_support hK hsK oneDirection_norm
  have hb := positive_support hL hsL oneDirection_norm
  have hvK : volume K = ENNReal.ofReal (2 * support K oneDirection) := by
    conv_lhs => rw [← wulff_support hK]
    exact volume_wulff_one (support_neg hK hsK)
  have hvL : volume L = ENNReal.ofReal (2 * support L oneDirection) := by
    conv_lhs => rw [← wulff_support hL]
    exact volume_wulff_one (support_neg hL hsL)
  have hreal :
      (2 * support K oneDirection) ^ (1 - t) * (2 * support L oneDirection) ^ t =
        2 * (support K oneDirection ^ (1 - t) * support L oneDirection ^ t) := by
    rw [Real.mul_rpow (by norm_num) ha.le, Real.mul_rpow (by norm_num) hb.le]
    calc
      _ = ((2 : ℝ) ^ (1 - t) * 2 ^ t) *
          (support K oneDirection ^ (1 - t) * support L oneDirection ^ t) := by ring
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), sub_add_cancel,
        Real.rpow_one]
  change volume (wulff (interpolatedSupport K L t)) = _
  rw [volume_wulff_one (interpolatedSupport_even hK hL hsK hsL t), hvK, hvL,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (sub_nonneg.mpr ht1),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) ht0,
    ← ENNReal.ofReal_mul (by positivity), hreal]
  rfl

end LogBrunnMinkowski

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace SlabPartition
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
lemma variation_eq (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t : ℝ) (x : ι → ℝ) :
    variation ψ b k t x = ∑ i, b i ^ k * Real.exp (b i * t) * MvPolynomial.eval x (ψ i) := by
  simp [variation, derivativePoly]

omit [Fintype ι] in
lemma variation_continuous (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t : ℝ) :
    Continuous (variation ψ b k t) := MvPolynomial.continuous_eval _

omit [Fintype ι] in
lemma variation_hasDerivAt (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ)
    (t : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => variation ψ b k s x) (variation ψ b (k+1) t x) t := by
  have hi (i : κ) : HasDerivAt
      (fun s => b i ^ k * Real.exp (b i * s) * MvPolynomial.eval x (ψ i))
      (b i ^ (k+1) * Real.exp (b i * t) * MvPolynomial.eval x (ψ i)) t := by
    convert! (((hasDerivAt_id t).const_mul (b i)).exp.const_mul (b i ^ k)).mul_const
      (MvPolynomial.eval x (ψ i)) using 1
    simp only [id_eq, mul_one, pow_succ]
    ring
  convert! HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hi i) using 1
  · funext s
    simp only [variation_eq, Finset.sum_apply]
  · exact variation_eq ψ b (k+1) t x

lemma potential_continuous (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) :
    Continuous (potential ε ψ b t) := by
  apply Continuous.add
  · exact continuous_const.mul (continuous_finsetSum _ fun j _ => (continuous_apply j).pow 2)
  · exact variation_continuous ψ b 0 t

lemma density_continuous (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) :
    Continuous (density ε ψ b t) := Real.continuous_exp.comp (potential_continuous ε ψ b t).neg

lemma densityFirst_continuous (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) :
    Continuous (densityFirst ε ψ b t) :=
  (variation_continuous ψ b 1 t).neg.mul (density_continuous ε ψ b t)

lemma densitySecond_continuous (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) :
    Continuous (densitySecond ε ψ b t) :=
  ((variation_continuous ψ b 1 t).pow 2 |>.sub (variation_continuous ψ b 2 t)).mul
    (density_continuous ε ψ b t)

lemma density_hasDerivAt (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ)
    (t : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => density ε ψ b s x) (densityFirst ε ψ b t x) t := by
  have h := ((variation_hasDerivAt ψ b 0 t x).const_add
    (ε / 2 * ∑ j, x j ^ 2)).neg.exp
  convert! h using 1
  simp [potential, density, densityFirst, mul_comm]

lemma densityFirst_hasDerivAt (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ)
    (t : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => densityFirst ε ψ b s x) (densitySecond ε ψ b t x) t := by
  have h := (variation_hasDerivAt ψ b 1 t x).neg.mul (density_hasDerivAt ε ψ b t x)
  convert! h using 1
  simp only [densitySecond, densityFirst, Pi.neg_apply, Nat.reduceAdd]
  ring

lemma potential_lower (ε : ℝ) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) (x : ι → ℝ) :
    ε / 2 * (∑ j, x j ^ 2) ≤ potential ε ψ b t x := by
  apply le_add_of_nonneg_right
  rw [variation_eq]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hψ i x))

lemma polynomial_integrable {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ)
    (P : MvPolynomial ι ℝ) : Integrable (fun x => MvPolynomial.eval x P * density ε ψ b t x) := by
  exact GaussianPolynomial.dominated_polynomial (c := 0) (potential_continuous ε ψ b t)
    (half_pos hε) (fun x => by simpa using potential_lower ε hψ b t x) P

lemma density_integrable {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) :
    Integrable (density ε ψ b t) := by
  simpa using polynomial_integrable hε hψ b t (1 : MvPolynomial ι ℝ)

lemma densityFirst_integrable {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) :
    Integrable (densityFirst ε ψ b t) := by
  change Integrable (fun x => -variation ψ b 1 t x * density ε ψ b t x)
  simpa only [variation, map_neg] using polynomial_integrable hε hψ b t (-derivativePoly ψ b 1 t)

omit [Fintype ι] in
lemma eval_boundPoly (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t₀ : ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (boundPoly ψ b k t₀) =
      ∑ i, |b i| ^ k * Real.exp (|b i| * (|t₀| + 1)) * MvPolynomial.eval x (ψ i) := by
  simp [boundPoly]

omit [Fintype ι] in
lemma boundPoly_nonneg {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (k : ℕ) (t₀ : ℝ) (x : ι → ℝ) :
    0 ≤ MvPolynomial.eval x (boundPoly ψ b k t₀) := by
  rw [eval_boundPoly]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hψ i x))

omit [Fintype ι] in
lemma norm_variation_le {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (k : ℕ) (t₀ : ℝ)
    {t : ℝ} (ht : t ∈ Metric.ball t₀ 1) (x : ι → ℝ) :
    ‖variation ψ b k t x‖ ≤ MvPolynomial.eval x (boundPoly ψ b k t₀) := by
  have ht' : |t - t₀| < 1 := by simpa [Real.dist_eq] using ht
  have habs : |t| ≤ |t₀| + 1 := by
    calc
      |t| = |t - t₀ + t₀| := by congr 1; ring
      _ ≤ |t - t₀| + |t₀| := abs_add_le _ _
      _ ≤ |t₀| + 1 := by linarith
  rw [variation_eq, eval_boundPoly]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (hψ i x)]
  apply mul_le_mul_of_nonneg_right _ (hψ i x)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    b i * t ≤ |b i * t| := le_abs_self _
    _ = |b i| * |t| := abs_mul _ _
    _ ≤ |b i| * (|t₀| + 1) := mul_le_mul_of_nonneg_left habs (abs_nonneg _)

lemma density_le_gaussian (ε : ℝ) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) (x : ι → ℝ) :
    density ε ψ b t x ≤ Real.exp (-(ε/2) * ∑ j, x j ^ 2) := by
  apply Real.exp_le_exp.mpr
  linarith [potential_lower ε hψ b t x]

lemma norm_densityFirst_le (ε : ℝ) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t₀ : ℝ)
    {t : ℝ} (ht : t ∈ Metric.ball t₀ 1) (x : ι → ℝ) :
    ‖densityFirst ε ψ b t x‖ ≤
      MvPolynomial.eval x (boundPoly ψ b 1 t₀) * Real.exp (-(ε/2) * ∑ j, x j ^ 2) := by
  rw [densityFirst, norm_mul, norm_neg,
    Real.norm_eq_abs (density ε ψ b t x),
    abs_of_pos (show 0 < density ε ψ b t x from Real.exp_pos _)]
  exact mul_le_mul (norm_variation_le hψ b 1 t₀ ht x) (density_le_gaussian ε hψ b t x)
    (Real.exp_pos _).le (boundPoly_nonneg hψ b 1 t₀ x)

lemma norm_densitySecond_le (ε : ℝ) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t₀ : ℝ)
    {t : ℝ} (ht : t ∈ Metric.ball t₀ 1) (x : ι → ℝ) :
    ‖densitySecond ε ψ b t x‖ ≤
      MvPolynomial.eval x ((boundPoly ψ b 1 t₀)^2 + boundPoly ψ b 2 t₀) *
        Real.exp (-(ε/2) * ∑ j, x j ^ 2) := by
  have h₁ := norm_variation_le hψ b 1 t₀ ht x
  have h₂ := norm_variation_le hψ b 2 t₀ ht x
  have h₀ := boundPoly_nonneg hψ b 1 t₀ x
  have h₂₀ := boundPoly_nonneg hψ b 2 t₀ x
  rw [densitySecond, norm_mul, Real.norm_eq_abs (density _ _ _ _ _),
    abs_of_pos (show 0 < density ε ψ b t x from Real.exp_pos _)]
  apply mul_le_mul _ (density_le_gaussian ε hψ b t x) (Real.exp_pos _).le
    (by simp only [MvPolynomial.eval_add, MvPolynomial.eval_pow]; positivity)
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_pow]
  calc
    ‖variation ψ b 1 t x ^ 2 - variation ψ b 2 t x‖ ≤
      ‖variation ψ b 1 t x ^ 2‖ + ‖variation ψ b 2 t x‖ := norm_sub_le _ _
    _ ≤ MvPolynomial.eval x (boundPoly ψ b 1 t₀)^2 +
        MvPolynomial.eval x (boundPoly ψ b 2 t₀) := by
      rw [norm_pow]
      exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h₁ 2) h₂

lemma partition_pos {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) :
    0 < partition ε ψ b t := integral_exp_pos (density_integrable hε hψ b t)

lemma partition_hasDerivAt {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t₀ : ℝ) :
    HasDerivAt (partition ε ψ b) (partitionFirst ε ψ b t₀) t₀ := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (density_continuous ε ψ b t).aestronglyMeasurable)
    (density_integrable hε hψ b t₀)
    (densityFirst_continuous ε ψ b t₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => norm_densityFirst_le ε hψ b t₀ ht x)
    (GaussianPolynomial.polynomial_integrable (half_pos hε) (boundPoly ψ b 1 t₀))
    (Filter.Eventually.of_forall fun x t _ => density_hasDerivAt ε ψ b t x)).2

lemma partitionFirst_hasDerivAt {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t₀ : ℝ) :
    HasDerivAt (partitionFirst ε ψ b) (partitionSecond ε ψ b t₀) t₀ := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (densityFirst_continuous ε ψ b t).aestronglyMeasurable)
    (densityFirst_integrable hε hψ b t₀)
    (densitySecond_continuous ε ψ b t₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => norm_densitySecond_le ε hψ b t₀ ht x)
    (GaussianPolynomial.polynomial_integrable (half_pos hε)
      ((boundPoly ψ b 1 t₀)^2 + boundPoly ψ b 2 t₀))
    (Filter.Eventually.of_forall fun x t _ => densityFirst_hasDerivAt ε ψ b t x)).2

lemma log_partition_hasDerivAt {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t => Real.log (partition ε ψ b t))
      (partitionFirst ε ψ b t₀ / partition ε ψ b t₀) t₀ :=
  (partition_hasDerivAt hε hψ b t₀).log (partition_pos hε hψ b t₀).ne'

lemma log_partition_derivative_hasDerivAt {ε : ℝ} (hε : 0 < ε)
    {ψ : κ → MvPolynomial ι ℝ} (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i))
    (b : κ → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t => partitionFirst ε ψ b t / partition ε ψ b t)
      ((partitionSecond ε ψ b t₀ * partition ε ψ b t₀ - partitionFirst ε ψ b t₀ ^ 2) /
        partition ε ψ b t₀ ^ 2) t₀ := by
  simpa only [Pi.div_apply, pow_two] using! (partitionFirst_hasDerivAt hε hψ b t₀).div
    (partition_hasDerivAt hε hψ b t₀) (partition_pos hε hψ b t₀).ne'

lemma variance_eq {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ)
    (P : MvPolynomial ι ℝ) :
    variance ε ψ b t (fun x => MvPolynomial.eval x P) =
      mean ε ψ b t (fun x => MvPolynomial.eval x P ^ 2) -
        mean ε ψ b t (fun x => MvPolynomial.eval x P) ^ 2 := by
  have hP := polynomial_integrable hε hψ b t P
  have hP₂ : Integrable (fun x => MvPolynomial.eval x P ^ 2 * density ε ψ b t x) := by
    convert! polynomial_integrable hε hψ b t (P^2) using 1
    funext x
    rw [map_pow]
  have hd := density_integrable hε hψ b t
  let m := mean ε ψ b t (fun x => MvPolynomial.eval x P)
  have he : (fun x => (MvPolynomial.eval x P-m)^2 * density ε ψ b t x) =
      (fun x => MvPolynomial.eval x P ^ 2 * density ε ψ b t x -
        2*m*(MvPolynomial.eval x P * density ε ψ b t x) + m^2*density ε ψ b t x) := by
    funext x
    ring
  change (∫ x, (MvPolynomial.eval x P-m)^2 * density ε ψ b t x) / partition ε ψ b t = _
  have hsub : Integrable (fun x => MvPolynomial.eval x P ^ 2 * density ε ψ b t x -
      2*m*(MvPolynomial.eval x P * density ε ψ b t x)) := by
    simpa only [Pi.sub_apply] using! hP₂.sub (hP.const_mul (2*m))
  rw [he, integral_add hsub (hd.const_mul (m^2)),
    integral_sub hP₂ (hP.const_mul (2*m)), integral_const_mul, integral_const_mul]
  have hZ := (partition_pos hε hψ b t).ne'
  dsimp [m, mean, partition] at *
  field_simp
  ring

lemma partitionFirst_eq (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) :
    partitionFirst ε ψ b t = -(∫ x, variation ψ b 1 t x * density ε ψ b t x) := by
  simp only [partitionFirst, densityFirst, neg_mul, integral_neg]

lemma partitionSecond_eq {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) :
    partitionSecond ε ψ b t =
      (∫ x, variation ψ b 1 t x ^ 2 * density ε ψ b t x) -
      (∫ x, variation ψ b 2 t x * density ε ψ b t x) := by
  have hP₂ : Integrable (fun x => variation ψ b 1 t x ^ 2 * density ε ψ b t x) := by
    convert! polynomial_integrable hε hψ b t ((derivativePoly ψ b 1 t)^2) using 1
    funext x
    rw [map_pow]
    rfl
  simp only [partitionSecond, densitySecond, sub_mul]
  exact integral_sub hP₂ (polynomial_integrable hε hψ b t (derivativePoly ψ b 2 t))

lemma log_partition_second {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) :
    ((partitionSecond ε ψ b t * partition ε ψ b t - partitionFirst ε ψ b t ^ 2) /
        partition ε ψ b t ^ 2) =
      variance ε ψ b t (variation ψ b 1 t) - mean ε ψ b t (variation ψ b 2 t) := by
  rw [partitionFirst_eq, partitionSecond_eq hε hψ]
  rw [show variation ψ b 1 t = (fun x => MvPolynomial.eval x (derivativePoly ψ b 1 t)) from rfl,
    variance_eq hε hψ]
  have hZ := (partition_pos hε hψ b t).ne'
  dsimp only [mean, variation]
  field_simp
  ring

lemma log_partition_concave_of_variance {ε : ℝ} (hε : 0 < ε)
    {ψ : κ → MvPolynomial ι ℝ} (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i))
    (b : κ → ℝ)
    (hvar : ∀ t, variance ε ψ b t (variation ψ b 1 t) ≤ mean ε ψ b t (variation ψ b 2 t)) :
    ConcaveOn ℝ Set.univ (fun t => Real.log (partition ε ψ b t)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    (f' := fun t => partitionFirst ε ψ b t / partition ε ψ b t)
    (f'' := fun t => (partitionSecond ε ψ b t * partition ε ψ b t - partitionFirst ε ψ b t ^ 2) /
      partition ε ψ b t ^ 2)
  · exact (continuous_iff_continuousAt.mpr fun t =>
      (log_partition_hasDerivAt hε hψ b t).continuousAt).continuousOn
  · exact fun t _ => (log_partition_hasDerivAt hε hψ b t).hasDerivWithinAt
  · exact fun t _ => (log_partition_derivative_hasDerivAt hε hψ b t).hasDerivWithinAt
  · intro t _
    rw [log_partition_second hε hψ]
    exact sub_nonpos.mpr (hvar t)

lemma partition_rpow_le_of_variance {ε : ℝ} (hε : 0 < ε)
    {ψ : κ → MvPolynomial ι ℝ} (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i))
    (b : κ → ℝ)
    (hvar : ∀ t, variance ε ψ b t (variation ψ b 1 t) ≤ mean ε ψ b t (variation ψ b 2 t))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    partition ε ψ b 0 ^ (1-t) * partition ε ψ b 1 ^ t ≤ partition ε ψ b t := by
  have hc := log_partition_concave_of_variance hε hψ b hvar
  have hh := hc.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hh
  have h₀ := partition_pos hε hψ b 0
  have h₁ := partition_pos hε hψ b 1
  have ht₀ := partition_pos hε hψ b t
  rw [Real.rpow_def_of_pos h₀, Real.rpow_def_of_pos h₁, ← Real.exp_add,
    ← Real.exp_log ht₀]
  apply Real.exp_le_exp.mpr
  nlinarith [hh]

end SlabPartition

namespace SoftSlabLimits
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

lemma level_null (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) {t : ℝ} (ht : t ≠ 0) :
    volume {x | ℓ x = t} = 0 := by
  let s := (affineSpan ℝ ({t} : Set ℝ)).comap ℓ.toAffineMap
  have hs : s ≠ ⊤ := by
    intro h
    have hz : (0 : ι → ℝ) ∈ s := by rw [h]; trivial
    have : (0 : ℝ) = t := by
      simpa [s, AffineSubspace.mem_affineSpan_singleton] using hz
    exact ht this.symm
  have hset : {x | ℓ x = t} = (s : Set (ι → ℝ)) := by
    ext x
    simp [s]
  rw [hset]
  exact addHaar_affineSubspace volume s hs

lemma abs_level_ne_ae (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) :
    ∀ᵐ x, |ℓ x| ≠ 1 := by
  have hp : ∀ᵐ x, ℓ x ≠ 1 := by
    rw [ae_iff]; simpa only [not_not] using level_null ℓ one_ne_zero
  have hm : ∀ᵐ x, ℓ x ≠ -1 := by
    rw [ae_iff]; simpa only [not_not] using level_null ℓ (t := -1) (by norm_num)
  filter_upwards [hp, hm] with x hp hm
  intro he
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp he with h | h
  · exact hp h
  · exact hm h

lemma body_measurable (ℓ : κ → (ι → ℝ) →ₗ[ℝ] ℝ) : MeasurableSet (body ℓ) := by
  have hb : body ℓ = ⋂ i, {x | |ℓ i x| ≤ 1} := by ext x; simp [body]
  rw [hb]
  apply MeasurableSet.iInter
  intro i
  exact (isClosed_le ((ℓ i).continuous_of_finiteDimensional.abs) continuous_const).measurableSet

lemma continuous_density (ℓ : κ → (ι → ℝ) →ₗ[ℝ] ℝ) (ε : ℝ) (k : ℕ) :
    Continuous (density ℓ ε k) := by
  unfold density
  fun_prop

lemma density_le_gaussian (ℓ : κ → (ι → ℝ) →ₗ[ℝ] ℝ) (ε : ℝ) (k : ℕ) (x : ι → ℝ) :
    ‖density ℓ ε k x‖ ≤ gaussian ε x := by
  rw [density, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (Finset.sum_nonneg fun i _ => Even.pow_nonneg ⟨k+1, by omega⟩ _)

lemma gaussian_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (gaussian (ι:=ι) ε) := by
  unfold gaussian
  simpa only [map_one, one_mul] using GaussianPolynomial.polynomial_integrable
    (show 0 < ε/2 by positivity) (1 : MvPolynomial ι ℝ)

lemma evenIndex_tendsto : Tendsto (fun k : ℕ => 2*k+2) atTop atTop :=
  tendsto_atTop_mono (fun k : ℕ => by dsimp; omega) tendsto_id

lemma density_tendsto (ℓ : κ → (ι → ℝ) →ₗ[ℝ] ℝ) (ε : ℝ) (x : ι → ℝ)
    (hx : ∀ i, |ℓ i x| ≠ 1) :
    Tendsto (fun k => density ℓ ε k x) atTop (𝓝 ((body ℓ).indicator (gaussian ε) x)) := by
  classical
  by_cases hi : x ∈ body ℓ
  · have hlt : ∀ i, |ℓ i x| < 1 := fun i => lt_of_le_of_ne (hi i) (hx i)
    have ht : Tendsto (fun k => ∑ i, (ℓ i x) ^ (2*k+2)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun i _ =>
        (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (hlt i)).comp evenIndex_tendsto)
    rw [indicator_of_mem hi]
    simpa only [density, gaussian, sub_zero, Function.comp_def] using!
      Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_const_nhds.sub ht) : Tendsto
          (fun k => -(ε/2) * ∑ j, x j^2 - ∑ i, (ℓ i x) ^ (2*k+2)) atTop
          (𝓝 (-(ε/2) * ∑ j, x j^2 - 0)))
  · have hout : ∃ i, 1 < |ℓ i x| := by
      simpa only [body, mem_ofPred_eq, not_forall, not_le] using hi
    obtain ⟨i, hix⟩ := hout
    have ht : Tendsto (fun k => ∑ j, (ℓ j x) ^ (2*k+2)) atTop atTop := by
      apply tendsto_atTop_mono (fun k => ?_)
        ((tendsto_pow_atTop_atTop_of_one_lt hix).comp evenIndex_tendsto)
      change |ℓ i x| ^ (2*k+2) ≤ _
      rw [Even.pow_abs ⟨k+1, by omega⟩]
      have hn (j : κ) : 0 ≤ (ℓ j x) ^ (2*k+2) := Even.pow_nonneg ⟨k+1, by omega⟩ _
      exact Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    rw [indicator_of_notMem hi]
    have ht' : Tendsto (fun k => (∑ j, (ℓ j x) ^ (2*k+2)) + (ε/2) * ∑ j, x j^2)
        atTop atTop := ht.atTop_add tendsto_const_nhds
    have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht')
    convert! he using 1
    funext k
    dsimp [density]
    congr 1
    ring

lemma partition_tendsto (ℓ : κ → (ι → ℝ) →ₗ[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => ∫ x, density ℓ ε k x) atTop
      (𝓝 (∫ x in body ℓ, gaussian ε x)) := by
  rw [← integral_indicator (body_measurable ℓ)]
  apply tendsto_integral_of_dominated_convergence (gaussian ε)
    (fun k => (continuous_density ℓ ε k).aestronglyMeasurable)
    (gaussian_integrable hε) (fun k => Eventually.of_forall (density_le_gaussian ℓ ε k))
  have h : ∀ᵐ x, ∀ i, |ℓ i x| ≠ 1 := ae_all_iff.mpr (fun i => abs_level_ne_ae (ℓ i))
  filter_upwards [h] with x hx
  exact density_tendsto ℓ ε x hx

lemma gaussian_tendsto_volume {s : Set (ι → ℝ)} (hs : volume s ≠ ⊤)
    {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k) (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in s, gaussian (ε k) x) atTop (𝓝 (volume.real s)) := by
  have hi : Integrable (fun _ : ι → ℝ => (1 : ℝ)) (volume.restrict s) := integrableOn_const hs
  have hc (k : ℕ) : Continuous (gaussian (ι:=ι) (ε k)) := by unfold gaussian; fun_prop
  have hl := tendsto_integral_of_dominated_convergence (μ := volume.restrict s) (f := fun _ => (1 : ℝ))
    (fun _ : ι → ℝ => (1 : ℝ)) (fun k => (hc k).aestronglyMeasurable) hi
    (fun k => Eventually.of_forall (fun x => ?_))
    (Eventually.of_forall (fun x => ?_))
  · simpa only [setIntegral_const, smul_eq_mul, mul_one] using hl
  · rw [gaussian, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (hε k) (by norm_num)))
      (Finset.sum_nonneg fun j _ => sq_nonneg (x j))
  · have hh : Tendsto (fun k => -(ε k/2) * ∑ j, x j^2) atTop (𝓝 0) := by
      simpa only [zero_div, neg_zero, zero_mul] using (ht.div_const 2).neg.mul_const (∑ j, x j^2)
    simpa only [gaussian, Real.exp_zero, Function.comp_def] using!
      Real.continuous_exp.continuousAt.tendsto.comp hh

lemma volume_rpow_le_of_partition (ℓ₀ ℓ₁ ℓt : κ → (ι → ℝ) →ₗ[ℝ] ℝ)
    (h₀ : volume (body ℓ₀) ≠ ⊤) (h₁ : volume (body ℓ₁) ≠ ⊤)
    (htb : volume (body ℓt) ≠ ⊤) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hpart : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ,
      (∫ x, density ℓ₀ ε k x) ^ (1-t) * (∫ x, density ℓ₁ ε k x) ^ t ≤
        ∫ x, density ℓt ε k x) :
    volume.real (body ℓ₀) ^ (1-t) * volume.real (body ℓ₁) ^ t ≤ volume.real (body ℓt) := by
  have hgauss (ε : ℝ) (hε : 0 < ε) :
      (∫ x in body ℓ₀, gaussian ε x) ^ (1-t) * (∫ x in body ℓ₁, gaussian ε x) ^ t ≤
        ∫ x in body ℓt, gaussian ε x := by
    exact le_of_tendsto_of_tendsto
      (((partition_tendsto ℓ₀ hε).rpow_const (Or.inr (sub_nonneg.mpr ht.2))).mul
        ((partition_tendsto ℓ₁ hε).rpow_const (Or.inr ht.1)))
      (partition_tendsto ℓt hε) (Eventually.of_forall (hpart ε hε))
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hepos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have het : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_one, Function.comp_def] using!
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto
    (((gaussian_tendsto_volume h₀ (fun k => (hepos k).le) het).rpow_const
      (Or.inr (sub_nonneg.mpr ht.2))).mul
      ((gaussian_tendsto_volume h₁ (fun k => (hepos k).le) het).rpow_const (Or.inr ht.1)))
    (gaussian_tendsto_volume htb (fun k => (hepos k).le) het)
    (Eventually.of_forall (fun k => hgauss (ε k) (hepos k)))

end SoftSlabLimits

namespace SlabReduction
open MeasureTheory Set Filter
open scoped BigOperators Topology
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

lemma eval_feature (p x : ι → ℝ) (h : ℝ) (q : ℕ) :
    MvPolynomial.eval x (feature p h q) = (p ⬝ᵥ x / h)^q := by
  simp [feature, linearPoly, dotProduct, div_eq_mul_inv, mul_comm]

lemma normal_apply (p x : ι → ℝ) (h : ℝ) : normal p h x = p ⬝ᵥ x / h := by
  simp [normal, div_eq_mul_inv, mul_comm]

lemma width_pos {h₀ h₁ : ℝ} (ha : 0 < h₀) (hb : 0 < h₁) (t : ℝ) :
    0 < width h₀ h₁ t := mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)

lemma width_exponential {h₀ h₁ : ℝ} (ha : 0 < h₀) (hb : 0 < h₁) (t : ℝ) :
    width h₀ h₁ t = h₀ * Real.exp (t * Real.log (h₁/h₀)) := by
  dsimp [width]
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add,
    Real.log_div hb.ne' ha.ne']
  calc
    _ = Real.exp (Real.log h₀ + t * (Real.log h₁ - Real.log h₀)) := by congr 1; ring
    _ = _ := by rw [Real.exp_add, Real.exp_log ha]

lemma feature_exponential {h₀ h₁ : ℝ} (ha : 0 < h₀) (hb : 0 < h₁)
    (p x : ι → ℝ) (q : ℕ) (t : ℝ) :
    Real.exp (rate q h₀ h₁ * t) * MvPolynomial.eval x (feature p h₀ q) =
      (normal p (width h₀ h₁ t) x)^q := by
  rw [eval_feature, normal_apply, width_exponential ha hb]
  rw [show rate q h₀ h₁ * t = (q:ℝ) * (-(t * Real.log (h₁/h₀))) by dsimp [rate]; ring,
    Real.exp_nat_mul, ← mul_pow, Real.exp_neg]
  congr 1
  field_simp

omit [Fintype κ] in
lemma features_nonneg (p : κ → ι → ℝ) (h : κ → ℝ) {q : ℕ} (hq : Even q) :
    ∀ i x, 0 ≤ MvPolynomial.eval x (features p h q i) := by
  intro i x
  rw [features, eval_feature]
  exact hq.pow_nonneg _

lemma variation_identification (p : κ → ι → ℝ) {h₀ h₁ : κ → ℝ}
    (ha : ∀ i, 0 < h₀ i) (hb : ∀ i, 0 < h₁ i) (q k : ℕ) (t : ℝ) (x : ι → ℝ) :
    SlabPartition.variation (features p h₀ q) (rates h₀ h₁ q) k t x =
      ∑ i, (rates h₀ h₁ q i)^k * (normal (p i) (width (h₀ i) (h₁ i) t) x)^q := by
  rw [SlabPartition.variation_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc]
  congr 1
  exact feature_exponential (ha i) (hb i) (p i) x q t

lemma density_identification (p : κ → ι → ℝ) {h₀ h₁ : κ → ℝ}
    (ha : ∀ i, 0 < h₀ i) (hb : ∀ i, 0 < h₁ i) (ε : ℝ) (k : ℕ) (t : ℝ) :
    SlabPartition.density ε (features p h₀ (2*k+2)) (rates h₀ h₁ (2*k+2)) t =
      SoftSlabLimits.density (normals p (widths h₀ h₁ t)) ε k := by
  funext x
  dsimp [SlabPartition.density, SlabPartition.potential, SoftSlabLimits.density]
  rw [variation_identification p ha hb]
  simp only [pow_zero, one_mul]
  congr 1
  dsimp [normals, widths]
  ring

omit [Fintype κ] in
lemma widths_zero {h₀ h₁ : κ → ℝ} :
    widths h₀ h₁ 0 = h₀ := by
  funext i
  simp [widths, width]

omit [Fintype κ] in
lemma widths_one {h₀ h₁ : κ → ℝ} :
    widths h₀ h₁ 1 = h₁ := by
  funext i
  simp [widths, width]

theorem finite_slabs_of_variance (p : κ → ι → ℝ) {h₀ h₁ : κ → ℝ}
    (ha : ∀ i, 0 < h₀ i) (hb : ∀ i, 0 < h₁ i) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hfin₀ : volume (SoftSlabLimits.body (normals p h₀)) ≠ ⊤)
    (hfin₁ : volume (SoftSlabLimits.body (normals p h₁)) ≠ ⊤)
    (hfint : volume (SoftSlabLimits.body (normals p (widths h₀ h₁ t))) ≠ ⊤)
    (hvar : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, ∀ s : ℝ,
      SlabPartition.variance ε (features p h₀ (2*k+2)) (rates h₀ h₁ (2*k+2)) s
        (SlabPartition.variation (features p h₀ (2*k+2)) (rates h₀ h₁ (2*k+2)) 1 s) ≤
      SlabPartition.mean ε (features p h₀ (2*k+2)) (rates h₀ h₁ (2*k+2)) s
        (SlabPartition.variation (features p h₀ (2*k+2)) (rates h₀ h₁ (2*k+2)) 2 s)) :
    volume.real (SoftSlabLimits.body (normals p h₀)) ^ (1-t) *
      volume.real (SoftSlabLimits.body (normals p h₁)) ^ t ≤
        volume.real (SoftSlabLimits.body (normals p (widths h₀ h₁ t))) := by
  apply SoftSlabLimits.volume_rpow_le_of_partition _ _ _ hfin₀ hfin₁ hfint ht
  intro ε hε k
  have h := SlabPartition.partition_rpow_le_of_variance hε
    (features_nonneg p h₀ (show Even (2*k+2) from ⟨k+1, by omega⟩))
    (rates h₀ h₁ (2*k+2)) (hvar ε hε k) ht
  simpa only [SlabPartition.partition, density_identification p ha hb,
    widths_zero, widths_one] using h

end SlabReduction

namespace LogBrunnMinkowski

lemma finiteSlabs_preimage_eq_body {n : ℕ} (D : Finset (Space n))
    (f : Space n → ℝ) (hf : ∀ u ∈ D, 0 < f u) :
    WithLp.toLp 2 ⁻¹' (finiteSlabs D f) =
      SoftSlabLimits.body (SlabReduction.normals (fun u : D => u.val.ofLp)
        (fun u : D => f u.val)) := by
  ext x
  simp only [Set.mem_preimage, finiteSlabs, SoftSlabLimits.body, Set.mem_ofPred_eq]
  constructor
  · intro hx u
    rw [SlabReduction.normals, SlabReduction.normal_apply, abs_div,
      abs_of_pos (hf u.val u.property), div_le_one (hf u.val u.property)]
    simpa [EuclideanSpace.inner_eq_star_dotProduct] using hx u.val u.property
  · intro hx u hu
    have h := hx ⟨u, hu⟩
    rw [SlabReduction.normals, SlabReduction.normal_apply, abs_div,
      abs_of_pos (hf u hu), div_le_one (hf u hu)] at h
    simpa [EuclideanSpace.inner_eq_star_dotProduct] using h

lemma volume_finiteSlabs_eq_body {n : ℕ} (D : Finset (Space n))
    (f : Space n → ℝ) (hf : ∀ u ∈ D, 0 < f u) :
    volume (finiteSlabs D f) =
      volume (SoftSlabLimits.body (SlabReduction.normals (fun u : D => u.val.ofLp)
        (fun u : D => f u.val))) := by
  rw [← finiteSlabs_preimage_eq_body D f hf]
  exact ((PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (finiteSlabs_closed D f).measurableSet.nullMeasurableSet).symm

lemma ennreal_rpow_le_of_toReal {a b c : ℝ≥0∞} (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) (hc : c ≠ ⊤) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (h : a.toReal^(1-t)*b.toReal^t ≤ c.toReal) : a^(1-t)*b^t ≤ c := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr ht.2) ha)
      (ENNReal.rpow_ne_top_of_nonneg ht.1 hb)) hc).mp
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using h

lemma finiteSlabs_volume_of_body_inequality {n : ℕ} (D : Finset (Space n))
    (hD : ∀ i : Fin n, EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (f₀ f₁ : Space n → ℝ) (h₀ : ∀ u ∈ D, 0 < f₀ u)
    (h₁ : ∀ u ∈ D, 0 < f₁ u) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (h : volume.real (SoftSlabLimits.body (SlabReduction.normals
        (fun u : D => u.val.ofLp) (fun u : D => f₀ u.val)))^(1-t) *
      volume.real (SoftSlabLimits.body (SlabReduction.normals
        (fun u : D => u.val.ofLp) (fun u : D => f₁ u.val)))^t ≤
      volume.real (SoftSlabLimits.body (SlabReduction.normals
        (fun u : D => u.val.ofLp) (fun u : D => f₀ u.val^(1-t)*f₁ u.val^t)))) :
    volume (finiteSlabs D f₀) ^ (1-t) * volume (finiteSlabs D f₁) ^ t ≤
      volume (finiteSlabs D (fun u => f₀ u ^ (1-t) * f₁ u ^ t)) := by
  let f := fun u => f₀ u ^ (1-t) * f₁ u ^ t
  have hf : ∀ u ∈ D, 0 < f u := fun u hu =>
    SlabReduction.width_pos (h₀ u hu) (h₁ u hu) t
  apply ennreal_rpow_le_of_toReal
    ((finiteSlabs_compact D f₀ hD).measure_ne_top (μ := volume))
    ((finiteSlabs_compact D f₁ hD).measure_ne_top (μ := volume))
    ((finiteSlabs_compact D f hD).measure_ne_top (μ := volume)) ht
  simpa only [volume_finiteSlabs_eq_body D f₀ h₀, volume_finiteSlabs_eq_body D f₁ h₁,
    volume_finiteSlabs_eq_body D f hf, Measure.real] using h

lemma volume_body_finiteSlabs_ne_top {n : ℕ} (D : Finset (Space n))
    (hD : ∀ i : Fin n, EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (f : Space n → ℝ) (hf : ∀ u ∈ D, 0 < f u) :
    volume (SoftSlabLimits.body (SlabReduction.normals
        (fun u : D => u.val.ofLp) (fun u : D => f u.val))) ≠ ⊤ := by
  rw [← volume_finiteSlabs_eq_body D f hf]
  exact (finiteSlabs_compact D f hD).measure_ne_top (μ := volume)

lemma finiteSlabs_volume_of_variance {n : ℕ} (D : Finset (Space n))
    (hD : ∀ i : Fin n, EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (f₀ f₁ : Space n → ℝ) (h₀ : ∀ u ∈ D, 0 < f₀ u)
    (h₁ : ∀ u ∈ D, 0 < f₁ u) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hvar : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, ∀ s : ℝ,
      SlabPartition.variance ε
        (SlabReduction.features (fun u : D => u.val.ofLp) (fun u : D => f₀ u.val) (2*k+2))
        (SlabReduction.rates (fun u : D => f₀ u.val) (fun u : D => f₁ u.val) (2*k+2)) s
        (SlabPartition.variation
          (SlabReduction.features (fun u : D => u.val.ofLp) (fun u : D => f₀ u.val) (2*k+2))
          (SlabReduction.rates (fun u : D => f₀ u.val) (fun u : D => f₁ u.val) (2*k+2)) 1 s) ≤
      SlabPartition.mean ε
        (SlabReduction.features (fun u : D => u.val.ofLp) (fun u : D => f₀ u.val) (2*k+2))
        (SlabReduction.rates (fun u : D => f₀ u.val) (fun u : D => f₁ u.val) (2*k+2)) s
        (SlabPartition.variation
          (SlabReduction.features (fun u : D => u.val.ofLp) (fun u : D => f₀ u.val) (2*k+2))
          (SlabReduction.rates (fun u : D => f₀ u.val) (fun u : D => f₁ u.val) (2*k+2)) 2 s)) :
    volume (finiteSlabs D f₀) ^ (1-t) * volume (finiteSlabs D f₁) ^ t ≤
      volume (finiteSlabs D (fun u => f₀ u ^ (1-t) * f₁ u ^ t)) := by
  apply finiteSlabs_volume_of_body_inequality D hD f₀ f₁ h₀ h₁ ht
  exact SlabReduction.finite_slabs_of_variance (fun u : D => u.val.ofLp)
    (fun u => h₀ u.val u.property) (fun u => h₁ u.val u.property) ht
    (volume_body_finiteSlabs_ne_top D hD f₀ h₀)
    (volume_body_finiteSlabs_ne_top D hD f₁ h₁)
    (volume_body_finiteSlabs_ne_top D hD (fun u => f₀ u^(1-t)*f₁ u^t)
      (fun u hu => SlabReduction.width_pos (h₀ u hu) (h₁ u hu) t)) hvar

lemma varying_density_eq {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]
    (p : κ → ι → ℝ) {h₀ h₁ : κ → ℝ}
    (ha : ∀ i, 0 < h₀ i) (hb : ∀ i, 0 < h₁ i) (ε : ℝ) (q : ℕ) (s : ℝ) :
    SlabPartition.density ε (SlabReduction.features p h₀ q)
      (SlabReduction.rates h₀ h₁ q) s =
    SlabPartition.density ε (SlabReduction.features p (SlabReduction.widths h₀ h₁ s) q)
      (fun _ => 0) 0 := by
  classical
  funext x
  dsimp [SlabPartition.density, SlabPartition.potential]
  congr 2
  rw [SlabReduction.variation_identification p ha hb, SlabPartition.variation_eq]
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [SlabReduction.features, SlabReduction.eval_feature, SlabReduction.normal_apply]
  rfl

lemma varying_variation_eq {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]
    (p : κ → ι → ℝ) {h₀ h₁ : κ → ℝ}
    (ha : ∀ i, 0 < h₀ i) (hb : ∀ i, 0 < h₁ i) (q k : ℕ) (s : ℝ) :
    SlabPartition.variation (SlabReduction.features p h₀ q)
      (SlabReduction.rates h₀ h₁ q) k s =
      fun x => ∑ i, (SlabReduction.rates h₀ h₁ q i)^k *
        MvPolynomial.eval x (SlabReduction.features p (SlabReduction.widths h₀ h₁ s) q i) := by
  funext x
  rw [SlabReduction.variation_identification p ha hb]
  apply Finset.sum_congr rfl
  intro i _
  rw [SlabReduction.features, SlabReduction.eval_feature, SlabReduction.normal_apply]
  rfl

lemma source_variance_at_parameter (hv : SoftVarianceStatement)
    {n : ℕ} (hn : 2 ≤ n) {κ : Type} [Fintype κ] [Nonempty κ]
    (p : κ → Fin n → ℝ) (hp : ∀ i, p i ≠ 0) {h₀ h₁ : κ → ℝ}
    (ha : ∀ i, 0 < h₀ i) (hb : ∀ i, 0 < h₁ i) {ε : ℝ} (hε : 0 < ε)
    (k : ℕ) (s : ℝ) :
    SlabPartition.variance ε (SlabReduction.features p h₀ (2*k+2))
      (SlabReduction.rates h₀ h₁ (2*k+2)) s
      (SlabPartition.variation (SlabReduction.features p h₀ (2*k+2))
        (SlabReduction.rates h₀ h₁ (2*k+2)) 1 s) ≤
    SlabPartition.mean ε (SlabReduction.features p h₀ (2*k+2))
      (SlabReduction.rates h₀ h₁ (2*k+2)) s
      (SlabPartition.variation (SlabReduction.features p h₀ (2*k+2))
        (SlabReduction.rates h₀ h₁ (2*k+2)) 2 s) := by
  have h := hv n hn κ inferInstance inferInstance (2*k+2) ⟨k+1, by omega⟩ (by omega)
    ε hε p hp (SlabReduction.widths h₀ h₁ s)
    (fun i => SlabReduction.width_pos (ha i) (hb i) s) (SlabReduction.rates h₀ h₁ (2*k+2))
  rw [varying_variation_eq p ha hb, varying_variation_eq p ha hb]
  simp only [pow_one]
  simpa only [SlabPartition.variance, SlabPartition.mean, SlabPartition.partition,
    varying_density_eq p ha hb] using h

lemma main_of_softVariance (hv : SoftVarianceStatement) : MainStatement := by
  intro n hn K L hK hL hsK hsL t ht₀ ht₁
  by_cases hn₁ : n = 1
  · subst n
    exact (main_dimension_one hK hL hsK hsL ht₀ ht₁).ge
  have hn₂ : 2 ≤ n := by omega
  apply main_of_finite_slabs hn hK hL hsK hsL ht₀ ht₁
  intro D hD hunit
  have ha : ∀ u ∈ D, 0 < support K u := fun u hu => positive_support hK hsK (hunit u hu)
  have hb : ∀ u ∈ D, 0 < support L u := fun u hu => positive_support hL hsL (hunit u hu)
  apply finiteSlabs_volume_of_variance D hD (support K) (support L) ha hb ⟨ht₀, ht₁⟩
  intro ε hε k s
  let : Nonempty D := ⟨⟨EuclideanSpace.basisFun (Fin n) ℝ ⟨0, by omega⟩, hD _⟩⟩
  apply source_variance_at_parameter hv hn₂ (fun u : D => u.val.ofLp) _
    (fun u => ha u.val u.property) (fun u => hb u.val u.property) hε k s
  intro u hu
  have hzero : u.val = 0 := by
    apply WithLp.ofLp_injective
    exact hu
  have hnorm := hunit u.val u.property
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

end LogBrunnMinkowski
end


end



noncomputable section


namespace LogBrunnMinkowski
open MeasureTheory Set
open scoped InnerProductSpace ENNReal ContDiff

theorem main_oai (n : ℕ) (hn : 1 ≤ n) (K L : Set (Space n))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume K) ^ (1 - t) * (volume L) ^ t ≤ volume (logCombination K L t) := by
  exact main_of_softVariance softVariance n hn K L hK hL hsK hsL t ht0 ht1
end LogBrunnMinkowski
end

end OAI
end

theorem solution : type_of% @OAI.LogBrunnMinkowski.main_oai := @OAI.LogBrunnMinkowski.main_oai
