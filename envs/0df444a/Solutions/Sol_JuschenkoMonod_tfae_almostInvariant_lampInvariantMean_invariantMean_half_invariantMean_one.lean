-- Prove2me | solution 1 for JuschenkoMonod.tfae_almostInvariant_lampInvariantMean_invariantMean_half_invariantMean_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T15:48:00.184825+00:00
-- url     : https://prove2.me/submissions/fd1cbda6-2600-4a7a-94c8-f0a960f5bd1e

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_JuschenkoMonod

section
open MeasureTheory
open scoped ENNReal Pointwise
namespace JuschenkoMonod.L31
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
/-! Blueprint for Juschenko–Monod Lemma 3.1 (p. 783): the cycle
(i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (ii) ⇒ (i). -/
/-- Condition (i), finite form. -/
def CondI : Prop :=
  ∀ S : Finset G, ∀ ε : ℝ, 0 < ε → ∃ f : (X → Fin 2) → ℂ, MemLp f 2 (bernoulli X) ∧
    0 < l2Norm f ∧ (∀ g ∈ S, l2Norm (translate g f - f) ≤ ε * l2Norm f) ∧
    (1 - ε) * l2Norm f ≤ l2Norm (restrictZero x₀ f)

/-- Condition (ii). -/
def CondII : Prop :=
  ∃ m : Set (Finset X) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
    IsLampInvariant G m

/-- Condition (iii). -/
def CondIII : Prop :=
  ∃ m : Set (Finset X) → ℝ≥0∞, IsInvariantMean G m ∧ m {E | x₀ ∈ E} = 1 / 2

/-- Condition (iv). -/
def CondIV : Prop :=
  ∃ m : Set (Finset X) → ℝ≥0∞, IsInvariantMean G m ∧ m {E | x₀ ∈ E} = 1

end JuschenkoMonod.L31
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
instance isProb_bernoulli (X : Type*) : IsProbabilityMeasure (bernoulli X) := by
  unfold bernoulli; infer_instance

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {X : Type*} [DecidableEq X]
/-- The sign character of `Fin 2`. -/
def sgn (a : Fin 2) : ℂ := if a = 0 then 1 else -1

lemma sgn_mul_self (a : Fin 2) : sgn a * sgn a = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma norm_sgn (a : Fin 2) : ‖sgn a‖ = 1 := by
  unfold sgn; split_ifs <;> simp

lemma conj_sgn (a : Fin 2) : (starRingEnd ℂ) (sgn a) = sgn a := by
  unfold sgn; split_ifs <;> simp

/-- Walsh characters. -/
noncomputable def walsh (E : Finset X) (ω : X → Fin 2) : ℂ := ∏ x ∈ E, sgn (ω x)

lemma walsh_empty (ω : X → Fin 2) : walsh ∅ ω = 1 := by simp [walsh]

lemma walsh_mul_self (E : Finset X) (ω : X → Fin 2) : walsh E ω * walsh E ω = 1 := by
  unfold walsh; rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun x _ => sgn_mul_self _

lemma walsh_split (E F : Finset X) (ω : X → Fin 2) :
    walsh E ω = walsh (E \ F) ω * walsh (E ∩ F) ω := by
  unfold walsh
  rw [← Finset.sdiff_inter_self_left, Finset.prod_sdiff Finset.inter_subset_left]

lemma walsh_mul (E F : Finset X) (ω : X → Fin 2) :
    walsh E ω * walsh F ω = walsh (E ∆ F) ω := by
  have h1 := walsh_split E F ω
  have h2 := walsh_split F E ω
  have h3 : walsh (E ∆ F) ω = walsh (E \ F) ω * walsh (F \ E) ω := by
    unfold walsh
    rw [symmDiff_def, Finset.sup_eq_union, Finset.prod_union disjoint_sdiff_sdiff]
  rw [h1, h2, h3, Finset.inter_comm F E]
  have := walsh_mul_self (E ∩ F) ω
  linear_combination (walsh (E \ F) ω * walsh (F \ E) ω) * this

lemma norm_walsh (E : Finset X) (ω : X → Fin 2) : ‖walsh E ω‖ = 1 := by
  simp [walsh, norm_sgn]

lemma conj_walsh (E : Finset X) (ω : X → Fin 2) : (starRingEnd ℂ) (walsh E ω) = walsh E ω := by
  simp [walsh, map_prod, conj_sgn]

lemma measurable_sgn : Measurable sgn := measurable_of_finite _

lemma measurable_walsh (E : Finset X) : Measurable (walsh E) := by
  unfold walsh
  exact Finset.measurable_prod _ fun x _ => measurable_sgn.comp (measurable_pi_apply x)

lemma integral_sgn :
    ∫ a, sgn a ∂(PMF.uniformOfFintype (Fin 2)).toMeasure = 0 := by
  rw [integral_fintype (Integrable.of_finite)]
  simp [Fin.sum_univ_two, sgn, measureReal_def]

lemma integral_walsh (E : Finset X) :
    ∫ ω, walsh E ω ∂bernoulli X = if E = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h; simp [walsh_empty]
  · have : (fun ω : X → Fin 2 => walsh E ω) =
        fun ω => (fun y : (E → Fin 2) => ∏ i : E, sgn (y i)) (E.restrict ω) := by
      funext ω; exact (Finset.prod_coe_sort E (fun x => sgn (ω x))).symm
    rw [this, bernoulli]
    refine (integral_restrict_infinitePi (μ := fun _ : X => (PMF.uniformOfFintype (Fin 2)).toMeasure)
      (f := fun y : (E → Fin 2) => ∏ i : E, sgn (y i))
      (measurable_of_finite _).aestronglyMeasurable).trans ?_
    rw [integral_fintype_prod_eq_prod (fun _ => sgn)]
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 h
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨x, hx⟩) integral_sgn

lemma integrable_walsh (E : Finset X) : Integrable (walsh E) (bernoulli X) :=
  Integrable.of_bound (measurable_walsh E).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => (norm_walsh E ω).le)

lemma integral_walsh_mul (E F : Finset X) :
    ∫ ω, walsh E ω * walsh F ω ∂bernoulli X = if E = F then 1 else 0 := by
  simp_rw [walsh_mul, integral_walsh]
  simp only [Finset.symmDiff_eq_empty]

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {X : Type*}
lemma l2Norm_sq_eq {f : (X → Fin 2) → ℂ} (hf : MemLp f 2 (bernoulli X)) :
    l2Norm f ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂bernoulli X := by
  unfold l2Norm
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ ω, ‖f ω‖ ^ 2 ∂bernoulli X := integral_nonneg fun _ => by positivity
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), show (2:ℝ)⁻¹ = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt h0]

lemma l2Norm_nonneg (f : (X → Fin 2) → ℂ) : 0 ≤ l2Norm f := ENNReal.toReal_nonneg

lemma l2Norm_add_le {f g : (X → Fin 2) → ℂ} (hf : MemLp f 2 (bernoulli X))
    (hg : MemLp g 2 (bernoulli X)) : l2Norm (f + g) ≤ l2Norm f + l2Norm g := by
  unfold l2Norm
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable (by norm_num))

lemma l2Norm_neg (f : (X → Fin 2) → ℂ) : l2Norm (-f) = l2Norm f := by
  simp [l2Norm, eLpNorm_neg]

lemma l2Norm_smul (c : ℂ) (f : (X → Fin 2) → ℂ) : l2Norm (c • f) = ‖c‖ * l2Norm f := by
  simp [l2Norm, eLpNorm_const_smul, ENNReal.toReal_mul]

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {X : Type*} [DecidableEq X]
/-- Walsh polynomials. -/
noncomputable def poly (T : Finset (Finset X)) (c : Finset X → ℂ) (ω : X → Fin 2) : ℂ :=
  ∑ E ∈ T, c E * walsh E ω

lemma measurable_poly (T : Finset (Finset X)) (c : Finset X → ℂ) : Measurable (poly T c) := by
  unfold poly
  exact Finset.measurable_sum _ fun E _ => (measurable_walsh E).const_mul _

lemma memLp_poly (T : Finset (Finset X)) (c : Finset X → ℂ) : MemLp (poly T c) 2 (bernoulli X) :=
  MemLp.of_bound (measurable_poly T c).aestronglyMeasurable (∑ E ∈ T, ‖c E‖)
    (Filter.Eventually.of_forall fun ω => by
      unfold poly
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun E _ => ?_)
      simp [norm_walsh])

lemma integral_norm_sq_poly (T : Finset (Finset X)) (c : Finset X → ℂ) :
    ∫ ω, ‖poly T c ω‖ ^ 2 ∂bernoulli X = ∑ E ∈ T, ‖c E‖ ^ 2 := by
  have key : ∀ ω, ((‖poly T c ω‖ ^ 2 : ℝ) : ℂ) = ∑ E ∈ T, ∑ F ∈ T,
      (c E * (starRingEnd ℂ) (c F)) * (walsh E ω * walsh F ω) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', poly, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F _ => ?_
    rw [map_mul, conj_walsh]; ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  have hint : ∀ E F : Finset X, Integrable (fun ω => walsh E ω * walsh F ω) (bernoulli X) :=
    fun E F => (integrable_walsh (E ∆ F)).congr
      (Filter.Eventually.of_forall fun ω => (walsh_mul E F ω).symm)
  rw [integral_finsetSum _ fun E _ => integrable_finsetSum _ fun F _ => (hint E F).const_mul _]
  have inner : ∀ E ∈ T, ∫ ω, ∑ F ∈ T, (c E * (starRingEnd ℂ) (c F)) * (walsh E ω * walsh F ω)
      ∂bernoulli X = c E * (starRingEnd ℂ) (c E) := by
    intro E hE
    rw [integral_finsetSum _ fun F _ => (hint E F).const_mul _]
    simp_rw [integral_const_mul, integral_walsh_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, if_pos hE]
  rw [Finset.sum_congr rfl inner]
  simp_rw [Complex.mul_conj']
  push_cast; rfl

lemma l2Norm_poly_sq (T : Finset (Finset X)) (c : Finset X → ℂ) :
    l2Norm (poly T c) ^ 2 = ∑ E ∈ T, ‖c E‖ ^ 2 := by
  rw [l2Norm_sq_eq (memLp_poly T c), integral_norm_sq_poly]

lemma poly_sub (T : Finset (Finset X)) (a b : Finset X → ℂ) :
    poly T a - poly T b = poly T (a - b) := by
  funext ω; simp [poly, sub_mul, Finset.sum_sub_distrib]

lemma poly_subset {T U : Finset (Finset X)} (h : T ⊆ U) (c : Finset X → ℂ)
    (hc : ∀ E ∈ U, E ∉ T → c E = 0) : poly U c = poly T c := by
  funext ω
  exact (Finset.sum_subset h fun E hU hT => by simp [hc E hU hT]).symm

lemma poly_image (σ : Finset X ≃ Finset X) (T : Finset (Finset X)) (c : Finset X → ℂ)
    (ω : X → Fin 2) :
    poly (T.image σ) (fun F => c (σ.symm F)) ω = ∑ E ∈ T, c E * walsh (σ E) ω := by
  unfold poly
  rw [Finset.sum_image fun E _ F _ h => σ.injective h]
  simp

/-- The span of the Walsh characters. -/
noncomputable def W (X : Type*) [DecidableEq X] : Submodule ℂ ((X → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (walsh (X := X)))

lemma walsh_mem_W (E : Finset X) : walsh E ∈ W X := Submodule.subset_span ⟨E, rfl⟩

lemma mul_mem_W (F : Finset X) {f : (X → Fin 2) → ℂ} (hf : f ∈ W X) :
    (fun ω => walsh F ω * f ω) ∈ W X := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨E, rfl⟩ := hx
    have : (fun ω => walsh F ω * walsh E ω) = walsh (F ∆ E) := funext fun ω => walsh_mul F E ω
    rw [this]; exact walsh_mem_W _
  | zero =>
    have : (fun ω => walsh F ω * (0 : (X → Fin 2) → ℂ) ω) = 0 := by funext ω; simp
    rw [this]; exact (W X).zero_mem
  | add x y _ _ hx hy =>
    have : (fun ω => walsh F ω * (x + y) ω) =
        (fun ω => walsh F ω * x ω) + (fun ω => walsh F ω * y ω) := by
      funext ω; simp [mul_add]
    rw [this]; exact add_mem hx hy
  | smul a x _ hx =>
    have : (fun ω => walsh F ω * (a • x) ω) = a • (fun ω => walsh F ω * x ω) := by
      funext ω; simp; ring
    rw [this]; exact Submodule.smul_mem _ a hx

lemma mem_W_poly {f : (X → Fin 2) → ℂ} (hf : f ∈ W X) : ∃ T c, f = poly T c := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  refine ⟨c.support, c, ?_⟩
  funext ω
  simp [Finsupp.sum, poly, Finset.sum_apply]

lemma walsh_singleton (x : X) (ω : X → Fin 2) : walsh {x} ω = sgn (ω x) := by
  simp [walsh]

lemma prod_mem_W (η : X → Fin 2) (t : Finset X) :
    (fun ω : X → Fin 2 => ∏ x ∈ t, (if ω x = η x then (1:ℂ) else 0)) ∈ W X := by
  induction t using Finset.induction_on with
  | empty =>
    have : (fun ω : X → Fin 2 => ∏ x ∈ (∅ : Finset X), (if ω x = η x then (1:ℂ) else 0)) =
        walsh ∅ := funext fun ω => by simp [walsh_empty]
    rw [this]; exact walsh_mem_W _
  | insert x t hx ih =>
    have : (fun ω : X → Fin 2 => ∏ y ∈ insert x t, (if ω y = η y then (1:ℂ) else 0)) =
        (1 / 2 : ℂ) • (fun ω : X → Fin 2 => ∏ y ∈ t, (if ω y = η y then (1:ℂ) else 0)) +
        (sgn (η x) / 2) • (fun ω => walsh {x} ω *
          (fun ω : X → Fin 2 => ∏ y ∈ t, (if ω y = η y then (1:ℂ) else 0)) ω) := by
      funext ω
      simp only [Finset.prod_insert hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        walsh_singleton]
      have key : (if ω x = η x then (1:ℂ) else 0) = 1 / 2 + sgn (η x) / 2 * sgn (ω x) := by
        unfold sgn
        rcases Fin.exists_fin_two.1 ⟨ω x, rfl⟩ with h1 | h1 <;>
          rcases Fin.exists_fin_two.1 ⟨η x, rfl⟩ with h2 | h2 <;> simp [h1, h2] <;> norm_num
      rw [key]; ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ ih) (Submodule.smul_mem _ _ (mul_mem_W {x} ih))

lemma cyl_mem_W (s : Finset X) (S : Set (s → Fin 2)) (a : ℂ) :
    (MeasureTheory.cylinder s S).indicator (fun _ => a) ∈ W X := by
  classical
  let ext : (s → Fin 2) → X → Fin 2 := fun η x => if h : x ∈ s then η ⟨x, h⟩ else 0
  have : (MeasureTheory.cylinder s S).indicator (fun _ => a) =
      ∑ η ∈ Finset.univ.filter (· ∈ S), a • (fun ω : X → Fin 2 =>
        ∏ x ∈ s, (if ω x = ext η x then (1:ℂ) else 0)) := by
    funext ω
    have hp : ∀ η : s → Fin 2, (∏ x ∈ s, (if ω x = ext η x then (1:ℂ) else 0)) =
        if s.restrict ω = η then 1 else 0 := by
      intro η
      rw [Finset.prod_boole]
      congr 1
      apply propext
      constructor
      · intro h; funext ⟨x, hx⟩; have := h x hx; simp [ext, hx] at this; exact this
      · intro h x hx; subst h; simp [ext, hx]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hp, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [Set.indicator, MeasureTheory.mem_cylinder]
  rw [this]
  exact Submodule.sum_mem _ fun η _ => Submodule.smul_mem _ _ (prod_mem_W _ _)

lemma exists_poly_near {f : (X → Fin 2) → ℂ} (hf : MemLp f 2 (bernoulli X)) {η : ℝ}
    (hη : 0 < η) : ∃ T c, l2Norm (f - poly T c) ≤ η := by
  have h2 : ∀ f : (X → Fin 2) → ℂ, f ∈ W X → AEStronglyMeasurable f (bernoulli X) := by
    intro f hf
    obtain ⟨T, c, rfl⟩ := mem_W_poly hf
    exact (measurable_poly T c).aestronglyMeasurable
  have h0 : ∀ (a : ℂ) ⦃s : Set (X → Fin 2)⦄, MeasurableSet s → bernoulli X s < ∞ →
      ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : (X → Fin 2) → ℂ,
        eLpNorm (g - s.indicator fun _ => a) 2 (bernoulli X) ≤ ε ∧ g ∈ W X := by
    intro a s hs _ ε hε
    have hD : ∃ D : Set (Set (X → Fin 2)), D.Countable ∧
        D ⊆ measurableCylinders (fun _ => Fin 2) ∧ bernoulli X (⋃₀ D)ᶜ = 0 :=
      ⟨{Set.univ}, Set.countable_singleton _, Set.singleton_subset_iff.2
        ((mem_measurableCylinders _).2 ⟨∅, Set.univ, .univ, (cylinder_univ _).symm⟩), by simp⟩
    have hδ : 0 < (ε / ‖a‖ₑ) ^ 2 :=
      ENNReal.pow_pos (ENNReal.div_pos hε enorm_ne_top) 2
    obtain ⟨t, ht, hμ⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      isSetRing_measurableCylinders hD generateFrom_measurableCylinders.symm hs hδ
    obtain ⟨s', S, -, rfl⟩ := (mem_measurableCylinders _).1 ht
    refine ⟨_, ?_, cyl_mem_W s' S a⟩
    rw [eLpNorm_indicator_sub_indicator, eLpNorm_indicator_const
      ((MeasurableSet.of_mem_measurableCylinders ht).symmDiff hs) two_ne_zero ENNReal.ofNat_ne_top]
    calc ‖a‖ₑ * bernoulli X (cylinder s' S ∆ s) ^ (1 / (2:ℝ≥0∞).toReal)
        ≤ ‖a‖ₑ * ((ε / ‖a‖ₑ) ^ 2) ^ (1 / (2:ℝ≥0∞).toReal) := by
          gcongr
      _ = ‖a‖ₑ * (ε / ‖a‖ₑ) := by
          congr 1
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ ε := ENNReal.mul_div_le
  obtain ⟨g, hg, hgW⟩ := hf.induction_dense ENNReal.ofNat_ne_top (· ∈ W X) h0
    (fun f g hf hg => add_mem hf hg) h2 (ENNReal.ofReal_pos.2 hη).ne'
  obtain ⟨T, c, rfl⟩ := mem_W_poly hgW
  exact ⟨T, c, ENNReal.toReal_le_of_le_ofReal hη.le hg⟩

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]
lemma mp_translate (g : G) : MeasurePreserving (fun ω : X → Fin 2 => fun x => ω (g • x))
    (bernoulli X) (bernoulli X) := by
  have := Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : X => (PMF.uniformOfFintype (Fin 2)).toMeasure) (MulAction.toPerm g).symm
  refine ⟨measurable_pi_lambda _ fun x => measurable_pi_apply _, ?_⟩
  unfold bernoulli
  convert this using 2
  funext ω x
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

lemma l2Norm_translate (g : G) {f : (X → Fin 2) → ℂ} (hf : AEStronglyMeasurable f (bernoulli X)) :
    l2Norm (translate g f) = l2Norm f := by
  unfold l2Norm translate
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving (f := fun ω : X → Fin 2 => fun x => ω (g • x)) hf (mp_translate g))

lemma memLp_translate (g : G) {f : (X → Fin 2) → ℂ} (hf : MemLp f 2 (bernoulli X)) :
    MemLp (translate g f) 2 (bernoulli X) :=
  hf.comp_measurePreserving (mp_translate g)

lemma translate_walsh (g : G) (E : Finset X) : translate g (walsh E) = walsh (g • E) := by
  funext ω
  simp only [translate, walsh, Finset.smul_finset_def]
  rw [Finset.prod_image fun x _ y _ h => MulAction.injective g h]

lemma translate_poly (g : G) (T : Finset (Finset X)) (c : Finset X → ℂ) :
    translate g (poly T c) = poly (T.image (MulAction.toPerm g))
      (fun F => c ((MulAction.toPerm g).symm F)) := by
  funext ω
  rw [poly_image]
  simp only [translate, poly]
  refine Finset.sum_congr rfl fun E _ => ?_
  exact congrArg _ (congrFun (translate_walsh g E) ω)

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {X : Type*} [DecidableEq X]
/-- The weight of a set of finite subsets for the coefficient function `c`. -/
noncomputable def wt (c : Finset X → ℂ) (A : Set (Finset X)) : ℝ :=
  ∑' E, A.indicator (fun E => ‖c E‖ ^ 2) E

lemma l1_finset (U : Finset (Finset X)) (a b : Finset X → ℂ) :
    ∑ E ∈ U, |‖a E‖ ^ 2 - ‖b E‖ ^ 2| ≤
      √(∑ E ∈ U, ‖a E - b E‖ ^ 2) * (√(∑ E ∈ U, ‖a E‖ ^ 2) + √(∑ E ∈ U, ‖b E‖ ^ 2)) := by
  have h1 : ∀ E ∈ U, |‖a E‖ ^ 2 - ‖b E‖ ^ 2| ≤
      ‖a E - b E‖ * ‖a E‖ + ‖a E - b E‖ * ‖b E‖ := by
    intro E _
    have h := abs_norm_sub_norm_le (a E) (b E)
    rw [show ‖a E‖ ^ 2 - ‖b E‖ ^ 2 = (‖a E‖ - ‖b E‖) * (‖a E‖ + ‖b E‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖a E‖ + ‖b E‖)]
    nlinarith [norm_nonneg (a E), norm_nonneg (b E), abs_nonneg (‖a E‖ - ‖b E‖)]
  calc _ ≤ ∑ E ∈ U, (‖a E - b E‖ * ‖a E‖ + ‖a E - b E‖ * ‖b E‖) := Finset.sum_le_sum h1
    _ = ∑ E ∈ U, ‖a E - b E‖ * ‖a E‖ + ∑ E ∈ U, ‖a E - b E‖ * ‖b E‖ := Finset.sum_add_distrib
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

lemma wt_eq_sum (c : Finset X → ℂ) (U : Finset (Finset X)) (hc : ∀ E ∉ U, c E = 0)
    (A : Set (Finset X)) : wt c A = ∑ E ∈ U, A.indicator (fun E => ‖c E‖ ^ 2) E :=
  tsum_eq_sum fun E hE => by simp [Set.indicator, hc E hE]

lemma wt_image (c : Finset X → ℂ) (τ : Finset X ≃ Finset X) (A : Set (Finset X)) :
    wt c (τ '' A) = wt (fun E => c (τ E)) A := by
  unfold wt
  rw [← τ.tsum_eq]
  congr 1; funext E
  by_cases h : E ∈ A <;> simp [Set.indicator, h]

lemma sum_comp_equiv (T : Finset (Finset X)) (c : Finset X → ℂ) (hc : ∀ E ∉ T, c E = 0)
    (τ : Finset X ≃ Finset X) (U : Finset (Finset X)) (hU : ∀ E ∉ U, c (τ E) = 0) :
    ∑ E ∈ U, ‖c (τ E)‖ ^ 2 = ∑ E ∈ T, ‖c E‖ ^ 2 := by
  have e1 : ∑' E, ‖c (τ E)‖ ^ 2 = ∑ E ∈ U, ‖c (τ E)‖ ^ 2 :=
    tsum_eq_sum fun E hE => by simp [hU E hE]
  have e2 : ∑' E, ‖c E‖ ^ 2 = ∑ E ∈ T, ‖c E‖ ^ 2 :=
    tsum_eq_sum fun E hE => by simp [hc E hE]
  rw [← e1, ← e2]
  exact τ.tsum_eq (fun E => ‖c E‖ ^ 2)

lemma l2Norm_poly (T : Finset (Finset X)) (c : Finset X → ℂ) :
    l2Norm (poly T c) = √(∑ E ∈ T, ‖c E‖ ^ 2) := by
  rw [← l2Norm_poly_sq, Real.sqrt_sq (l2Norm_nonneg _)]

lemma wt_close (T : Finset (Finset X)) (c : Finset X → ℂ) (hc : ∀ E ∉ T, c E = 0)
    (τ : Finset X ≃ Finset X) (A : Set (Finset X)) :
    |wt c (τ '' A) - wt c A| ≤
      2 * l2Norm (poly (T.image τ.symm) (fun F => c (τ F)) - poly T c) *
        √(∑ E ∈ T, ‖c E‖ ^ 2) := by
  set U := T ∪ T.image τ.symm with hUdef
  have hcU : ∀ E ∉ U, c E = 0 := fun E hE => hc E (fun h => hE (Finset.mem_union_left _ h))
  have hcτ : ∀ E ∉ T.image τ.symm, c (τ E) = 0 := fun E hE =>
    hc _ (fun h => hE (Finset.mem_image.2 ⟨τ E, h, by simp⟩))
  have hcτU : ∀ E ∉ U, c (τ E) = 0 := fun E hE => hcτ E (fun h => hE (Finset.mem_union_right _ h))
  rw [wt_image, wt_eq_sum _ U hcτU, wt_eq_sum _ U hcU, ← Finset.sum_sub_distrib]
  have hpoly : poly (T.image τ.symm) (fun F => c (τ F)) - poly T c =
      poly U (fun F => c (τ F) - c F) := by
    rw [← poly_subset Finset.subset_union_right (fun F => c (τ F)) (fun E _ hE => hcτ E hE),
      ← poly_subset Finset.subset_union_left c (fun E _ hE => hc E hE), poly_sub]
    rfl
  rw [hpoly, l2Norm_poly]
  have hN1 := sum_comp_equiv T c hc τ U hcτU
  have hN2 : ∑ E ∈ U, ‖c E‖ ^ 2 = ∑ E ∈ T, ‖c E‖ ^ 2 :=
    (Finset.sum_subset Finset.subset_union_left fun E _ hE => by simp [hc E hE]).symm
  have hl1 := l1_finset U (fun E => c (τ E)) c
  rw [hN1, hN2] at hl1
  calc _ ≤ ∑ E ∈ U, |A.indicator (fun E => ‖c (τ E)‖ ^ 2) E -
        A.indicator (fun E => ‖c E‖ ^ 2) E| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ E ∈ U, |‖c (τ E)‖ ^ 2 - ‖c E‖ ^ 2| := by
        refine Finset.sum_le_sum fun E _ => ?_
        by_cases h : E ∈ A <;> simp [Set.indicator, h]
    _ ≤ _ := hl1.trans (le_of_eq (by ring))

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]
lemma measurableSet_zero (x₀ : X) : MeasurableSet {ω : X → Fin 2 | ω x₀ = 0} :=
  measurable_pi_apply x₀ (measurableSet_singleton 0)

lemma l2_pythag (x₀ : X) {f : (X → Fin 2) → ℂ} (hf : MemLp f 2 (bernoulli X)) :
    l2Norm f ^ 2 = l2Norm (restrictZero x₀ f) ^ 2 + l2Norm (f - restrictZero x₀ f) ^ 2 := by
  have h1 : MemLp (restrictZero x₀ f) 2 (bernoulli X) := hf.indicator (measurableSet_zero x₀)
  have h2 := hf.sub h1
  rw [l2Norm_sq_eq hf, l2Norm_sq_eq h1, l2Norm_sq_eq h2, ← integral_add
    ((memLp_two_iff_integrable_sq_norm h1.1).1 h1) ((memLp_two_iff_integrable_sq_norm h2.1).1 h2)]
  congr 1; funext ω
  by_cases h : ω x₀ = 0 <;> simp [restrictZero, Set.indicator, h]

lemma l2Norm_sub_restrictZero_le (x₀ : X) {f : (X → Fin 2) → ℂ} (hf : MemLp f 2 (bernoulli X)) :
    l2Norm (f - restrictZero x₀ f) ≤ l2Norm f := by
  unfold l2Norm
  refine ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono fun ω => ?_)
  by_cases h : ω x₀ = 0 <;> simp [restrictZero, Set.indicator, h]

/-- The flip `E ↦ {x} ∆ E`. -/
def flipEquiv (x : X) : Finset X ≃ Finset X :=
  Function.Involutive.toPerm (fun E => {x} ∆ E)
    (fun E => symmDiff_symmDiff_cancel_left ({x} : Finset X) E)

lemma flipEquiv_symm_apply (x : X) (E : Finset X) : (flipEquiv x).symm E = {x} ∆ E := rfl

lemma walsh_mul_poly (x : X) (T : Finset (Finset X)) (c : Finset X → ℂ) :
    (fun ω => walsh {x} ω * poly T c ω) =
      poly (T.image (flipEquiv x).symm) (fun F => c (flipEquiv x F)) := by
  funext ω
  have := poly_image (flipEquiv x).symm T c ω
  rw [Equiv.symm_symm] at this
  rw [this]
  simp only [poly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [flipEquiv_symm_apply, ← walsh_mul]
  ring

lemma finite_step (x₀ : X) (hI : CondI G X x₀) (S : Finset G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (T : Finset (Finset X)) (c : Finset X → ℂ), (∀ E ∉ T, c E = 0) ∧
      0 < ∑ E ∈ T, ‖c E‖ ^ 2 ∧
      (∀ g ∈ S, ∀ A, |wt c ((MulAction.toPerm g).symm '' A) - wt c A| ≤
        δ * ∑ E ∈ T, ‖c E‖ ^ 2) ∧
      ∀ A, |wt c (flipEquiv x₀ '' A) - wt c A| ≤ δ * ∑ E ∈ T, ‖c E‖ ^ 2 := by
  set θ := min (1 / 2) (δ / 24) with hθdef
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
  have hθδ : θ ≤ δ / 24 := min_le_right _ _
  obtain ⟨f, hf, hfpos, hfS, hfz⟩ := hI S (θ ^ 2) (by positivity)
  set F := l2Norm f with hFdef
  obtain ⟨T, c₀, hp⟩ := exists_poly_near hf (η := θ * F) (by positivity)
  set c : Finset X → ℂ := fun E => if E ∈ T then c₀ E else 0 with hcdef
  have hc : ∀ E ∉ T, c E = 0 := fun E hE => if_neg hE
  have hpc : poly T c = poly T c₀ :=
    funext fun ω => Finset.sum_congr rfl fun E hE => by simp [c, hE]
  rw [← hpc] at hp
  set p := poly T c with hpdef
  have hpm : MemLp p 2 (bernoulli X) := memLp_poly T c
  set P := l2Norm p with hPdef
  have hN : ∑ E ∈ T, ‖c E‖ ^ 2 = P ^ 2 := (l2Norm_poly_sq T c).symm
  have hsqrt : √(∑ E ∈ T, ‖c E‖ ^ 2) = P := by rw [hN, Real.sqrt_sq (l2Norm_nonneg _)]
  have hfp' : l2Norm (p - f) ≤ θ * F := by rw [← l2Norm_neg, neg_sub]; exact hp
  have hPF : F ≤ l2Norm (f - p) + P := by
    have := l2Norm_add_le (hf.sub hpm) hpm
    rwa [sub_add_cancel] at this
  have hFP : F ≤ 2 * P := by nlinarith [mul_le_mul_of_nonneg_right hθ1 hfpos.le]
  have hPpos : 0 < P := by nlinarith
  have hP0 : 0 ≤ P := hPpos.le
  have htr : ∀ g ∈ S, l2Norm (translate g p - p) ≤ 3 * θ * F := by
    intro g hg
    have e : translate g p - p = (translate g (p - f) + (translate g f - f)) + (f - p) := by
      funext ω; simp [translate]
    have m1 : MemLp (translate g (p - f)) 2 (bernoulli X) := memLp_translate g (hpm.sub hf)
    have m2 : MemLp (translate g f - f) 2 (bernoulli X) := (memLp_translate g hf).sub hf
    rw [e]
    have a1 := l2Norm_add_le (m1.add m2) (hf.sub hpm)
    have a2 := l2Norm_add_le m1 m2
    have a3 := l2Norm_translate g (hpm.sub hf).1
    have a4 := hfS g hg
    have a5 : θ ^ 2 * F ≤ θ * F :=
      mul_le_mul_of_nonneg_right (by nlinarith) hfpos.le
    linarith
  have hrz : l2Norm (f - restrictZero x₀ f) ≤ 2 * θ * F := by
    have hpy := l2_pythag x₀ hf
    have h1' : 0 ≤ (1 - θ ^ 2) * F := mul_nonneg (by nlinarith) hfpos.le
    have h2 := pow_le_pow_left₀ h1' hfz 2
    have hsq : l2Norm (f - restrictZero x₀ f) ^ 2 ≤ (2 * θ * F) ^ 2 := by
      rw [← hFdef] at hpy; nlinarith
    exact (pow_le_pow_iff_left₀ (l2Norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hprz : l2Norm (p - restrictZero x₀ p) ≤ 3 * θ * F := by
    have e : p - restrictZero x₀ p =
        ((p - f) - restrictZero x₀ (p - f)) + (f - restrictZero x₀ f) := by
      funext ω; by_cases h : ω x₀ = 0 <;> simp [restrictZero, Set.indicator, h]
    have m1 : MemLp ((p - f) - restrictZero x₀ (p - f)) 2 (bernoulli X) :=
      (hpm.sub hf).sub ((hpm.sub hf).indicator (measurableSet_zero x₀))
    have m2 : MemLp (f - restrictZero x₀ f) 2 (bernoulli X) :=
      hf.sub (hf.indicator (measurableSet_zero x₀))
    rw [e]
    have := l2Norm_add_le m1 m2
    have := l2Norm_sub_restrictZero_le x₀ (hpm.sub hf)
    linarith
  have hflip : l2Norm ((fun ω => walsh {x₀} ω * p ω) - p) = 2 * l2Norm (p - restrictZero x₀ p) := by
    have e : (fun ω => walsh {x₀} ω * p ω) - p = (-2 : ℂ) • (p - restrictZero x₀ p) := by
      funext ω
      by_cases h : ω x₀ = 0
      · simp [restrictZero, Set.indicator, h, walsh_singleton, sgn]
      · simp [restrictZero, Set.indicator, h, walsh_singleton, sgn]; ring
    rw [e, l2Norm_smul]; norm_num
  refine ⟨T, c, hc, by rw [hN]; positivity, ?_, ?_⟩
  · intro g hg A
    have key := wt_close T c hc (MulAction.toPerm g).symm A
    rw [Equiv.symm_symm, ← translate_poly, hsqrt] at key
    have := htr g hg
    rw [hN]
    calc _ ≤ _ := key
      _ ≤ 2 * (3 * θ * F) * P := by gcongr
      _ ≤ δ * P ^ 2 := by
          have k1 : θ * F * P ≤ θ * (2 * P) * P := by gcongr
          have k2 : θ * P ^ 2 ≤ δ / 24 * P ^ 2 := by gcongr
          nlinarith [sq_nonneg P]
  · intro A
    have key := wt_close T c hc (flipEquiv x₀) A
    rw [← walsh_mul_poly, hsqrt, hflip] at key
    rw [hN]
    calc _ ≤ _ := key
      _ ≤ 2 * (2 * (3 * θ * F)) * P := by gcongr
      _ ≤ δ * P ^ 2 := by
          have k1 : θ * F * P ≤ θ * (2 * P) * P := by gcongr
          have k2 : θ * P ^ 2 ≤ δ / 24 * P ^ 2 := by gcongr
          nlinarith [sq_nonneg P]

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {Y I J : Type*}
lemma fa_mono {m : Set Y → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m) {A B : Set Y}
    (h : A ⊆ B) : m A ≤ m B := by
  have := hm.2 A (B \ A) Set.disjoint_sdiff_right
  rw [Set.union_sdiff_cancel h] at this
  rw [this]; exact le_self_add

lemma ultralimit [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (μ : I → Set Y → ℝ≥0∞) (hfa : ∀ i, Garrido.IsFinitelyAdditiveMeasure (μ i))
    (h1 : ∀ i, μ i Set.univ = 1) (Φ : J → Set Y → Set Y)
    (hΦ : ∀ j A, ∀ n : ℕ, ∃ i₀, ∀ i, i₀ ≤ i →
      |(μ i (Φ j A)).toReal - (μ i A).toReal| ≤ 1 / (n + 1)) :
    ∃ m : Set Y → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
      ∀ j A, m (Φ j A) = m A := by
  have : (Filter.atTop : Filter I).NeBot := Filter.atTop_neBot
  let U : Ultrafilter I := Ultrafilter.of Filter.atTop
  have hU : (U : Filter I) ≤ Filter.atTop := Ultrafilter.of_le _
  have hlim : ∀ A : Set Y, ∃ L : ℝ≥0∞, Filter.Tendsto (fun i => μ i A) U (nhds L) := by
    intro A
    obtain ⟨L, -, hL⟩ := isCompact_univ.ultrafilter_le_nhds (U.map (fun i => μ i A)) (by simp)
    exact ⟨L, hL⟩
  choose L hL using hlim
  have hfin : ∀ i A, μ i A ≠ ⊤ := fun i A =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (h1 i ▸ fa_mono (hfa i) (Set.subset_univ A))
  have key : ∀ A B : Set Y, (∀ n : ℕ, ∃ i₀, ∀ i, i₀ ≤ i →
      |(μ i B).toReal - (μ i A).toReal| ≤ 1 / (n + 1)) → L B ≤ L A := by
    intro A B h
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε by exact_mod_cast hε)
    obtain ⟨i₀, hi₀⟩ := h n
    have hev : ∀ᶠ i in (U : Filter I), μ i B ≤ μ i A + ENNReal.ofReal (1 / (n + 1)) := by
      filter_upwards [hU (Filter.eventually_ge_atTop i₀)] with i hi
      have := hi₀ i hi
      rw [abs_le] at this
      rw [← ENNReal.ofReal_toReal (hfin i B), ← ENNReal.ofReal_toReal (hfin i A),
        ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have := le_of_tendsto_of_tendsto (hL B) ((hL A).add tendsto_const_nhds) hev
    refine this.trans (add_le_add le_rfl ?_)
    calc ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ ENNReal.ofReal (ε : ℝ) :=
          ENNReal.ofReal_le_ofReal hn.le
      _ = ε := ENNReal.ofReal_coe_nnreal
  refine ⟨L, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact tendsto_nhds_unique (hL ∅)
      (by simp [(hfa _).1])
  · intro A B hAB
    refine tendsto_nhds_unique (hL _) ?_
    simp only [(hfa _).2 A B hAB]
    exact (hL A).add (hL B)
  · exact tendsto_nhds_unique (hL _) (by simp [h1])
  · intro j A
    exact le_antisymm (key A (Φ j A) (hΦ j A))
      (key (Φ j A) A fun n => by
        obtain ⟨i₀, h⟩ := hΦ j A n
        exact ⟨i₀, fun i hi => by rw [abs_sub_comm]; exact h i hi⟩)

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]
lemma wt_nonneg (c : Finset X → ℂ) (A : Set (Finset X)) : 0 ≤ wt c A :=
  tsum_nonneg fun E => Set.indicator_nonneg (fun E _ => by positivity) E

/-- The normalised weights as a finitely additive probability. -/
noncomputable def nu (T : Finset (Finset X)) (c : Finset X → ℂ) (A : Set (Finset X)) : ℝ≥0∞ :=
  ENNReal.ofReal (wt c A / ∑ E ∈ T, ‖c E‖ ^ 2)

lemma nu_fa (T : Finset (Finset X)) (c : Finset X → ℂ) (hc : ∀ E ∉ T, c E = 0) :
    Garrido.IsFinitelyAdditiveMeasure (nu T c) := by
  refine ⟨by simp [nu, wt], fun A B hAB => ?_⟩
  have hN : 0 ≤ ∑ E ∈ T, ‖c E‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  unfold nu
  rw [← ENNReal.ofReal_add (div_nonneg (wt_nonneg c A) hN) (div_nonneg (wt_nonneg c B) hN),
    ← add_div]
  congr 2
  rw [wt_eq_sum c T hc, wt_eq_sum c T hc, wt_eq_sum c T hc, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun E _ => congrFun (Set.indicator_union_of_disjoint hAB _) E

lemma nu_univ (T : Finset (Finset X)) (c : Finset X → ℂ) (hc : ∀ E ∉ T, c E = 0)
    (hN : 0 < ∑ E ∈ T, ‖c E‖ ^ 2) : nu T c Set.univ = 1 := by
  unfold nu
  rw [wt_eq_sum c T hc]
  simp only [Set.indicator_univ]
  rw [div_self hN.ne', ENNReal.ofReal_one]

lemma nu_close (T : Finset (Finset X)) (c : Finset X → ℂ) (hN : 0 < ∑ E ∈ T, ‖c E‖ ^ 2)
    {δ : ℝ} (A B : Set (Finset X)) (h : |wt c B - wt c A| ≤ δ * ∑ E ∈ T, ‖c E‖ ^ 2) :
    |(nu T c B).toReal - (nu T c A).toReal| ≤ δ := by
  unfold nu
  rw [ENNReal.toReal_ofReal (div_nonneg (wt_nonneg c B) hN.le),
    ENNReal.toReal_ofReal (div_nonneg (wt_nonneg c A) hN.le), ← sub_div, abs_div,
    abs_of_pos hN, div_le_iff₀ hN]
  exact h

lemma exists_invariant (x₀ : X) (hI : CondI G X x₀) :
    ∃ m : Set (Finset X) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
      (∀ (g : G) A, m ((MulAction.toPerm g).symm '' A) = m A) ∧
      ∀ A, m (flipEquiv x₀ '' A) = m A := by
  classical
  have hstep : ∀ i : Finset G × ℕ, ∃ (T : Finset (Finset X)) (c : Finset X → ℂ),
      (∀ E ∉ T, c E = 0) ∧ 0 < ∑ E ∈ T, ‖c E‖ ^ 2 ∧
      (∀ g ∈ i.1, ∀ A, |wt c ((MulAction.toPerm g).symm '' A) - wt c A| ≤
        1 / (i.2 + 1) * ∑ E ∈ T, ‖c E‖ ^ 2) ∧
      ∀ A, |wt c (flipEquiv x₀ '' A) - wt c A| ≤ 1 / (i.2 + 1) * ∑ E ∈ T, ‖c E‖ ^ 2 :=
    fun i => finite_step x₀ hI i.1 (by positivity)
  choose T c hc hN hg hf using hstep
  let Φ : Option G → Set (Finset X) → Set (Finset X) := fun j A =>
    match j with
    | none => flipEquiv x₀ '' A
    | some g => (MulAction.toPerm g).symm '' A
  have hmono : ∀ n n' : ℕ, n ≤ n' → (1 : ℝ) / (n' + 1) ≤ 1 / (n + 1) := fun n n' h => by
    gcongr
  obtain ⟨m, hm, hm1, hmΦ⟩ := ultralimit (fun i => nu (T i) (c i)) (fun i => nu_fa _ _ (hc i))
    (fun i => nu_univ _ _ (hc i) (hN i)) Φ (by
      intro j A n
      cases j with
      | none =>
        refine ⟨(∅, n), fun i hi => ?_⟩
        exact (nu_close _ _ (hN i) _ _ (hf i A)).trans (hmono _ _ hi.2)
      | some g =>
        refine ⟨({g}, n), fun i hi => ?_⟩
        exact (nu_close _ _ (hN i) _ _ (hg i g (hi.1 (Finset.mem_singleton_self g)) A)).trans
          (hmono _ _ hi.2))
  exact ⟨m, hm, hm1, fun g A => hmΦ (some g) A, fun A => hmΦ none A⟩

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise symmDiff
set_option linter.unusedSectionVars false
namespace JuschenkoMonod.L31.PartC
lemma inv_image_eq {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] (g : G)
    (A : Set (Finset X)) : (MulAction.toPerm g⁻¹).symm '' A = (fun E => g • E) '' A := by
  congr 1; funext E; simp

/-- Part C: (i) ⇒ (ii). -/
theorem i_imp_ii (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
    [MulAction.IsPretransitive G X] : CondI G X x₀ → CondII G X := by
  intro hI
  obtain ⟨m, hm, hm1, hmg, hmf⟩ := exists_invariant x₀ hI
  have hsmul : ∀ (g : G) (A : Set (Finset X)), m ((fun E : Finset X => g • E) '' A) = m A :=
    fun g A => by rw [← inv_image_eq]; exact hmg g⁻¹ A
  have hx0 : ∀ A : Set (Finset X), m ((fun E => {x₀} ∆ E) '' A) = m A := hmf
  have hx : ∀ x : X, ∀ A : Set (Finset X), m ((fun E => {x} ∆ E) '' A) = m A := by
    intro x A
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G x₀ x
    have e : (fun E : Finset X => {h • x₀} ∆ E) '' A =
        (fun E => h • E) '' ((fun E => {x₀} ∆ E) '' ((fun E => h⁻¹ • E) '' A)) := by
      rw [Set.image_image, Set.image_image]
      congr 1; funext E
      rw [Finset.smul_finset_symmDiff, Finset.smul_finset_singleton, smul_inv_smul]
    rw [e, hsmul, hx0, hsmul]
  have hF : ∀ F : Finset X, ∀ A : Set (Finset X), m ((fun E => F ∆ E) '' A) = m A := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro A
      have : (fun E : Finset X => (∅ : Finset X) ∆ E) = id := funext fun E => bot_symmDiff E
      rw [this, Set.image_id]
    | insert x F hxF ih =>
      intro A
      have e : (fun E => (insert x F) ∆ E) '' A =
          (fun E => {x} ∆ E) '' ((fun E => F ∆ E) '' A) := by
        rw [Set.image_image]; congr 1; funext E
        rw [← symmDiff_assoc, Finset.insert_eq,
          Disjoint.symmDiff_eq_sup (Finset.disjoint_singleton_left.2 hxF)]
        rfl
      rw [e, hx, ih]
  refine ⟨m, hm, hm1, fun F g S => ?_⟩
  have e : (fun E => F ∆ (g • E)) '' S = (fun E => F ∆ E) '' ((fun E => g • E) '' S) := by
    rw [Set.image_image]
  rw [e, hF, hsmul]

end JuschenkoMonod.L31.PartC
end

section
open MeasureTheory
open scoped ENNReal Pointwise
namespace JuschenkoMonod.L31
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
alias i_imp_ii := JuschenkoMonod.L31.PartC.i_imp_ii

end JuschenkoMonod.L31
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
variable {X : Type*} {m : Set X → ℝ≥0∞}
theorem fa_mono (hm : IsFinitelyAdditiveMeasure m) {S T : Set X} (h : S ⊆ T) : m S ≤ m T := by
  have := hm.2 S (T \ S) Set.disjoint_sdiff_right
  rw [Set.union_sdiff_cancel h] at this
  rw [this]; exact le_self_add

theorem fa_sum (hm : IsFinitelyAdditiveMeasure m) {ι : Type*} (s : Finset ι) (S : ι → Set X)
    (hd : (s : Set ι).PairwiseDisjoint S) : m (⋃ i ∈ s, S i) = ∑ i ∈ s, m (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hm.1
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, hm.2, ih (hd.subset (by simp))]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
open Classical
variable {Y : Type*} [Nonempty Y]
noncomputable def sig (F : Finset (Set Y)) (y : Y) : Finset (Set Y) := F.filter (fun B => y ∈ B)

def atom (F : Finset (Set Y)) (σ : Finset (Set Y)) : Set Y := {y | sig F y = σ}

noncomputable def rep (F : Finset (Set Y)) (σ : Finset (Set Y)) : Y :=
  if h : (atom F σ).Nonempty then h.choose else Classical.arbitrary Y

theorem rep_mem {F : Finset (Set Y)} {σ : Finset (Set Y)} (h : (atom F σ).Nonempty) :
    rep F σ ∈ atom F σ := by
  unfold rep; rw [dif_pos h]; exact h.choose_spec

theorem sig_mem (F : Finset (Set Y)) (y : Y) : sig F y ∈ F.powerset := by
  simp [sig]

theorem atom_disjoint (F : Finset (Set Y)) :
    ((F.powerset : Finset (Finset (Set Y))) : Set (Finset (Set Y))).PairwiseDisjoint (atom F) := by
  intro σ _ σ' _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro y h h'
  exact hne (h.symm.trans h')

theorem iUnion_atom (F : Finset (Set Y)) : ⋃ σ ∈ F.powerset, atom F σ = Set.univ := by
  ext y; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨sig F y, sig_mem F y, rfl⟩

theorem mem_iff_of_atom {F : Finset (Set Y)} {σ : Finset (Set Y)} {y y' : Y} (hy : y ∈ atom F σ)
    (hy' : y' ∈ atom F σ) {B : Set Y} (hB : B ∈ F) : y ∈ B ↔ y' ∈ B := by
  have h1 : sig F y = sig F y' := hy.trans hy'.symm
  have : B ∈ sig F y ↔ B ∈ sig F y' := by rw [h1]
  simpa [sig, hB] using this

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
open Classical
variable {Y : Type*} [Nonempty Y]
variable (μ : Set Y → ℝ≥0∞)
/-- exact formula: a function with level sets in `F` -/
theorem sum_atom_level (hμ : IsFinitelyAdditiveMeasure μ) (F : Finset (Set Y)) (n : ℕ)
    (q : Y → ℕ) (hq : ∀ y, q y ≤ n) (hF : ∀ j ∈ Finset.range (n + 1), {y | q y = j} ∈ F) :
    ∑ σ ∈ F.powerset, μ (atom F σ) * (q (rep F σ) : ℝ≥0∞) =
      ∑ j ∈ Finset.range (n + 1), (j : ℝ≥0∞) * μ {y | q y = j} := by
  -- q is constant on atoms
  have hconst : ∀ σ y, y ∈ atom F σ → q y = q (rep F σ) := by
    intro σ y hy
    have hne : (atom F σ).Nonempty := ⟨y, hy⟩
    have hr := rep_mem hne
    have := mem_iff_of_atom hy hr (hF (q y) (Finset.mem_range.2 (Nat.lt_succ_of_le (hq y))))
    exact (this.1 rfl).symm
  have hlevel : ∀ j, {y | q y = j} = ⋃ σ ∈ F.powerset.filter (fun σ => q (rep F σ) = j), atom F σ := by
    intro j; ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro h
      exact ⟨sig F y, ⟨sig_mem F y, by rw [← hconst (sig F y) y rfl, h]⟩, rfl⟩
    · rintro ⟨σ, ⟨_, h⟩, hy⟩
      rw [hconst σ y hy, h]
  have hmu : ∀ j, μ {y | q y = j} = ∑ σ ∈ F.powerset.filter (fun σ => q (rep F σ) = j), μ (atom F σ) := by
    intro j
    rw [hlevel j, fa_sum hμ]
    exact (atom_disjoint F).subset (by intro σ hσ; simpa using (Finset.mem_filter.1 hσ).1)
  simp_rw [hmu, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := F.powerset) (t := Finset.range (n + 1))
      (g := fun σ => q (rep F σ)) (fun σ _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hq _)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2, mul_comm]

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
theorem real_bounds {ι : Type*} (s : Finset ι) (w g : ι → ℝ) (q : ι → ℕ) (n : ℕ) (hn : 0 < n)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (h1 : ∀ i, (q i : ℝ) ≤ n * g i)
    (h2 : ∀ i, (n : ℝ) * g i < q i + 1) :
    (1 / n) * ∑ i ∈ s, w i * q i ≤ ∑ i ∈ s, w i * g i ∧
      ∑ i ∈ s, w i * g i ≤ (1 / n) * ∑ i ∈ s, w i * q i + 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := h1 i
    have h3 : (1 / (n : ℝ)) * q i ≤ g i := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn']; linarith
    calc 1 / (n : ℝ) * (w i * q i) = w i * (1 / n * q i) := by ring
      _ ≤ w i * g i := mul_le_mul_of_nonneg_left h3 (hw i)
  · have : (1 / (n : ℝ)) = ∑ i ∈ s, w i * (1 / n) := by rw [← Finset.sum_mul, hsum, one_mul]
    rw [Finset.mul_sum]
    nth_rewrite 2 [this]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := h2 i
    have h3 : g i ≤ 1 / (n : ℝ) * q i + 1 / n := by
      have : g i < (q i + 1) / n := by rw [lt_div_iff₀ hn']; linarith
      calc g i ≤ (q i + 1) / n := this.le
        _ = 1 / (n : ℝ) * q i + 1 / n := by ring
    calc w i * g i ≤ w i * (1 / (n : ℝ) * q i + 1 / n) := mul_le_mul_of_nonneg_left h3 (hw i)
      _ = 1 / (n : ℝ) * (w i * q i) + w i * (1 / n) := by ring

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
open Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [MulAction H X] [Nonempty Y]
noncomputable def mF (μ : Set Y → ℝ≥0∞) (Φ : Y → Set X → ℝ≥0∞) (F : Finset (Set Y)) (A : Set X) :
    ℝ≥0∞ :=
  ∑ σ ∈ F.powerset, μ (atom F σ) * Φ (rep F σ) A

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
open Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [MulAction H X] [Nonempty Y]
variable {μ : Set Y → ℝ≥0∞} {Φ : Y → Set X → ℝ≥0∞}
theorem sum_atom_mu (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (F : Finset (Set Y)) : ∑ σ ∈ F.powerset, μ (atom F σ) = 1 := by
  rw [← fa_sum hμ _ _ (atom_disjoint F), iUnion_atom, hμ1]

theorem mu_ne_top (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1) (S : Set Y) :
    μ S ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hμ1 ▸ fa_mono hμ (Set.subset_univ S))

theorem mF_empty (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (F : Finset (Set Y)) :
    mF μ Φ F ∅ = 0 := by
  simp [mF, (hΦ _).1]

theorem mF_union (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (F : Finset (Set Y)) (A B : Set X)
    (h : Disjoint A B) : mF μ Φ F (A ∪ B) = mF μ Φ F A + mF μ Φ F B := by
  simp only [mF, (hΦ _).2 A B h, mul_add, Finset.sum_add_distrib]

theorem mF_univ (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hΦ1 : ∀ y, Φ y Set.univ = 1) (F : Finset (Set Y)) : mF μ Φ F Set.univ = 1 := by
  simp only [mF, hΦ1, mul_one]; exact sum_atom_mu hμ hμ1 F

theorem toReal_mF (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (hΦ1 : ∀ y, Φ y Set.univ = 1) (F : Finset (Set Y))
    (A : Set X) :
    (mF μ Φ F A).toReal = ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (Φ (rep F σ) A).toReal := by
  unfold mF
  rw [ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro σ _
    refine ENNReal.mul_ne_top (mu_ne_top hμ hμ1 _) ?_
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hΦ1 _ ▸ fa_mono (hΦ _) (Set.subset_univ A))

theorem mF_close (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hμi : IsInvariant H μ) (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y))
    (hΦ1 : ∀ y, Φ y Set.univ = 1)
    (hΦk : ∀ (k : H) (y : Y) (A : Set X), Φ (k • y) (k • A) = Φ y A) (k : H) (A : Set X)
    (n : ℕ) (hn : 0 < n) :
    ∃ F₀ : Finset (Set Y), ∀ F, F₀ ⊆ F →
      |(mF μ Φ F (k • A)).toReal - (mF μ Φ F A).toReal| ≤ 1 / n := by
  have hΦle : ∀ y (B : Set X), (Φ y B).toReal ≤ 1 := fun y B => by
    have : Φ y B ≤ 1 := hΦ1 y ▸ fa_mono (hΦ y) (Set.subset_univ B)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  set f : Y → ℝ := fun y => (Φ y A).toReal with hfdef
  have hf0 : ∀ y, 0 ≤ f y := fun y => ENNReal.toReal_nonneg
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set q : Y → ℕ := fun y => ⌊(n : ℝ) * f y⌋₊ with hqdef
  have hq : ∀ y, q y ≤ n := fun y => Nat.floor_le_of_le (by
    have := hΦle y A
    nlinarith [hf0 y])
  have hfk : ∀ y, (Φ y (k • A)).toReal = f (k⁻¹ • y) := fun y => by
    have := hΦk k (k⁻¹ • y) A
    rw [smul_inv_smul] at this
    simp [hfdef, this]
  let Lj : ℕ → Set Y := fun j => {y | q y = j}
  refine ⟨(Finset.range (n + 1)).image Lj ∪ (Finset.range (n + 1)).image (fun j => k • Lj j), ?_⟩
  intro F hF
  have hF1 : ∀ j ∈ Finset.range (n + 1), {y | q y = j} ∈ F := fun j hj =>
    hF (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj))
  have hset : ∀ j, {y | q (k⁻¹ • y) = j} = k • Lj j := by
    intro j; ext y
    simp [Lj, Set.mem_smul_set_iff_inv_smul_mem]
  have hF2 : ∀ j ∈ Finset.range (n + 1), {y | q (k⁻¹ • y) = j} ∈ F := fun j hj => by
    rw [hset]; exact hF (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
  have E1 := sum_atom_level μ hμ F n q hq hF1
  have E2 := sum_atom_level μ hμ F n (fun y => q (k⁻¹ • y)) (fun y => hq _) hF2
  have hE : ∑ σ ∈ F.powerset, μ (atom F σ) * (q (rep F σ) : ℝ≥0∞) =
      ∑ σ ∈ F.powerset, μ (atom F σ) * (q (k⁻¹ • rep F σ) : ℝ≥0∞) := by
    rw [E1, E2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hset, hμi k]
  have hw : ∀ σ, 0 ≤ (μ (atom F σ)).toReal := fun σ => ENNReal.toReal_nonneg
  have hsum : ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun σ _ => mu_ne_top hμ hμ1 _), sum_atom_mu hμ hμ1]; simp
  have hE' : ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (q (rep F σ) : ℝ) =
      ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (q (k⁻¹ • rep F σ) : ℝ) := by
    have := congrArg ENNReal.toReal hE
    rw [ENNReal.toReal_sum, ENNReal.toReal_sum] at this
    · simpa [ENNReal.toReal_mul] using this
    · intro σ _; exact ENNReal.mul_ne_top (mu_ne_top hμ hμ1 _) (by simp)
    · intro σ _; exact ENNReal.mul_ne_top (mu_ne_top hμ hμ1 _) (by simp)
  have B1 := real_bounds F.powerset (fun σ => (μ (atom F σ)).toReal) (fun σ => f (rep F σ))
    (fun σ => q (rep F σ)) n hn hw hsum
    (fun σ => by simpa [hqdef] using Nat.floor_le (mul_nonneg hnr.le (hf0 (rep F σ))))
    (fun σ => by simpa [hqdef] using Nat.lt_floor_add_one ((n : ℝ) * f (rep F σ)))
  have B2 := real_bounds F.powerset (fun σ => (μ (atom F σ)).toReal) (fun σ => f (k⁻¹ • rep F σ))
    (fun σ => q (k⁻¹ • rep F σ)) n hn hw hsum
    (fun σ => by simpa [hqdef] using Nat.floor_le (mul_nonneg hnr.le (hf0 (k⁻¹ • rep F σ))))
    (fun σ => by simpa [hqdef] using Nat.lt_floor_add_one ((n : ℝ) * f (k⁻¹ • rep F σ)))
  rw [toReal_mF hμ hμ1 hΦ hΦ1, toReal_mF hμ hμ1 hΦ hΦ1]
  simp only [hfk]
  have e1 : ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (Φ (rep F σ) A).toReal =
      ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * f (rep F σ) := rfl
  rw [e1, abs_le]
  rw [hE'] at B1
  constructor <;> linarith [B1.1, B1.2, B2.1, B2.2]

theorem le_add_ofReal_of_toReal {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : a.toReal ≤ b.toReal + δ) : a ≤ b + ENNReal.ofReal δ := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + δ) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal b.toReal + ENNReal.ofReal δ := ENNReal.ofReal_add ENNReal.toReal_nonneg hδ
    _ = b + ENNReal.ofReal δ := by rw [ENNReal.ofReal_toReal hb]

theorem mF_ge (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1) (F : Finset (Set Y))
    (B : Set Y) (hB : B ∈ F) (A : Set X) (c₁ c₂ : ℝ≥0∞) (h1 : ∀ y ∈ B, c₁ ≤ Φ y A)
    (h2 : ∀ y, y ∉ B → c₂ ≤ Φ y A) : c₁ * μ B + c₂ * μ Bᶜ ≤ mF μ Φ F A := by
  have hB1 : B = ⋃ σ ∈ F.powerset.filter (fun σ => B ∈ σ), atom F σ := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro hy
      exact ⟨sig F y, ⟨sig_mem F y, by simp [sig, hB, hy]⟩, rfl⟩
    · rintro ⟨σ, ⟨_, hσ⟩, hy⟩
      have : B ∈ sig F y := by rw [hy]; exact hσ
      simpa [sig, hB] using this
  have hB2 : Bᶜ = ⋃ σ ∈ F.powerset.filter (fun σ => B ∉ σ), atom F σ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro hy
      exact ⟨sig F y, ⟨sig_mem F y, by simp [sig, hB, hy]⟩, rfl⟩
    · rintro ⟨σ, ⟨_, hσ⟩, hy⟩ hyB
      have : B ∈ sig F y := by simp [sig, hB, hyB]
      rw [hy] at this; exact hσ this
  have dis : ∀ (p : Finset (Set Y) → Prop) [DecidablePred p],
      ((F.powerset.filter p : Finset (Finset (Set Y))) :
      Set (Finset (Set Y))).PairwiseDisjoint (atom F) := fun p _ =>
    (atom_disjoint F).subset (by intro σ hσ; simpa using (Finset.mem_filter.1 hσ).1)
  have e1 : μ B = ∑ σ ∈ F.powerset.filter (fun σ => B ∈ σ), μ (atom F σ) := by
    conv_lhs => rw [hB1]
    exact fa_sum hμ _ _ (dis _)
  have e2 : μ Bᶜ = ∑ σ ∈ F.powerset.filter (fun σ => B ∉ σ), μ (atom F σ) := by
    conv_lhs => rw [hB2]
    exact fa_sum hμ _ _ (dis _)
  rw [e1, e2, Finset.mul_sum, Finset.mul_sum]
  unfold mF
  rw [← Finset.sum_filter_add_sum_filter_not F.powerset (fun σ => B ∈ σ)]
  refine add_le_add (Finset.sum_le_sum fun σ hσ => ?_) (Finset.sum_le_sum fun σ hσ => ?_)
  · rw [mul_comm c₁]
    by_cases hne : (atom F σ).Nonempty
    · have hr := rep_mem hne
      have hrB : rep F σ ∈ B := by
        have : B ∈ sig F (rep F σ) := by rw [hr]; exact (Finset.mem_filter.1 hσ).2
        simpa [sig, hB] using this
      gcongr; exact h1 _ hrB
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, hμ.1]; simp
  · rw [mul_comm c₂]
    by_cases hne : (atom F σ).Nonempty
    · have hr := rep_mem hne
      have hrB : rep F σ ∉ B := by
        intro hb
        have : B ∈ sig F (rep F σ) := by simp [sig, hB, hb]
        rw [hr] at this; exact (Finset.mem_filter.1 hσ).2 this
      gcongr; exact h2 _ hrB
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, hμ.1]; simp

theorem mF_congr (hμ : IsFinitelyAdditiveMeasure μ) (F : Finset (Set Y)) (B : Set Y) (hB : B ∈ F)
    (hB0 : μ Bᶜ = 0) (A A' : Set X) (h : ∀ y ∈ B, Φ y A = Φ y A') :
    mF μ Φ F A = mF μ Φ F A' := by
  unfold mF
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hne : (atom F σ).Nonempty
  · by_cases hBσ : B ∈ σ
    · have hr : sig F (rep F σ) = σ := rep_mem hne
      have hrB : rep F σ ∈ B := by
        have : B ∈ sig F (rep F σ) := by rw [hr]; exact hBσ
        simpa [sig, hB] using this
      rw [h _ hrB]
    · have hsub : atom F σ ⊆ Bᶜ := by
        intro y hy hyB
        have : B ∈ sig F y := by simp [sig, hB, hyB]
        rw [show sig F y = σ from hy] at this; exact hBσ this
      have : μ (atom F σ) = 0 := le_antisymm (hB0 ▸ fa_mono hμ hsub) bot_le
      simp [this]
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, hμ.1]; simp

theorem exists_invariant_of_barycenter (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hμi : IsInvariant H μ) (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y))
    (hΦ1 : ∀ y, Φ y Set.univ = 1)
    (hΦk : ∀ (k : H) (y : Y) (A : Set X), Φ (k • y) (k • A) = Φ y A) :
    ∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧ IsInvariant H m ∧
      (∀ (B : Set Y) (A : Set X) (c₁ c₂ : ℝ≥0∞), (∀ y ∈ B, c₁ ≤ Φ y A) → (∀ y, y ∉ B → c₂ ≤ Φ y A) →
        c₁ * μ B + c₂ * μ Bᶜ ≤ m A) ∧
      ∀ (B : Set Y) (A A' : Set X), μ Bᶜ = 0 → (∀ y ∈ B, Φ y A = Φ y A') → m A = m A' := by
  haveI : (Filter.atTop : Filter (Finset (Set Y))).NeBot := Filter.atTop_neBot
  let U : Ultrafilter (Finset (Set Y)) := Ultrafilter.of Filter.atTop
  have hU : (U : Filter (Finset (Set Y))) ≤ Filter.atTop := Ultrafilter.of_le _
  have hlim : ∀ A : Set X, ∃ L : ℝ≥0∞, Filter.Tendsto (fun F => mF μ Φ F A) U (nhds L) := by
    intro A
    obtain ⟨L, -, hL⟩ := isCompact_univ.ultrafilter_le_nhds (U.map (fun F => mF μ Φ F A)) (by simp)
    exact ⟨L, hL⟩
  choose L hL using hlim
  have hFA : ∀ F, IsFinitelyAdditiveMeasure (mF μ Φ F) := fun F => ⟨mF_empty hΦ F, mF_union hΦ F⟩
  have hfin : ∀ F A, mF μ Φ F A ≠ ⊤ := fun F A =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (mF_univ hμ hμ1 hΦ1 F ▸ fa_mono (hFA F) (Set.subset_univ A))
  refine ⟨L, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact tendsto_nhds_unique (hL ∅) (by simpa [mF_empty hΦ] using tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  · intro A B hAB
    refine tendsto_nhds_unique (hL _) ?_
    simp only [mF_union hΦ _ A B hAB]
    exact (hL A).add (hL B)
  · exact tendsto_nhds_unique (hL _) (by simpa [mF_univ hμ hμ1 hΦ1] using tendsto_const_nhds (x := (1 : ℝ≥0∞)))
  · intro k A
    have key : ∀ (A B : Set X) (k : H), (∀ n : ℕ, 0 < n → ∃ F₀ : Finset (Set Y), ∀ F, F₀ ⊆ F →
        |(mF μ Φ F B).toReal - (mF μ Φ F A).toReal| ≤ 1 / n) → L B ≤ L A := by
      intro A B k h
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε by exact_mod_cast hε)
      obtain ⟨F₀, hF₀⟩ := h (n + 1) (Nat.succ_pos n)
      have hev : ∀ᶠ F in (U : Filter (Finset (Set Y))), mF μ Φ F B ≤ mF μ Φ F A + ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) := by
        filter_upwards [hU (Filter.eventually_ge_atTop F₀)] with F hF
        refine le_add_ofReal_of_toReal (hfin _ _) (hfin _ _) (by positivity) ?_
        have := hF₀ F hF
        rw [abs_le] at this; linarith
      have := le_of_tendsto_of_tendsto (hL B) ((hL A).add tendsto_const_nhds) hev
      refine this.trans (add_le_add_right ?_ _)
      have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      calc ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) ≤ ENNReal.ofReal (ε : ℝ) :=
            ENNReal.ofReal_le_ofReal (by rw [hc]; exact hn.le)
        _ = ε := ENNReal.ofReal_coe_nnreal
    exact le_antisymm (key A (k • A) k fun n hn => by
        obtain ⟨F₀, h⟩ := mF_close hμ hμ1 hμi hΦ hΦ1 hΦk k A n hn; exact ⟨F₀, h⟩)
      (key (k • A) A k fun n hn => by
        obtain ⟨F₀, h⟩ := mF_close hμ hμ1 hμi hΦ hΦ1 hΦk k A n hn
        exact ⟨F₀, fun F hF => by rw [abs_sub_comm]; exact h F hF⟩)
  · intro B A c₁ c₂ h1 h2
    refine ge_of_tendsto (hL A) ?_
    filter_upwards [hU (Filter.eventually_ge_atTop {B})] with F hF
    exact mF_ge hμ hμ1 F B (hF (Finset.mem_singleton_self B)) A c₁ c₂ h1 h2
  · intro B A A' hB0 h
    refine tendsto_nhds_unique (hL A) ((hL A').congr' ?_)
    filter_upwards [hU (Filter.eventually_ge_atTop {B})] with F hF
    exact (mF_congr hμ F B (hF (Finset.mem_singleton_self B)) hB0 A A' h).symm

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
open Classical
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
theorem inv_of_lamp {m : Set (Finset X) → ℝ≥0∞} (hm : IsLampInvariant G m) :
    IsInvariant G m := by
  intro g S
  have := hm ∅ g S
  have e : (fun E : Finset X => symmDiff ∅ (g • E)) '' S = g • S := by
    have h0 : ∀ a : Finset X, symmDiff ∅ a = a := fun a => bot_symmDiff a
    ext E; simp [Set.mem_smul_set, h0]
  rwa [e] at this

theorem flip_image (x : X) (S : Set (Finset X)) :
    (fun E : Finset X => symmDiff {x} E) '' S = {E | symmDiff {x} E ∈ S} := by
  ext E; constructor
  · rintro ⟨E', hE', rfl⟩; simpa [symmDiff_symmDiff_cancel_left] using hE'
  · intro h; exact ⟨_, h, symmDiff_symmDiff_cancel_left _ _⟩

theorem half_of_flip {m : Set (Finset X) → ℝ≥0∞} (hfa : IsFinitelyAdditiveMeasure m)
    (h1 : m Set.univ = 1)
    (hflip : m ((fun E : Finset X => symmDiff {x₀} E) '' {E | x₀ ∈ E}) = m {E | x₀ ∈ E}) :
    m {E | x₀ ∈ E} = 1 / 2 := by
  have e : (fun E : Finset X => symmDiff {x₀} E) '' {E | x₀ ∈ E} = {E | x₀ ∈ E}ᶜ := by
    rw [flip_image]; ext E; simp [Finset.mem_symmDiff]
  rw [e] at hflip
  have h := hfa.2 _ _ (disjoint_compl_right : Disjoint {E : Finset X | x₀ ∈ E} _)
  rw [Set.union_compl_self, h1, hflip] at h
  rw [ENNReal.eq_div_iff two_ne_zero ENNReal.ofNat_ne_top, two_mul, ← h]

theorem ii_imp_iii : CondII G X → CondIII G X x₀ := by
  rintro ⟨m, hfa, h1, hl⟩
  refine ⟨m, ⟨hfa, h1, inv_of_lamp G X hl⟩, half_of_flip X x₀ hfa h1 ?_⟩
  simpa using hl {x₀} 1 {E | x₀ ∈ E}

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
namespace JuschenkoMonod.L31
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
alias ii_imp_iii := JuschenkoMonod.L31.PartA.ii_imp_iii

end JuschenkoMonod.L31
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
open Classical
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
theorem step_union (μ : Set (Finset X) → ℝ≥0∞) (hμ : IsFinitelyAdditiveMeasure μ)
    (hμ1 : μ Set.univ = 1) (hμi : IsInvariant G μ) (hμB : μ {E | x₀ ∈ E} = 2⁻¹)
    (M : Set (Finset X) → ℝ≥0∞) (hM : IsFinitelyAdditiveMeasure M) (hM1 : M Set.univ = 1)
    (hMi : IsInvariant G M) (δ : ℝ≥0∞) (hδ : 1 ≤ M {E | x₀ ∈ E} + δ) :
    ∃ M' : Set (Finset X) → ℝ≥0∞, IsFinitelyAdditiveMeasure M' ∧ M' Set.univ = 1 ∧
      IsInvariant G M' ∧ 1 ≤ M' {E | x₀ ∈ E} + δ * 2⁻¹ := by
  let Φ : Finset X → Set (Finset X) → ℝ≥0∞ := fun E S => M {E' | E ∪ E' ∈ S}
  have hΦ : ∀ E, IsFinitelyAdditiveMeasure (Φ E) := fun E => by
    refine ⟨by simpa [Φ] using hM.1, fun S T hST => ?_⟩
    simp only [Φ]
    have : {E' | E ∪ E' ∈ S ∪ T} = {E' | E ∪ E' ∈ S} ∪ {E' | E ∪ E' ∈ T} := by ext; simp
    rw [this]
    exact hM.2 _ _ (Set.disjoint_left.2 fun x hxS hxT => Set.disjoint_left.1 hST hxS hxT)
  have hΦ1 : ∀ E, Φ E Set.univ = 1 := fun E => by simpa [Φ] using hM1
  have hΦk : ∀ (g : G) (E : Finset X) (S : Set (Finset X)), Φ (g • E) (g • S) = Φ E S := by
    intro g E S
    simp only [Φ]
    have : {E' | g • E ∪ E' ∈ g • S} = g • {E'' | E ∪ E'' ∈ S} := by
      ext E'
      simp only [Set.mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem]
      rw [Finset.smul_finset_union, inv_smul_smul]
    rw [this, hMi]
  obtain ⟨m', hm'fa, hm'1, hm'i, hge, -⟩ :=
    exists_invariant_of_barycenter (H := G) (Y := Finset X) (X := Finset X) hμ hμ1 hμi hΦ hΦ1 hΦk
  refine ⟨m', hm'fa, hm'1, hm'i, ?_⟩
  have hB := hge {E | x₀ ∈ E} {E | x₀ ∈ E} 1 (M {E | x₀ ∈ E})
    (fun E hE => by
      have : {E' | E ∪ E' ∈ {E : Finset X | x₀ ∈ E}} = Set.univ := by
        ext E'; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, Finset.mem_union]
        exact Or.inl hE
      simp only [Φ, this, hM1, le_refl])
    (fun E hE => by
      have : {E' | E ∪ E' ∈ {E : Finset X | x₀ ∈ E}} = {E' | x₀ ∈ E'} := by
        ext E'; simp only [Set.mem_setOf_eq, Finset.mem_union]
        have : x₀ ∉ E := hE
        tauto
      simp only [Φ, this, le_refl])
  have hBc : μ {E | x₀ ∈ E}ᶜ = 2⁻¹ := by
    have h := hμ.2 _ _ (disjoint_compl_right : Disjoint {E : Finset X | x₀ ∈ E} _)
    rw [Set.union_compl_self, hμ1, hμB] at h
    exact (ENNReal.add_right_inj (by simp)).1 (h.symm.trans ENNReal.inv_two_add_inv_two.symm)
  rw [hμB, hBc, one_mul] at hB
  calc (1 : ℝ≥0∞) = 2⁻¹ + 1 * 2⁻¹ := by rw [one_mul, ENNReal.inv_two_add_inv_two]
    _ ≤ 2⁻¹ + (M {E | x₀ ∈ E} + δ) * 2⁻¹ := by gcongr
    _ = (2⁻¹ + M {E | x₀ ∈ E} * 2⁻¹) + δ * 2⁻¹ := by rw [add_mul, add_assoc]
    _ ≤ m' {E | x₀ ∈ E} + δ * 2⁻¹ := by gcongr

theorem iii_imp_iv : CondIII G X x₀ → CondIV G X x₀ := by
  rintro ⟨μ, ⟨h0fa, h01, h0i⟩, h0B'⟩
  have h0B : μ {E | x₀ ∈ E} = 2⁻¹ := by rw [h0B', one_div]
  have hseq : ∀ k : ℕ, ∃ M : Set (Finset X) → ℝ≥0∞, IsFinitelyAdditiveMeasure M ∧
      M Set.univ = 1 ∧ IsInvariant G M ∧ 1 ≤ M {E | x₀ ∈ E} + 2⁻¹ ^ k := by
    intro k
    induction k with
    | zero => exact ⟨μ, h0fa, h01, h0i, by simp⟩
    | succ k ih =>
      obtain ⟨M, hM, hM1, hMi, hMk⟩ := ih
      obtain ⟨M', h1, h2, h3, h4⟩ := step_union G X x₀ μ h0fa h01 h0i h0B M hM hM1 hMi _ hMk
      exact ⟨M', h1, h2, h3, by rwa [← pow_succ] at h4⟩
  choose M hM using hseq
  haveI : (Filter.atTop : Filter ℕ).NeBot := Filter.atTop_neBot
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  have hlim : ∀ S : Set (Finset X), ∃ L : ℝ≥0∞, Filter.Tendsto (fun k => M k S) U (nhds L) := by
    intro S
    obtain ⟨L, -, hL⟩ := isCompact_univ.ultrafilter_le_nhds (U.map (fun k => M k S)) (by simp)
    exact ⟨L, hL⟩
  choose L hL using hlim
  have hLfa : IsFinitelyAdditiveMeasure L := by
    refine ⟨?_, fun S T hST => ?_⟩
    · refine tendsto_nhds_unique (hL ∅) ?_
      have : (fun k => M k ∅) = fun _ => 0 := funext fun k => (hM k).1.1
      rw [this]; exact tendsto_const_nhds
    · refine tendsto_nhds_unique (hL _) ?_
      simp only [fun k => (hM k).1.2 S T hST]
      exact (hL S).add (hL T)
  have hL1 : L Set.univ = 1 :=
    tendsto_nhds_unique (hL _) (by simpa [(hM _).2.1] using tendsto_const_nhds (x := (1 : ℝ≥0∞)))
  have hLi : IsInvariant G L := by
    intro g S
    refine tendsto_nhds_unique (hL _) ?_
    simp only [fun k => (hM k).2.2.1 g S]
    exact hL S
  refine ⟨L, ⟨hLfa, hL1, hLi⟩, ?_⟩
  have hge : 1 ≤ L {E | x₀ ∈ E} := by
    have hz : Filter.Tendsto (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k) U (nhds 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)).mono_left hU
    have := le_of_tendsto_of_tendsto' tendsto_const_nhds ((hL _).add hz) (fun k => (hM k).2.2.2)
    simpa using this
  exact le_antisymm (hL1 ▸ fa_mono hLfa (Set.subset_univ _)) hge

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
namespace JuschenkoMonod.L31
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
alias iii_imp_iv := JuschenkoMonod.L31.PartA.iii_imp_iv

end JuschenkoMonod.L31
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open Garrido
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
namespace JuschenkoMonod.L31.PartA
open Classical
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
/-- The uniform random subset kernel: `Φu E S` is the proportion of subsets of `E` lying in `S`. -/
noncomputable def Φu (E : Finset X) (S : Set (Finset X)) : ℝ≥0∞ :=
  ((E.powerset.filter (· ∈ S)).card : ℝ≥0∞) / 2 ^ E.card

theorem Φu_fa (E : Finset X) : IsFinitelyAdditiveMeasure (Φu X E) := by
  refine ⟨by simp [Φu], fun S T hST => ?_⟩
  simp only [Φu]
  rw [← ENNReal.add_div, ← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · congr 3; ext R; simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]; tauto
  · exact Finset.disjoint_filter.2 fun R _ h1 h2 => Set.disjoint_left.1 hST h1 h2

theorem Φu_univ (E : Finset X) : Φu X E Set.univ = 1 := by
  simp only [Φu, Set.mem_univ, Finset.filter_true, Finset.card_powerset, Nat.cast_pow,
    Nat.cast_ofNat]
  exact ENNReal.div_self (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

theorem Φu_equiv (g : G) (E : Finset X) (S : Set (Finset X)) : Φu X (g • E) (g • S) = Φu X E S := by
  simp only [Φu, Finset.card_smul_finset]
  congr 2
  refine Finset.card_nbij' (fun R => g⁻¹ • R) (fun R => g • R) ?_ ?_ ?_ ?_
  · intro R hR
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hR ⊢
    refine ⟨?_, (Set.mem_smul_set_iff_inv_smul_mem).1 hR.2⟩
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_smul_finset.1 hy
    obtain ⟨w, hw, hwz⟩ := Finset.mem_smul_finset.1 (hR.1 hz)
    rw [← hwz, inv_smul_smul]; exact hw
  · intro R hR
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hR ⊢
    exact ⟨Finset.smul_finset_subset_smul_finset hR.1, Set.smul_mem_smul_set hR.2⟩
  · intro R _; simp
  · intro R _; simp

theorem Φu_flip (x : X) (E : Finset X) (hx : x ∈ E) (S : Set (Finset X)) :
    Φu X E ((fun E => symmDiff {x} E) '' S) = Φu X E S := by
  rw [flip_image]
  simp only [Φu]
  congr 2
  have hsub : ∀ R, R ⊆ E → symmDiff {x} R ⊆ E := fun R hR =>
    (symmDiff_le_sup (a := ({x} : Finset X)) (b := R)).trans
      (Finset.union_subset (Finset.singleton_subset_iff.2 hx) hR)
  refine Finset.card_nbij' (fun R => symmDiff {x} R) (fun R => symmDiff {x} R) ?_ ?_ ?_ ?_
  · intro R hR
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hR ⊢
    exact ⟨hsub R hR.1, hR.2⟩
  · intro R hR
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hR ⊢
    exact ⟨hsub R hR.1, by rw [symmDiff_symmDiff_cancel_left]; exact hR.2⟩
  · intro R _; exact symmDiff_symmDiff_cancel_left _ _
  · intro R _; exact symmDiff_symmDiff_cancel_left _ _

theorem iv_imp_ii [MulAction.IsPretransitive G X] : CondIV G X x₀ → CondII G X := by
  rintro ⟨μ, ⟨hfa, h1, hi⟩, hx₀⟩
  have hall : ∀ x : X, μ {E | x ∈ E}ᶜ = 0 := by
    intro x
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G x₀ x
    have e : {E : Finset X | h • x₀ ∈ E} = h • {E | x₀ ∈ E} := by
      ext E; simp [Set.mem_smul_set_iff_inv_smul_mem, Finset.mem_inv_smul_finset_iff]
    have hx : μ {E : Finset X | h • x₀ ∈ E} = 1 := by rw [e, hi, hx₀]
    have hsum := hfa.2 _ _ (disjoint_compl_right : Disjoint {E : Finset X | h • x₀ ∈ E} _)
    rw [Set.union_compl_self, h1, hx] at hsum
    exact ((ENNReal.add_right_inj ENNReal.one_ne_top).1 (by rw [add_zero]; exact hsum)).symm
  obtain ⟨m, hmfa, hm1, hmi, -, hcongr⟩ :=
    exists_invariant_of_barycenter (H := G) (Y := Finset X) (X := Finset X) hfa h1 hi
      (Φu_fa X) (Φu_univ X) (fun g E S => Φu_equiv G X g E S)
  have hflip : ∀ (x : X) (S : Set (Finset X)), m ((fun E => symmDiff {x} E) '' S) = m S :=
    fun x S => hcongr {E | x ∈ E} _ _ (hall x) (fun E hE => Φu_flip X x E hE S)
  refine ⟨m, hmfa, hm1, ?_⟩
  intro F g S
  induction F using Finset.induction_on with
  | empty =>
    have h0 : ∀ a : Finset X, symmDiff ∅ a = a := fun a => bot_symmDiff a
    have e : (fun E : Finset X => symmDiff ∅ (g • E)) '' S = g • S := by
      ext E; simp [Set.mem_smul_set, h0]
    rw [e, hmi]
  | insert x F hx ih =>
    have e : (fun E => symmDiff (insert x F) (g • E)) '' S =
        (fun E => symmDiff {x} E) '' ((fun E => symmDiff F (g • E)) '' S) := by
      rw [Set.image_image]
      congr 1; funext E
      rw [← symmDiff_assoc, (Finset.disjoint_singleton_left.2 hx).symmDiff_eq_sup,
        Finset.sup_eq_union, Finset.insert_eq]
    rw [e, hflip, ih]

end JuschenkoMonod.L31.PartA
end

section
open MeasureTheory
open scoped ENNReal Pointwise
namespace JuschenkoMonod.L31
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
alias iv_imp_ii := JuschenkoMonod.L31.PartA.iv_imp_ii

end JuschenkoMonod.L31
end

section
namespace JuschenkoMonod.L31.PartB
open MeasureTheory Garrido
open scoped ENNReal Pointwise
open Set
variable {X : Type*} (m : Set X → ℝ≥0∞)
/-! Part B of Juschenko–Monod Lemma 3.1: (ii) ⇒ (i). -/
/-- Finite additivity over the fibres of a map. -/
theorem mean_fam_fiber (hm : IsFinitelyAdditiveMeasure m) {α : Type*} [DecidableEq α]
    (π : X → α) (T : Finset α) :
    m (π ⁻¹' (T : Set α)) = ∑ a ∈ T, m (π ⁻¹' {a}) := by
  induction T using Finset.induction_on with
  | empty => simp [hm.1]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.coe_insert, Set.insert_eq, Set.preimage_union]
    apply hm.2
    exact Disjoint.preimage π (Set.disjoint_singleton_left.2 (by simpa using ha))

theorem mean_mono (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel h).symm
  rw [this, hm.2 _ _ Set.disjoint_sdiff_right]
  exact le_self_add

theorem mean_ne_top (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : Set X) :
    m s ≠ ∞ :=
  ne_top_of_le_ne_top (by rw [h1]; exact ENNReal.one_ne_top) (mean_mono m hm (subset_univ s))

/-- The integral of a finitely valued function. -/
noncomputable def meanI (s : X → ℝ) : ℝ := ∑ᶠ v : ℝ, v * (m (s ⁻¹' {v})).toReal

end JuschenkoMonod.L31.PartB
end

section
namespace JuschenkoMonod.L31.PartB
open MeasureTheory Garrido
open scoped ENNReal Pointwise
open Set
variable {X : Type*} (m : Set X → ℝ≥0∞)
variable {m}
theorem meanI_factor (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    {α : Type*} [DecidableEq α] (π : X → α) (T : Finset α) (hT : ∀ x, π x ∈ T) (ψ : α → ℝ) :
    meanI m (ψ ∘ π) = ∑ a ∈ T, ψ a * (m (π ⁻¹' {a})).toReal := by
  classical
  rw [meanI, finsum_eq_sum_of_support_subset _ (s := T.image ψ) ?_]
  · have e : ∀ v, (ψ ∘ π) ⁻¹' {v} = π ⁻¹' ((T.filter (fun a => ψ a = v) : Finset α) : Set α) := by
      intro v; ext x; simp [hT x]
    simp_rw [e, mean_fam_fiber m hm, ENNReal.toReal_sum (fun a _ => mean_ne_top m hm h1 _),
      Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := ψ) (t := T.image ψ)
      (fun a ha => Finset.mem_image_of_mem ψ ha)]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  · intro v hv
    rw [Function.mem_support] at hv
    by_contra h
    apply hv
    have : (ψ ∘ π) ⁻¹' {v} = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      intro hx
      exact h (by simpa using ⟨π x, hT x, hx⟩)
    simp [this, hm.1]

theorem meanI_eq_sum (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    (s : X → ℝ) (T : Finset ℝ) (hT : ∀ x, s x ∈ T) :
    meanI m s = ∑ v ∈ T, v * (m (s ⁻¹' {v})).toReal :=
  meanI_factor hm h1 s T hT id

theorem mean_range_pair {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => (s x, t x)).Finite :=
  (hs.prod ht).subset (by rintro _ ⟨x, rfl⟩; exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩)

theorem mean_range_map {s : X → ℝ} (hs : (range s).Finite) (φ : ℝ → ℝ) :
    (range fun x => φ (s x)).Finite :=
  (hs.image φ).subset (by rintro _ ⟨x, rfl⟩; exact ⟨s x, ⟨x, rfl⟩, rfl⟩)

theorem mean_range_add {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => s x + t x).Finite :=
  ((mean_range_pair hs ht).image (fun p => p.1 + p.2)).subset
    (by rintro _ ⟨x, rfl⟩; exact ⟨(s x, t x), ⟨x, rfl⟩, rfl⟩)

theorem mean_range_const (c : ℝ) : (range fun _ : X => c).Finite :=
  (Set.finite_singleton c).subset Set.range_const_subset

theorem meanI_add (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) :
    meanI m (fun x => s x + t x) = meanI m s + meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hT : ∀ x, π x ∈ hs.toFinset ×ˢ ht.toFinset := fun x => by simp [π]
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  have e3 := meanI_factor hm h1 π _ hT (fun p => p.1 + p.2)
  simp only [Function.comp_def, π] at e1 e2 e3
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => add_mul _ _ _

theorem meanI_map (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s : X → ℝ}
    (hs : (range s).Finite) (c : ℝ) : meanI m (fun x => c * s x) = c * meanI m s := by
  classical
  have hT : ∀ x, s x ∈ hs.toFinset := fun x => by simp
  have e1 := meanI_factor hm h1 s _ hT (fun v => c * v)
  have e2 := meanI_eq_sum hm h1 s _ hT
  simp only [Function.comp_def] at e1
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

theorem meanI_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (c : ℝ) :
    meanI m (fun _ : X => c) = c := by
  have e := meanI_factor hm h1 (fun _ : X => ()) Finset.univ (fun _ => Finset.mem_univ _)
    (fun _ => c)
  simp only [Function.comp_def] at e
  rw [e]
  simp [h1]

theorem meanI_mono (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) (hst : ∀ x, s x ≤ t x) :
    meanI m s ≤ meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hπ := mean_range_pair hs ht
  have hT : ∀ x, π x ∈ hπ.toFinset := fun x => (Set.Finite.mem_toFinset hπ).2 ⟨x, rfl⟩
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  simp only [Function.comp_def, π] at e1 e2
  rw [e1, e2]
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨x, rfl⟩ := (Set.Finite.mem_toFinset hπ).1 ha
  exact mul_le_mul_of_nonneg_right (hst x) ENNReal.toReal_nonneg

/-! ### The upper integral on `ℓ∞` -/
local notation "E" X => lp (fun _ : X => ℝ) ∞

variable (m) in
/-- Upper Darboux integral of a bounded function. -/
noncomputable def meanP (f : E X) : ℝ :=
  sInf {r | ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧ meanI m s = r}

theorem mean_abs_le (f : E X) (x : X) : |(f : X → ℝ) x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  simpa [Real.norm_eq_abs] using this

theorem meanP_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {f : E X} {s : X → ℝ}
    (hs : (range s).Finite) (hfs : ∀ x, (f : X → ℝ) x ≤ s x) : meanP m f ≤ meanI m s := by
  refine csInf_le ⟨-‖f‖, ?_⟩ ⟨s, hs, hfs, rfl⟩
  rintro _ ⟨t, ht, hft, rfl⟩
  rw [← meanI_const hm h1 (-‖f‖)]
  exact meanI_mono hm h1 (mean_range_const _) ht
    (fun x => le_trans (neg_le_of_abs_le (mean_abs_le f x)) (hft x))

theorem le_meanP {f : E X} {r : ℝ}
    (h : ∀ s : X → ℝ, (range s).Finite → (∀ x, (f : X → ℝ) x ≤ s x) → r ≤ meanI m s) :
    r ≤ meanP m f := by
  refine le_csInf ⟨_, fun _ => ‖f‖, mean_range_const _,
    fun x => le_trans (le_abs_self _) (mean_abs_le f x), rfl⟩ ?_
  rintro _ ⟨s, hs, hfs, rfl⟩
  exact h s hs hfs

/-- Approximation from above by a finitely valued function, within `ε`. -/
theorem mean_approx (f : E X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧
      ∀ x, s x ≤ (f : X → ℝ) x + ε := by
  refine ⟨fun x => ε * ⌈(f : X → ℝ) x / ε⌉, ?_, fun x => ?_, fun x => ?_⟩
  · refine ((Set.finite_Icc ⌈-‖f‖ / ε⌉ ⌈‖f‖ / ε⌉).image (fun k : ℤ => ε * k)).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨_, ⟨Int.ceil_mono ?_, Int.ceil_mono ?_⟩, rfl⟩
    · exact div_le_div_of_nonneg_right (neg_le_of_abs_le (mean_abs_le f x)) hε.le
    · exact div_le_div_of_nonneg_right (le_trans (le_abs_self _) (mean_abs_le f x)) hε.le
  · have := Int.le_ceil ((f : X → ℝ) x / ε)
    calc (f : X → ℝ) x = ε * ((f : X → ℝ) x / ε) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hε.le
  · have := Int.ceil_lt_add_one ((f : X → ℝ) x / ε)
    calc ε * (⌈(f : X → ℝ) x / ε⌉ : ℝ) ≤ ε * ((f : X → ℝ) x / ε + 1) :=
          mul_le_mul_of_nonneg_left this.le hε.le
      _ = (f : X → ℝ) x + ε := by field_simp

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem meanP_ofFin (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : X → ℝ)
    (hs : (range s).Finite) : meanP m (meanOfFin s hs) = meanI m s :=
  le_antisymm (meanP_le hm h1 hs fun _ => le_rfl)
    (le_meanP fun t ht hst => meanI_mono (t := t) hm h1 hs ht hst)

theorem meanP_smul_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) ≤ c * meanP m f := by
  have : meanP m (c • f) / c ≤ meanP m f := by
    refine le_meanP fun s hs hfs => ?_
    rw [div_le_iff₀ hc]
    calc meanP m (c • f) ≤ meanI m (fun x => c * s x) :=
          meanP_le hm h1 (mean_range_map hs _) (fun x => by
            simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
            exact mul_le_mul_of_nonneg_left (hfs x) hc.le)
      _ = meanI m s * c := by rw [meanI_map hm h1 hs, mul_comm]
  rwa [div_le_iff₀ hc, mul_comm] at this

theorem meanP_smul (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) = c * meanP m f := by
  refine le_antisymm (meanP_smul_le hm h1 hc f) ?_
  have := meanP_smul_le hm h1 (inv_pos.2 hc) (c • f)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  calc c * meanP m f ≤ c * (c⁻¹ * meanP m (c • f)) := mul_le_mul_of_nonneg_left this hc.le
    _ = _ := by field_simp

theorem meanP_add_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f g : E X) :
    meanP m (f + g) ≤ meanP m f + meanP m g := by
  have h2 : meanP m (f + g) - meanP m f ≤ meanP m g := by
    refine le_meanP fun t ht hgt => ?_
    have : meanP m (f + g) - meanI m t ≤ meanP m f := by
      refine le_meanP fun s hs hfs => ?_
      have := meanP_le hm h1 (f := f + g) (mean_range_add hs ht)
        (fun x => by simp only [lp.coeFn_add, Pi.add_apply]; exact add_le_add (hfs x) (hgt x))
      rw [meanI_add hm h1 hs ht] at this
      linarith
    linarith
  linarith

theorem meanP_zero (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    meanP m (0 : E X) = 0 := by
  refine le_antisymm ?_ ?_
  · calc meanP m (0 : E X) ≤ meanI m (fun _ => 0) :=
          meanP_le hm h1 (mean_range_const _) (fun x => by simp)
      _ = 0 := meanI_const hm h1 0
  · refine le_meanP fun s hs hfs => ?_
    rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
    exact meanI_mono hm h1 (mean_range_const _) hs (fun x => by simpa using hfs x)

/-- The upper integral is linear (Hahn–Banach plus uniform approximation). -/
theorem mean_exists_linear (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    ∃ L : (E X) →ₗ[ℝ] ℝ, ∀ f, L f = meanP m f := by
  obtain ⟨L, -, hL⟩ := exists_extension_of_le_sublinear
    ({ domain := ⊥, toFun := 0 } : (E X) →ₗ.[ℝ] ℝ) (meanP m)
    (fun c hc f => meanP_smul hm h1 hc f) (meanP_add_le hm h1)
    (fun x => by
      have hx : (x : E X) = 0 := (Submodule.mem_bot ℝ).1 x.2
      simp [hx, meanP_zero hm h1])
  refine ⟨L, fun f => le_antisymm (hL f) ?_⟩
  -- `L` agrees with `meanI` on finitely valued functions.
  have hLs : ∀ s hs, L (meanOfFin s hs) = meanI m s := by
    intro s hs
    refine le_antisymm ((hL _).trans (meanP_ofFin hm h1 s hs).le) ?_
    have hns := mean_range_map hs (fun v => -1 * v)
    have e : -(meanOfFin s hs) = meanOfFin (fun x => -1 * s x) hns := by
      ext x; simp
    have := hL (-(meanOfFin s hs))
    rw [map_neg, e, meanP_ofFin hm h1 _ hns, meanI_map hm h1 hs] at this
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s, hs, hfs, hsf⟩ := mean_approx f hε
  have hs' := mean_range_map hs (fun v => v + -ε)
  have h3 : meanI m (fun x => s x + -ε) = meanI m s - ε := by
    rw [meanI_add hm h1 hs (mean_range_const _), meanI_const hm h1]; ring
  have h4 : L (meanOfFin _ hs') ≤ L f := by
    have := hL (meanOfFin _ hs' - f)
    have h0 : meanP m (meanOfFin _ hs' - f) ≤ 0 := by
      calc meanP m (meanOfFin _ hs' - f) ≤ meanI m (fun _ => 0) :=
            meanP_le hm h1 (mean_range_const _) (fun x => by
              simp only [lp.coeFn_sub, Pi.sub_apply, meanOfFin_apply]; linarith [hsf x])
        _ = 0 := meanI_const hm h1 0
    rw [map_sub] at this
    linarith
  rw [hLs] at h4
  calc meanP m f ≤ meanI m s := meanP_le hm h1 hs hfs
    _ ≤ L f + ε := by linarith

theorem meanP_nonneg (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (hf : ∀ x, 0 ≤ (f : X → ℝ) x) : 0 ≤ meanP m f := by
  refine le_meanP fun s hs hfs => ?_
  rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
  exact meanI_mono hm h1 (mean_range_const _) hs (fun x => (hf x).trans (hfs x))

theorem meanP_comp_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (e : Equiv.Perm X)
    (he : ∀ A, m (e ⁻¹' A) = m A) (f f' : E X)
    (hf : ∀ x, (f' : X → ℝ) x = (f : X → ℝ) (e x)) : meanP m f' ≤ meanP m f := by
  refine le_meanP fun s hs hfs => ?_
  have hs' : (range (fun x => s (e x))).Finite :=
    hs.subset (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩)
  have hI : meanI m (fun x => s (e x)) = meanI m s := by
    unfold meanI
    congr 1
    funext v
    have : (fun x => s (e x)) ⁻¹' {v} = e ⁻¹' (s ⁻¹' {v}) := rfl
    rw [this, he]
  rw [← hI]
  exact meanP_le hm h1 hs' (fun x => by rw [hf]; exact hfs _)

theorem meanP_comp (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (e : Equiv.Perm X)
    (he : ∀ A, m (e ⁻¹' A) = m A) (f f' : E X)
    (hf : ∀ x, (f' : X → ℝ) x = (f : X → ℝ) (e x)) : meanP m f' = meanP m f := by
  refine le_antisymm (meanP_comp_le hm h1 e he f f' hf) ?_
  refine meanP_comp_le hm h1 e.symm (fun A => ?_) f' f (fun x => by rw [hf]; simp)
  rw [← he (e.symm ⁻¹' A)]
  congr 1
  ext x
  simp

/-- A bounded function as an element of `ℓ∞`. -/
noncomputable def ofBdd (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) : E X :=
  ⟨f, memℓp_infty_iff.2 ⟨C, by
    rintro _ ⟨x, rfl⟩
    simpa [Real.norm_eq_abs] using hf x⟩⟩

@[simp] theorem ofBdd_apply (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) (x : X) :
    (ofBdd f C hf : X → ℝ) x = f x := rfl

end JuschenkoMonod.L31.PartB
end

section
namespace JuschenkoMonod.L31.PartB
open MeasureTheory Garrido
open scoped ENNReal Pointwise
open Set
/-- **Reiter's condition** from an invariant finitely additive probability measure, for finitely
many measure-preserving permutations (Hahn–Banach in `(ι → ℓ¹(Y))`). -/
theorem reiter {Y ι : Type*} [Fintype ι] [DecidableEq ι] (m : Set Y → ℝ≥0∞)
    (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (σ : ι → Equiv.Perm Y)
    (hσ : ∀ i A, m (σ i ⁻¹' A) = m A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ μ : Y → ℝ, ∃ S : Finset Y, (∀ y, 0 ≤ μ y) ∧ (∀ y ∉ S, μ y = 0) ∧ ∑ y ∈ S, μ y = 1 ∧
      ∀ i, ∀ V : Finset Y, ∑ y ∈ V, |μ ((σ i).symm y) - μ y| ≤ δ := by
  classical
  by_contra hne
  let K : Set (ι → lp (fun _ : Y => ℝ) 1) := {v | ∃ μ : Y → ℝ, ∃ S : Finset Y,
      (∀ y, 0 ≤ μ y) ∧ (∀ y ∉ S, μ y = 0) ∧ ∑ y ∈ S, μ y = 1 ∧
      ∀ i y, (v i : Y → ℝ) y = μ ((σ i).symm y) - μ y}
  have hK : Convex ℝ K := by
    rintro v ⟨μ, S, h0, hS, h1', hv⟩ w ⟨ν, T, h0', hT, h1'', hw⟩ a b ha hb hab
    refine ⟨fun y => a * μ y + b * ν y, S ∪ T, fun y => ?_, ?_, ?_, ?_⟩
    · have := h0 y; have := h0' y; positivity
    · intro y hy
      simp only [Finset.mem_union, not_or] at hy
      simp [hS y hy.1, hT y hy.2]
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.sum_subset Finset.subset_union_left (fun y _ hy => hS y hy),
        ← Finset.sum_subset Finset.subset_union_right (fun y _ hy => hT y hy), h1', h1'',
        mul_one, mul_one, hab]
    · intro i y
      simp only [Pi.add_apply, Pi.smul_apply, lp.coeFn_add, lp.coeFn_smul, smul_eq_mul, hv, hw]
      ring
  have hdisj : Disjoint (Metric.ball (0 : ι → lp (fun _ : Y => ℝ) 1) δ) K := by
    rw [Set.disjoint_left]
    rintro v hv ⟨μ, S, h0, hS, h1', hvμ⟩
    apply hne
    refine ⟨μ, S, h0, hS, h1', fun i V => ?_⟩
    have hb : ‖v i‖ < δ := lt_of_le_of_lt (norm_le_pi_norm v i) (by simpa using hv)
    have := lp.sum_rpow_le_norm_rpow (p := 1) (by norm_num) (v i) V
    simp only [ENNReal.toReal_one, Real.rpow_one] at this
    calc ∑ y ∈ V, |μ ((σ i).symm y) - μ y| = ∑ y ∈ V, ‖(v i : Y → ℝ) y‖ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Real.norm_eq_abs, hvμ]
      _ ≤ δ := this.trans hb.le
  obtain ⟨φ, u, hφ1, hφ2⟩ :=
    geometric_hahn_banach_open (convex_ball 0 δ) Metric.isOpen_ball hK hdisj
  have hu : 0 < u := by simpa using hφ1 0 (Metric.mem_ball_self hδ)
  let h : ι → Y → ℝ := fun i y => φ (Pi.single i (lp.single 1 y (1 : ℝ)))
  have hbd : ∀ i y, |h i y| ≤ ‖φ‖ := by
    intro i y
    have := φ.le_opNorm (Pi.single i (lp.single 1 y (1 : ℝ)))
    rw [Pi.norm_single, lp.norm_single (by norm_num)] at this
    simpa [Real.norm_eq_abs] using this
  have key : ∀ y, u ≤ ∑ i, (h i (σ i y) - h i y) := by
    intro y
    let v : ι → lp (fun _ : Y => ℝ) 1 := fun i => lp.single 1 (σ i y) 1 - lp.single 1 y 1
    have hvK : v ∈ K := by
      refine ⟨fun z => if z = y then 1 else 0, {y}, fun z => by dsimp only; split_ifs <;> norm_num,
        fun z hz => by simp at hz; simp [hz], by simp, fun i z => ?_⟩
      simp only [v, lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_apply]
      congr 1
      by_cases hz : z = σ i y
      · subst hz; simp
      · have : (σ i).symm z ≠ y := fun h' => hz (by rw [← h']; simp)
        simp [hz, this]
    have := hφ2 v hvK
    rw [← Finset.univ_sum_single v, map_sum] at this
    simpa [v, h, Pi.single_sub, map_sub] using this
  obtain ⟨L, hL⟩ := mean_exists_linear hm h1
  let H : ι → lp (fun _ : Y => ℝ) ∞ := fun i => ofBdd (h i) _ (hbd i)
  let Hσ : ι → lp (fun _ : Y => ℝ) ∞ := fun i => ofBdd (fun y => h i (σ i y)) _ (fun y => hbd i _)
  have hinv : ∀ i, L (Hσ i) = L (H i) := fun i => by
    rw [hL, hL]
    exact meanP_comp hm h1 (σ i) (hσ i) _ _ (fun y => rfl)
  have hsum : L (∑ i, (Hσ i - H i)) = 0 := by simp [map_sum, map_sub, hinv]
  let c : lp (fun _ : Y => ℝ) ∞ := meanOfFin (fun _ => u) (mean_range_const u)
  have hc : L c = u := by rw [hL, meanP_ofFin hm h1, meanI_const hm h1]
  have hge : 0 ≤ L (∑ i, (Hσ i - H i) - c) := by
    rw [hL]
    refine meanP_nonneg hm h1 _ fun y => ?_
    simp only [lp.coeFn_sub, lp.coeFn_sum, Pi.sub_apply, Finset.sum_apply, H, Hσ, c, ofBdd_apply,
      meanOfFin_apply]
    linarith [key y]
  rw [map_sub, hsum, hc] at hge
  linarith

end JuschenkoMonod.L31.PartB
end

section
namespace JuschenkoMonod.L31.PartB
open MeasureTheory Garrido
open scoped ENNReal Pointwise
open Set
variable {X : Type*} [DecidableEq X]
/-- The sign `(-1)^a` of a coordinate value. -/
def sgn (a : Fin 2) : ℝ := if a = 0 then 1 else -1

theorem sgn_mul_self (a : Fin 2) : sgn a * sgn a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem abs_sgn (a : Fin 2) : |sgn a| = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem sgn_rev (a : Fin 2) : sgn (Fin.rev a) = -sgn a := by
  fin_cases a <;> simp [sgn]

/-- The Walsh character `w_E(ω) = ∏_{x ∈ E} (-1)^{ω x}`. -/
def walsh (E : Finset X) (ω : X → Fin 2) : ℝ := ∏ x ∈ E, sgn (ω x)

theorem walsh_mul (E F : Finset X) (ω : X → Fin 2) :
    walsh E ω * walsh F ω = walsh (symmDiff E F) ω := by
  unfold walsh
  have hd : Disjoint (symmDiff E F) (E ∩ F) := by simpa using disjoint_symmDiff_inf E F
  have hu : symmDiff E F ∪ E ∩ F = E ∪ F := by simpa using symmDiff_sup_inf E F
  rw [← Finset.prod_union_inter, ← hu, Finset.prod_union hd, mul_assoc,
    ← Finset.prod_mul_distrib]
  simp [sgn_mul_self]

theorem abs_walsh (E : Finset X) (ω : X → Fin 2) : |walsh E ω| = 1 := by
  unfold walsh
  rw [Finset.abs_prod]
  simp [abs_sgn]

theorem measurable_sgn : Measurable sgn := measurable_of_finite _

theorem measurable_walsh (E : Finset X) : Measurable (walsh E) :=
  Finset.measurable_prod E fun x _ => measurable_sgn.comp (measurable_pi_apply x)

instance instProbBernoulli : IsProbabilityMeasure (bernoulli X) := by
  unfold bernoulli; infer_instance

theorem memLp_walsh (E : Finset X) (p : ℝ≥0∞) : MemLp (walsh E) p (bernoulli X) :=
  (memLp_top_of_bound (measurable_walsh E).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_walsh])).mono_exponent le_top

theorem integrable_walsh (E : Finset X) : Integrable (walsh E) (bernoulli X) :=
  Integrable.of_bound (measurable_walsh E).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_walsh])

theorem map_rev_uniform :
    ((PMF.uniformOfFintype (Fin 2)).toMeasure).map Fin.rev =
      (PMF.uniformOfFintype (Fin 2)).toMeasure := by
  rw [Measure.ext_iff_singleton]
  intro a
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton a)]
  have : (Fin.rev : Fin 2 → Fin 2) ⁻¹' {a} = {Fin.rev a} := by
    ext b; simp [Fin.rev_eq_iff]
  rw [this, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply]

/-- Flipping coordinate `x` preserves the Bernoulli measure. -/
theorem map_flip (x : X) :
    (bernoulli X).map (fun ω i => (if i = x then Fin.rev else id) (ω i)) = bernoulli X := by
  unfold bernoulli
  have h := Measure.infinitePi_map_pi (μ := fun _ : X => (PMF.uniformOfFintype (Fin 2)).toMeasure)
    (f := fun i => (if i = x then Fin.rev else id : Fin 2 → Fin 2)) (fun i => measurable_of_finite _)
  rw [h]
  congr 1
  funext i
  by_cases h : i = x
  · simp only [h, if_true]; exact map_rev_uniform
  · simp only [h, if_false, Measure.map_id]

theorem integral_walsh (E : Finset X) :
    ∫ ω, walsh E ω ∂bernoulli X = if E = ∅ then 1 else 0 := by
  split_ifs with hE
  · subst hE; simp [walsh]
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hE
    let Φ : (X → Fin 2) → (X → Fin 2) := fun ω i => (if i = x then Fin.rev else id) (ω i)
    have hΦ : Measurable Φ :=
      measurable_pi_lambda _ fun i => (measurable_of_finite _).comp (measurable_pi_apply i)
    have hneg : ∀ ω, walsh E (Φ ω) = -walsh E ω := by
      intro ω
      unfold walsh
      rw [← Finset.mul_prod_erase E _ hx, ← Finset.mul_prod_erase E _ hx]
      have : ∏ i ∈ E.erase x, sgn (Φ ω i) = ∏ i ∈ E.erase x, sgn (ω i) :=
        Finset.prod_congr rfl fun i hi => by
          simp [Φ, (Finset.mem_erase.1 hi).1]
      rw [this]
      simp [Φ, sgn_rev]
    have key : ∫ ω, walsh E ω ∂bernoulli X = ∫ ω, walsh E (Φ ω) ∂bernoulli X := by
      conv_lhs => rw [← map_flip x]
      exact integral_map hΦ.aemeasurable (measurable_walsh E).aestronglyMeasurable
    simp only [hneg, integral_neg] at key
    linarith

theorem integral_walsh_mul (E F : Finset X) :
    ∫ ω, walsh E ω * walsh F ω ∂bernoulli X = if E = F then 1 else 0 := by
  simp only [walsh_mul, integral_walsh]
  congr 1
  apply propext
  rw [← Finset.bot_eq_empty, symmDiff_eq_bot]

/-- A finite Walsh sum. -/
def W (a : Finset X → ℝ) (U : Finset (Finset X)) (ω : X → Fin 2) : ℝ :=
  ∑ E ∈ U, a E * walsh E ω

theorem memLp_W (a : Finset X → ℝ) (U : Finset (Finset X)) : MemLp (W a U) 2 (bernoulli X) :=
  memLp_finsetSum U fun E _ => (memLp_walsh E 2).const_mul (a E)

theorem integral_W_sq (a : Finset X → ℝ) (U : Finset (Finset X)) :
    ∫ ω, W a U ω ^ 2 ∂bernoulli X = ∑ E ∈ U, a E ^ 2 := by
  have e : ∀ ω, W a U ω ^ 2 = ∑ E ∈ U, ∑ F ∈ U, a E * a F * (walsh E ω * walsh F ω) := by
    intro ω
    rw [W, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F _ => ?_
    ring
  simp_rw [e]
  have hi : ∀ E F : Finset X, Integrable (fun ω => a E * a F * (walsh E ω * walsh F ω))
      (bernoulli X) := fun E F =>
    ((integrable_walsh E).mul_of_top_left (memLp_walsh F ⊤)).const_mul _
  refine (integral_finsetSum U fun E _ => integrable_finsetSum U fun F _ => hi E F).trans ?_
  refine Finset.sum_congr rfl fun E hE => ?_
  refine (integral_finsetSum U fun F _ => hi E F).trans ?_
  simp_rw [integral_const_mul, integral_walsh_mul]
  simp [hE, sq]

theorem l2Norm_eq_sqrt (f : (X → Fin 2) → ℝ) (hf : MemLp f 2 (bernoulli X)) :
    l2Norm f = Real.sqrt (∫ ω, f ω ^ 2 ∂bernoulli X) := by
  unfold l2Norm
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs, one_div]

theorem l2Norm_W (a : Finset X → ℝ) (U : Finset (Finset X)) :
    l2Norm (W a U) = Real.sqrt (∑ E ∈ U, a E ^ 2) := by
  rw [l2Norm_eq_sqrt _ (memLp_W a U), integral_W_sq]

theorem l2Norm_ofReal (f : (X → Fin 2) → ℝ) :
    l2Norm (fun ω => (f ω : ℂ)) = l2Norm f := by
  unfold l2Norm
  rw [eLpNorm_congr_norm_ae (ae_of_all _ fun ω => Complex.norm_real (f ω))]

theorem W_perm (a : Finset X → ℝ) (U : Finset (Finset X)) (σ : Equiv.Perm (Finset X))
    (ω : X → Fin 2) :
    ∑ E ∈ U, a E * walsh (σ E) ω = W (fun F => a (σ.symm F)) (U.map σ.toEmbedding) ω := by
  simp [W, Finset.sum_map]

theorem W_extend (a : Finset X → ℝ) {U V : Finset (Finset X)} (ha : ∀ E ∉ U, a E = 0)
    (hUV : U ⊆ V) : W a V = W a U := by
  funext ω
  unfold W
  exact (Finset.sum_subset hUV fun E _ hE => by simp [ha E hE]).symm

theorem W_lin (a b : Finset X → ℝ) (U : Finset (Finset X)) (r s : ℝ) (ω : X → Fin 2) :
    W a U ω * r + W b U ω * s = W (fun E => a E * r + b E * s) U ω := by
  simp only [W, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun E _ => ?_
  ring

end JuschenkoMonod.L31.PartB
end

section
namespace JuschenkoMonod.L31.PartB
open MeasureTheory Garrido
open scoped ENNReal Pointwise
open Set
variable {X : Type*} [DecidableEq X]
variable {G : Type*} [Group G] [MulAction G X]
theorem walsh_translate (g : G) (E : Finset X) (ω : X → Fin 2) :
    walsh E (fun x => ω (g • x)) = walsh (g • E) ω := by
  unfold walsh
  rw [Finset.smul_finset_def, Finset.prod_image fun x _ y _ h => MulAction.injective g h]

theorem translate_W (g : G) (a : Finset X → ℝ) (U : Finset (Finset X)) :
    translate g (W a U) = fun ω => ∑ E ∈ U, a E * walsh (MulAction.toPerm g E) ω := by
  funext ω
  simp [translate, W, walsh_translate]

end JuschenkoMonod.L31.PartB
end

section
namespace JuschenkoMonod.L31.PartB
open MeasureTheory Garrido
open scoped ENNReal Pointwise
open Set
theorem perm_preimage_of_image {Y : Type*} (m : Set Y → ℝ≥0∞) (e : Equiv.Perm Y)
    (he : ∀ A, m (e '' A) = m A) (A : Set Y) : m (e ⁻¹' A) = m A := by
  rw [← he (e ⁻¹' A), Set.image_preimage_eq A e.surjective]

theorem sqrt_sub_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sqrt_nonneg a
  have h4 := Real.sqrt_nonneg b
  have e : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    linear_combination -h1 + h2
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a + Real.sqrt b), ← sq_abs, sq]
  exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)

theorem l2Norm_le_add {X : Type*} {f h : (X → Fin 2) → ℂ} (hf : MemLp f 2 (bernoulli X))
    (hh : MemLp h 2 (bernoulli X)) : l2Norm f ≤ l2Norm h + l2Norm (f - h) := by
  unfold l2Norm
  have hle := eLpNorm_add_le (p := 2) (μ := bernoulli X) hh.aestronglyMeasurable
    (hf.sub hh).aestronglyMeasurable (by norm_num)
  have e : h + (f - h) = f := by ext ω; simp
  rw [e] at hle
  rw [← ENNReal.toReal_add hh.eLpNorm_ne_top (hf.sub hh).eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hh.eLpNorm_ne_top, (hf.sub hh).eLpNorm_ne_top⟩)
    hle

/-- The Reiter bound turned into an `ℓ²` bound for the square roots. -/
theorem sum_sq_le_of_reiter {Y : Type*} (μ : Y → ℝ) (h0 : ∀ y, 0 ≤ μ y) (e : Equiv.Perm Y)
    (V : Finset Y) {c : ℝ} (hc : ∑ y ∈ V, |μ (e.symm y) - μ y| ≤ c) :
    ∑ y ∈ V, (Real.sqrt (μ (e.symm y)) - Real.sqrt (μ y)) ^ 2 ≤ c :=
  (Finset.sum_le_sum fun y _ => sqrt_sub_sq_le (h0 (e.symm y)) (h0 y)).trans hc

theorem W_perm_extend {X : Type*} [DecidableEq X] (a : Finset X → ℝ) (U : Finset (Finset X))
    (ha : ∀ E ∉ U, a E = 0) (e : Equiv.Perm (Finset X)) (ω : X → Fin 2) :
    ∑ E ∈ U, a E * walsh (e E) ω = W (fun F => a (e.symm F)) (U ∪ U.map e.toEmbedding) ω := by
  rw [W_perm, W_extend _ ?_ Finset.subset_union_right]
  intro F hF
  apply ha
  intro hm
  apply hF
  exact Finset.mem_map.2 ⟨_, hm, by simp⟩

open JuschenkoMonod.L31 in
/-- **Part B: (ii) ⇒ (i).** -/
theorem ii_imp_i (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X) :
    CondII G X → CondI G X x₀ := by
  rintro ⟨m, hm, h1, hinv⟩ S ε hε
  classical
  let τ : Equiv.Perm (Finset X) :=
    Function.Involutive.toPerm (symmDiff {x₀}) (fun E => symmDiff_symmDiff_cancel_left _ _)
  let σ : Option S → Equiv.Perm (Finset X) := fun i =>
    i.elim τ (fun g => MulAction.toPerm (g : G))
  have hσ : ∀ i A, m (σ i ⁻¹' A) = m A := by
    intro i A
    apply perm_preimage_of_image
    intro B
    cases i with
    | none =>
      have := hinv {x₀} 1 B
      simp only [one_smul] at this
      exact this
    | some g =>
      have := hinv ∅ (g : G) B
      have e : (fun E : Finset X => symmDiff ∅ ((g : G) • E)) = fun E => (g : G) • E := by
        funext E
        rw [← Finset.bot_eq_empty, bot_symmDiff]
      rw [e] at this
      simpa [σ] using this
  obtain ⟨μ, Sup, h0, hS, hsum, hR⟩ := reiter m hm h1 σ hσ (pow_pos hε 2)
  let a : Finset X → ℝ := fun E => Real.sqrt (μ E)
  have ha : ∀ E ∉ Sup, a E = 0 := by intro E hE; simp [a, hS E hE]
  let r := W a Sup
  have hmem : MemLp (fun ω => (r ω : ℂ)) 2 (bernoulli X) := (memLp_W a Sup).ofReal
  have hnorm : l2Norm (fun ω => (r ω : ℂ)) = 1 := by
    rw [l2Norm_ofReal, l2Norm_W, Finset.sum_congr rfl (fun E _ => Real.sq_sqrt (h0 E)), hsum,
      Real.sqrt_one]
  refine ⟨fun ω => (r ω : ℂ), hmem, by rw [hnorm]; norm_num, ?_, ?_⟩
  · intro g hg
    let e : Equiv.Perm (Finset X) := MulAction.toPerm g
    let V := Sup ∪ Sup.map e.toEmbedding
    have hfun : translate g (fun ω => (r ω : ℂ)) - (fun ω => (r ω : ℂ)) =
        fun ω => ((W (fun F => a (e.symm F) * 1 + a F * (-1)) V ω : ℝ) : ℂ) := by
      funext ω
      have h1' : translate g r ω = W (fun F => a (e.symm F)) V ω := by
        rw [translate_W]
        exact W_perm_extend a Sup ha e ω
      show ((translate g r ω : ℝ) : ℂ) - (r ω : ℂ) = _
      rw [← W_lin, h1', show r = W a V from (W_extend a ha Finset.subset_union_left).symm]
      push_cast
      ring
    rw [hfun, l2Norm_ofReal, l2Norm_W, hnorm, mul_one]
    calc Real.sqrt (∑ F ∈ V, (a (e.symm F) * 1 + a F * (-1)) ^ 2)
        ≤ Real.sqrt (ε ^ 2) := by
          apply Real.sqrt_le_sqrt
          have := sum_sq_le_of_reiter μ h0 e V (hR (some ⟨g, hg⟩) V)
          simpa [a, ← sub_eq_add_neg] using this
      _ = ε := Real.sqrt_sq hε.le
  · let V := Sup ∪ Sup.map τ.toEmbedding
    have hw : ∀ ω, walsh {x₀} ω * r ω = W (fun F => a (τ.symm F)) V ω := by
      intro ω
      rw [← W_perm_extend a Sup ha τ ω]
      simp only [r, W, Finset.mul_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [mul_left_comm, walsh_mul]
      rfl
    have hpt : ∀ ω, (r ω : ℂ) - restrictZero x₀ (fun ω => (r ω : ℂ)) ω =
        ((W (fun F => a F * (1 / 2) + a (τ.symm F) * (-1 / 2)) V ω : ℝ) : ℂ) := by
      intro ω
      rw [← W_lin, ← hw, show W a V = r from W_extend a ha Finset.subset_union_left]
      unfold restrictZero
      by_cases h : ω x₀ = 0
      · rw [Set.indicator_of_mem (by simpa using h)]
        simp [walsh, sgn, h]
        ring
      · rw [Set.indicator_of_notMem (by simpa using h)]
        simp [walsh, sgn, h]
        ring
    have hmem' : MemLp (restrictZero x₀ (fun ω => (r ω : ℂ))) 2 (bernoulli X) :=
      hmem.indicator (show MeasurableSet ((fun ω : X → Fin 2 => ω x₀) ⁻¹' {0}) from
        (measurable_pi_apply x₀) (measurableSet_singleton 0))
    have htri := l2Norm_le_add hmem hmem'
    have hdiff : l2Norm ((fun ω => (r ω : ℂ)) - restrictZero x₀ (fun ω => (r ω : ℂ))) ≤ ε := by
      have e : (fun ω => (r ω : ℂ)) - restrictZero x₀ (fun ω => (r ω : ℂ)) =
          fun ω => ((W (fun F => a F * (1 / 2) + a (τ.symm F) * (-1 / 2)) V ω : ℝ) : ℂ) :=
        funext hpt
      rw [e, l2Norm_ofReal, l2Norm_W]
      calc Real.sqrt (∑ F ∈ V, (a F * (1 / 2) + a (τ.symm F) * (-1 / 2)) ^ 2)
          ≤ Real.sqrt (ε ^ 2) := by
            apply Real.sqrt_le_sqrt
            have := sum_sq_le_of_reiter μ h0 τ V (hR none V)
            refine le_trans (Finset.sum_le_sum fun F _ => ?_) this
            nlinarith [sq_nonneg (Real.sqrt (μ (τ.symm F)) - Real.sqrt (μ F))]
        _ = ε := Real.sqrt_sq hε.le
    rw [hnorm] at htri ⊢
    linarith

end JuschenkoMonod.L31.PartB
end

section
open MeasureTheory
open scoped ENNReal Pointwise
namespace JuschenkoMonod.L31
variable (G X : Type*) [Group G] [MulAction G X] [DecidableEq X] (x₀ : X)
alias ii_imp_i := JuschenkoMonod.L31.PartB.ii_imp_i

theorem tfae [MulAction.IsPretransitive G X] :
    List.TFAE [CondI G X x₀, CondII G X, CondIII G X x₀, CondIV G X x₀] := by
  tfae_have 1 → 2 := i_imp_ii G X x₀
  tfae_have 2 → 3 := ii_imp_iii G X x₀
  tfae_have 3 → 4 := iii_imp_iv G X x₀
  tfae_have 4 → 2 := iv_imp_ii G X x₀
  tfae_have 2 → 1 := ii_imp_i G X x₀
  tfae_finish

end JuschenkoMonod.L31
end

section
open MeasureTheory
open scoped ENNReal Pointwise
open JuschenkoMonod.L31 in
theorem solution
    (G X : Type*) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] [DecidableEq X]
    (x₀ : X) :
    List.TFAE
      [∀ S : Finset G, ∀ ε : ℝ, 0 < ε → ∃ f : (X → Fin 2) → ℂ, MemLp f 2 (JuschenkoMonod.bernoulli X) ∧
          0 < JuschenkoMonod.l2Norm f ∧ (∀ g ∈ S, JuschenkoMonod.l2Norm (JuschenkoMonod.translate g f - f) ≤ ε * JuschenkoMonod.l2Norm f) ∧
          (1 - ε) * JuschenkoMonod.l2Norm f ≤ JuschenkoMonod.l2Norm (JuschenkoMonod.restrictZero x₀ f),
        ∃ m : Set (Finset X) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
          JuschenkoMonod.IsLampInvariant G m,
        ∃ m : Set (Finset X) → ℝ≥0∞, JuschenkoMonod.IsInvariantMean G m ∧ m {E | x₀ ∈ E} = 1 / 2,
        ∃ m : Set (Finset X) → ℝ≥0∞, JuschenkoMonod.IsInvariantMean G m ∧ m {E | x₀ ∈ E} = 1] :=
  tfae G X x₀

end
