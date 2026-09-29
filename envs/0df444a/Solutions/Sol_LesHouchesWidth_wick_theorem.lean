-- Prove2me | solution 1 for LesHouchesWidth.wick_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T06:35:35.115923+00:00
-- url     : https://prove2.me/submissions/baa3afc5-5ef0-452b-a070-ee9bff92fe96

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

/-! Wick / Isserlis theorem for `multivariateGaussian 0 K`.
Route (Wick library reused from the checked FeynmanWick proof): `multivariateGaussian 0 K` is the
image of `Measure.pi (gaussianReal 0 1)` under `y ↦ √K *ᵥ y`; every coordinate is a linear form
`√K i ⬝ᵥ y`; Gaussian integration by parts (Stein) gives the pairing recursion `wick_pi`; the
two-point weights are `(√K √K) i j = K i j`. Odd moments vanish because an involution with full
support has even support size. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace LesHouchesWidth
namespace WickLib

/-! ### Combinatorics of pairings (from a9908763) -/

section comb

variable {M : ℕ}

/-- Pairings of a subset `s`: involutions whose support is exactly `s`. -/
def P (s : Finset (Fin M)) : Finset (Equiv.Perm (Fin M)) :=
  Finset.univ.filter (fun σ => σ * σ = 1 ∧ σ.support = s)

/-- Wick sum over the pairings of `s`. -/
noncomputable def W (c : Fin M → Fin M → ℝ) (s : Finset (Fin M)) : ℝ :=
  ∑ σ ∈ P s, ∏ a ∈ s.filter (fun a => a < σ a), c a (σ a)

lemma mem_P {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)} :
    σ ∈ P s ↔ σ * σ = 1 ∧ σ.support = s := by simp [P]

lemma P_empty : P (∅ : Finset (Fin M)) = {1} := by
  ext σ; simp only [P, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.support_eq_empty_iff, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro rfl; simp

lemma W_empty (c : Fin M → Fin M → ℝ) : W c (∅ : Finset (Fin M)) = 1 := by
  simp [W, P_empty]

lemma invol_apply {σ : Equiv.Perm (Fin M)} (h : σ * σ = 1) (x : Fin M) : σ (σ x) = x := by
  simpa using congrArg (fun τ : Equiv.Perm (Fin M) => τ x) h

lemma swap_mul_apply_fwd {σ : Equiv.Perm (Fin M)} (h : σ * σ = 1) {a₀ b : Fin M}
    (hb : σ a₀ = b) (x : Fin M) :
    (Equiv.swap a₀ b * σ) x = if x = a₀ ∨ x = b then x else σ x := by
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  rw [Equiv.Perm.mul_apply]
  by_cases hx0 : x = a₀
  · subst hx0; simp [hb]
  by_cases hxb : x = b
  · subst hxb; simp [hσb]
  have h1 : σ x ≠ a₀ := by
    intro h'; apply hxb; rw [← invol_apply h x, h', hb]
  have h2 : σ x ≠ b := by
    intro h'; apply hx0; rw [← hb] at h'; exact σ.injective h'
  simp [hx0, hxb, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma fwd_mem {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)} (hσ : σ ∈ P s) {a₀ b : Fin M}
    (ha₀ : a₀ ∈ s) (hb : σ a₀ = b) :
    Equiv.swap a₀ b * σ ∈ P ((s.erase a₀).erase b) := by
  rw [mem_P] at hσ ⊢
  obtain ⟨h, hs⟩ := hσ
  have hne : σ a₀ ≠ a₀ := by rw [← Equiv.Perm.mem_support, hs]; exact ha₀
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  have key := swap_mul_apply_fwd h hb
  constructor
  · ext x
    rw [Equiv.Perm.mul_apply, key x, Equiv.Perm.one_apply]
    by_cases hx : x = a₀ ∨ x = b
    · simp [hx, key]
    · rw [if_neg hx, key (σ x)]
      have : ¬ (σ x = a₀ ∨ σ x = b) := by
        rintro (h' | h')
        · apply hx; right; rw [← invol_apply h x, h', hb]
        · apply hx; left; rw [← hb] at h'; exact σ.injective h'
      rw [if_neg this, invol_apply h]
  · ext x
    rw [Equiv.Perm.mem_support, key x, Finset.mem_erase, Finset.mem_erase, ← hs,
      Equiv.Perm.mem_support]
    by_cases hx0 : x = a₀
    · subst hx0; simp
    by_cases hxb : x = b
    · subst hxb; simp
    simp [hx0, hxb]

lemma bwd_mem {s : Finset (Fin M)} {τ : Equiv.Perm (Fin M)} {a₀ b : Fin M}
    (ha₀ : a₀ ∈ s) (hb : b ∈ s.erase a₀) (hτ : τ ∈ P ((s.erase a₀).erase b)) :
    Equiv.swap a₀ b * τ ∈ P s ∧ (Equiv.swap a₀ b * τ) a₀ = b := by
  rw [mem_P] at hτ ⊢
  obtain ⟨h, hs⟩ := hτ
  have hba : b ≠ a₀ := (Finset.mem_erase.1 hb).1
  have hbs : b ∈ s := (Finset.mem_erase.1 hb).2
  have hτa : τ a₀ = a₀ := by
    by_contra hc
    have := Equiv.Perm.mem_support.2 hc; rw [hs] at this; simp at this
  have hτb : τ b = b := by
    by_contra hc
    have := Equiv.Perm.mem_support.2 hc; rw [hs] at this; simp at this
  have hmid : ∀ x, x ≠ a₀ → x ≠ b → τ x ≠ a₀ ∧ τ x ≠ b := by
    intro x h0 h1
    refine ⟨fun h' => h0 (τ.injective (h'.trans hτa.symm)),
      fun h' => h1 (τ.injective (h'.trans hτb.symm))⟩
  have key : ∀ x, (Equiv.swap a₀ b * τ) x = if x = a₀ then b else if x = b then a₀ else τ x := by
    intro x
    rw [Equiv.Perm.mul_apply]
    by_cases h0 : x = a₀
    · subst h0; simp [hτa]
    by_cases h1 : x = b
    · subst h1; simp [hτb, hba]
    obtain ⟨m0, m1⟩ := hmid x h0 h1
    simp [h0, h1, Equiv.swap_apply_of_ne_of_ne m0 m1]
  refine ⟨⟨?_, ?_⟩, by simp [key]⟩
  · ext x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases h0 : x = a₀
    · subst h0; simp [key, hba]
    by_cases h1 : x = b
    · subst h1; simp [key, hba]
    obtain ⟨m0, m1⟩ := hmid x h0 h1
    rw [key x, if_neg h0, if_neg h1, key (τ x), if_neg m0, if_neg m1, invol_apply h]
  · ext x
    rw [Equiv.Perm.mem_support, key x]
    by_cases h0 : x = a₀
    · subst h0; simp [hba, ha₀]
    by_cases h1 : x = b
    · subst h1; simp [hba, hbs]; exact fun h => hba h.symm
    rw [if_neg h0, if_neg h1, ← Equiv.Perm.mem_support, hs]
    simp [h0, h1]

lemma prod_fwd (c : Fin M → Fin M → ℝ) {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)}
    (hσ : σ ∈ P s) {a₀ b : Fin M} (ha₀ : a₀ ∈ s) (hmin : ∀ x ∈ s, a₀ ≤ x) (hb : σ a₀ = b) :
    ∏ a ∈ s.filter (fun a => a < σ a), c a (σ a) =
      c a₀ b * ∏ a ∈ ((s.erase a₀).erase b).filter (fun a => a < (Equiv.swap a₀ b * σ) a),
        c a ((Equiv.swap a₀ b * σ) a) := by
  rw [mem_P] at hσ
  obtain ⟨h, hs⟩ := hσ
  have hsupp : a₀ ∈ σ.support := by rw [hs]; exact ha₀
  have hne : σ a₀ ≠ a₀ := Equiv.Perm.mem_support.1 hsupp
  have hbs : b ∈ s.erase a₀ := by
    rw [Finset.mem_erase, ← hb]
    exact ⟨hne, by rw [← hs]; exact Equiv.Perm.apply_mem_support.2 hsupp⟩
  have hab : a₀ < b :=
    lt_of_le_of_ne (hmin b (Finset.mem_of_mem_erase hbs)) (by rw [← hb]; exact hne.symm)
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  have key := swap_mul_apply_fwd h hb
  rw [Finset.prod_filter, Finset.prod_filter]
  conv_lhs => rw [← Finset.insert_erase ha₀, ← Finset.insert_erase hbs]
  rw [Finset.prod_insert (by simp [hab.ne]), Finset.prod_insert (by simp)]
  rw [hb, if_pos hab, hσb, if_neg (not_lt.2 hab.le), one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hxb : x ≠ b := (Finset.mem_erase.1 hx).1
  have hx0 : x ≠ a₀ := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1
  have : ¬ (x = a₀ ∨ x = b) := by tauto
  rw [key x, if_neg this]

lemma W_rec (c : Fin M → Fin M → ℝ) {s : Finset (Fin M)} (hs : s.Nonempty) :
    W c s = ∑ b ∈ s.erase (s.min' hs),
      c (s.min' hs) b * W c ((s.erase (s.min' hs)).erase b) := by
  have ha₀ : s.min' hs ∈ s := Finset.min'_mem s hs
  have hmin : ∀ x ∈ s, s.min' hs ≤ x := fun x hx => Finset.min'_le s x hx
  unfold W
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Fin M) => σ (s.min' hs))
    (t := s.erase (s.min' hs))]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_nbij' (fun σ => Equiv.swap (s.min' hs) b * σ)
      (fun τ => Equiv.swap (s.min' hs) b * τ)
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact fwd_mem hσ.1 ha₀ hσ.2
    · intro τ hτ
      obtain ⟨h1, h2⟩ := bwd_mem ha₀ hb hτ
      exact Finset.mem_filter.2 ⟨h1, h2⟩
    · intro σ _; simp [Equiv.swap_mul_self_mul]
    · intro τ _; simp [Equiv.swap_mul_self_mul]
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact prod_fwd c hσ.1 ha₀ hmin hσ.2
  · intro σ hσ
    rw [mem_P] at hσ
    have hsupp : s.min' hs ∈ σ.support := by rw [hσ.2]; exact ha₀
    rw [Finset.mem_erase]
    have h2 := Equiv.Perm.apply_mem_support.2 hsupp
    rw [hσ.2] at h2
    exact ⟨Equiv.Perm.mem_support.1 hsupp, h2⟩

end comb

/-! ### The standard Gaussian on `Fin N → ℝ` and its Lebesgue density -/

section dens

variable {N : ℕ}

/-- Unnormalised standard Gaussian weight. -/
noncomputable def gw (y : Fin N → ℝ) : ℝ := Real.exp (-(∑ i, y i ^ 2) / 2)

lemma prod_pdf (y : Fin N → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (y i) = (Real.sqrt (2 * Real.pi))⁻¹ ^ N * gw y := by
  simp only [gaussianPDFReal, gw, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

lemma pi_gauss_eq :
    Measure.pi (fun _ : Fin N => gaussianReal 0 1) =
      (volume : Measure (Fin N → ℝ)).withDensity
        (fun y => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) := by
  apply Measure.pi_eq
  intro s hs
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    setIntegral_nonneg (hs i) fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  have hint : Integrable (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) := by
    have := Integrable.fintype_prod (f := fun (_ : Fin N) (x : ℝ) => gaussianPDFReal 0 1 x)
      (μ := fun _ => volume) (fun _ => integrable_gaussianPDFReal 0 1)
    simpa [← volume_pi] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (ae_of_all _ fun y => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  rw [← integral_indicator hbox]
  have hind : (Set.univ.pi s).indicator (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) =
      fun y => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (y i) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hy i trivial) _).symm
    · rw [Set.indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ s i := by simpa [Set.mem_pi] using hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_indicator (hs _)]

lemma integral_pi_gauss (g : (Fin N → ℝ) → ℝ) :
    ∫ y, g y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ N * ∫ y, gw y * g y := by
  have hm : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  rw [pi_gauss_eq, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    prod_pdf, smul_eq_mul, mul_assoc]

end dens

/-! ### Gaussian integration by parts for products of linear forms -/

section stein

variable {N : ℕ}

lemma hasLineDerivAt_gw (y v : Fin N → ℝ) :
    HasLineDerivAt ℝ gw (-(v ⬝ᵥ y) * gw y) y v := by
  have h1 : HasDerivAt (fun t : ℝ => ∑ i, (y i + t * v i) ^ 2) (∑ i, 2 * y i * v i) 0 := by
    apply HasDerivAt.fun_sum; intro i _
    have hl : HasDerivAt (fun t : ℝ => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (y i)
    refine (hl.fun_pow 2).congr_deriv ?_
    simp
  have h3 : HasDerivAt (fun t : ℝ => gw (y + t • v))
      (Real.exp (-(∑ i, (y i + 0 * v i) ^ 2) / 2) * (-(∑ i, 2 * y i * v i) / 2)) 0 :=
    ((h1.neg).div_const 2).exp
  refine h3.congr_deriv ?_
  simp only [zero_mul, add_zero, gw, dotProduct]
  have : ∑ i, 2 * y i * v i = 2 * ∑ i, v i * y i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

lemma hasLineDerivAt_lin {ι : Type*} [DecidableEq ι] (t : Finset ι) (w : ι → Fin N → ℝ)
    (y v : Fin N → ℝ) :
    HasLineDerivAt ℝ (fun y : Fin N → ℝ => ∏ j ∈ t, w j ⬝ᵥ y)
      (∑ b ∈ t, (w b ⬝ᵥ v) * ∏ j ∈ t.erase b, w j ⬝ᵥ y) y v := by
  have := HasDerivAt.fun_finsetProd (u := t)
    (f := fun j (τ : ℝ) => w j ⬝ᵥ y + τ * (w j ⬝ᵥ v))
    (f' := fun j => w j ⬝ᵥ v) (x := 0) (fun j _ => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w j ⬝ᵥ v)).const_add (w j ⬝ᵥ y))
  have hfun : (fun τ : ℝ => ∏ j ∈ t, w j ⬝ᵥ (y + τ • v)) =
      fun τ => ∏ j ∈ t, (w j ⬝ᵥ y + τ * (w j ⬝ᵥ v)) := by
    funext τ
    simp [dotProduct_add, dotProduct_smul]
  unfold HasLineDerivAt
  rw [hfun]
  refine this.congr_deriv ?_
  simp [mul_comm]

lemma integrable_one_add_abs_pow_mul_exp {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ k * Real.exp (-b * x ^ 2)) := by
  have h : ∀ x : ℝ, (1 + |x|) ^ k * Real.exp (-b * x ^ 2) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (|x| ^ j * Real.exp (-b * x ^ 2)) := by
    intro x
    rw [add_comm, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; simp only [one_pow, mul_one]; ring
  simp_rw [h]
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  have := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (j : ℝ))
    (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, Real.rpow_natCast, abs_of_pos (Real.exp_pos _)]

lemma abs_le_prod_one_add (z : Fin N → ℝ) (j : Fin N) : |z j| ≤ ∏ i, (1 + |z i|) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => 1 + |z i|) (Finset.mem_univ j)]
  have h1 : 1 ≤ ∏ i ∈ Finset.univ.erase j, (1 + |z i|) :=
    Finset.one_le_prod (fun i _ => by linarith [abs_nonneg (z i)])
  nlinarith [abs_nonneg (z j)]

lemma abs_dot_le (u z : Fin N → ℝ) : |u ⬝ᵥ z| ≤ (∑ l, |u l|) * ∏ i, (1 + |z i|) := by
  calc |u ⬝ᵥ z| ≤ ∑ l, |u l * z l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |u l| * ∏ i, (1 + |z i|) := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le_prod_one_add z l) (abs_nonneg _)
    _ = (∑ l, |u l|) * ∏ i, (1 + |z i|) := (Finset.sum_mul _ _ _).symm

lemma abs_prod_dot_le {ι : Type*} (t : Finset ι) (w : ι → Fin N → ℝ) (z : Fin N → ℝ) :
    |∏ j ∈ t, w j ⬝ᵥ z| ≤ (∏ j ∈ t, ∑ l, |w j l|) * ∏ i, (1 + |z i|) ^ t.card := by
  rw [Finset.abs_prod, Finset.prod_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => abs_dot_le _ _)

lemma continuous_prod_dot {ι : Type*} (t : Finset ι) (w : ι → Fin N → ℝ) :
    Continuous (fun y : Fin N → ℝ => ∏ j ∈ t, w j ⬝ᵥ y) := by
  simp only [dotProduct]; fun_prop

lemma continuous_gw : Continuous (gw (N := N)) := by
  unfold gw; fun_prop

lemma integrable_gw_mul {ι : Type*} (t : Finset ι) (w : ι → Fin N → ℝ) :
    Integrable (fun y => gw y * ∏ j ∈ t, w j ⬝ᵥ y) := by
  have hdom : Integrable (fun z : Fin N → ℝ =>
      ∏ i, ((1 + |z i|) ^ t.card * Real.exp (-(1 / 2) * z i ^ 2))) := by
    have := Integrable.fintype_prod
      (f := fun (_ : Fin N) (x : ℝ) => (1 + |x|) ^ t.card * Real.exp (-(1 / 2) * x ^ 2))
      (μ := fun _ => volume)
      (fun _ => integrable_one_add_abs_pow_mul_exp (by norm_num) t.card)
    simpa [← volume_pi] using this
  refine (hdom.const_mul (∏ j ∈ t, ∑ l, |w j l|)).mono'
    (continuous_gw.mul (continuous_prod_dot t w)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, gw, abs_of_pos (Real.exp_pos _), Finset.prod_mul_distrib,
    ← Real.exp_sum]
  have hexp : -(∑ i, z i ^ 2) / 2 = ∑ i, -(1 / 2) * z i ^ 2 := by
    rw [← Finset.mul_sum]; ring
  rw [hexp]
  calc Real.exp (∑ i, -(1 / 2) * z i ^ 2) * |∏ j ∈ t, w j ⬝ᵥ z|
      ≤ Real.exp (∑ i, -(1 / 2) * z i ^ 2) *
          ((∏ j ∈ t, ∑ l, |w j l|) * ∏ i, (1 + |z i|) ^ t.card) :=
        mul_le_mul_of_nonneg_left (abs_prod_dot_le t w z) (Real.exp_pos _).le
    _ = _ := by ring

lemma stein_vol {ι : Type*} [DecidableEq ι] (w : ι → Fin N → ℝ) {s : Finset ι} {a₀ : ι}
    (ha₀ : a₀ ∈ s) :
    ∫ y, gw y * ∏ j ∈ s, w j ⬝ᵥ y =
      ∑ b ∈ s.erase a₀, (w a₀ ⬝ᵥ w b) * ∫ y, gw y * ∏ j ∈ (s.erase a₀).erase b, w j ⬝ᵥ y := by
  have hsplit : ∀ y : Fin N → ℝ,
      ∏ j ∈ s, w j ⬝ᵥ y = (w a₀ ⬝ᵥ y) * ∏ j ∈ s.erase a₀, w j ⬝ᵥ y :=
    fun y => (Finset.mul_prod_erase s (fun j => w j ⬝ᵥ y) ha₀).symm
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin N → ℝ))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := gw) (f' := fun y => -(w a₀ ⬝ᵥ y) * gw y)
    (g := fun y => ∏ j ∈ s.erase a₀, w j ⬝ᵥ y)
    (g' := fun y => ∑ b ∈ s.erase a₀, (w b ⬝ᵥ w a₀) * ∏ j ∈ (s.erase a₀).erase b, w j ⬝ᵥ y)
    (v := w a₀) ?_ ?_ ?_
    (fun y _ => hasLineDerivAt_gw y (w a₀))
    (fun y _ => hasLineDerivAt_lin (s.erase a₀) w y (w a₀))
  · simp only [ContinuousLinearMap.mul_apply'] at hibp
    have hL : ∫ y, gw y * ∏ j ∈ s, w j ⬝ᵥ y =
        -∫ y, -(w a₀ ⬝ᵥ y) * gw y * ∏ j ∈ s.erase a₀, w j ⬝ᵥ y := by
      rw [← integral_neg]
      congr 1; funext y; rw [hsplit]; ring
    rw [hL, ← hibp]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl; intro b _
      rw [← integral_const_mul, dotProduct_comm (w b)]
      congr 1; funext y; ring
    · intro b _
      exact ((integrable_gw_mul _ w).const_mul (w b ⬝ᵥ w a₀)).congr
        (Filter.Eventually.of_forall fun y => by simp only; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    exact (integrable_gw_mul s w).neg.congr
      (Filter.Eventually.of_forall fun y => by simp only [Pi.neg_apply]; rw [hsplit]; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro b _
    exact ((integrable_gw_mul _ w).const_mul (w b ⬝ᵥ w a₀)).congr
      (Filter.Eventually.of_forall fun y => by simp only; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    exact integrable_gw_mul _ w

/-- Stein recursion under the product of standard Gaussians. -/
lemma stein_pi {ι : Type*} [DecidableEq ι] (w : ι → Fin N → ℝ) {s : Finset ι} {a₀ : ι}
    (ha₀ : a₀ ∈ s) :
    ∫ y, ∏ j ∈ s, w j ⬝ᵥ y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∑ b ∈ s.erase a₀, (w a₀ ⬝ᵥ w b) *
        ∫ y, ∏ j ∈ (s.erase a₀).erase b, w j ⬝ᵥ y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  rw [integral_pi_gauss, stein_vol w ha₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_pi_gauss]
  ring

lemma wick_pi {M : ℕ} (w : Fin M → Fin N → ℝ) (s : Finset (Fin M)) :
    ∫ y, ∏ j ∈ s, w j ⬝ᵥ y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      W (fun a b => w a ⬝ᵥ w b) s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [W_empty]; simp
    · rw [W_rec _ hs, stein_pi w (Finset.min'_mem s hs)]
      apply Finset.sum_congr rfl
      intro b _
      have hsub : (s.erase (s.min' hs)).erase b ⊂ s :=
        (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset (Finset.min'_mem s hs))
      rw [ih _ hsub]

lemma cov_pi (u v : Fin N → ℝ) :
    ∫ y, (u ⬝ᵥ y) * (v ⬝ᵥ y) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) = u ⬝ᵥ v := by
  have h := stein_pi ![u, v] (s := Finset.univ) (Finset.mem_univ 0)
  have e1 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have e2 : ({1} : Finset (Fin 2)).erase 1 = ∅ := by decide
  rw [e1, Finset.sum_singleton, e2] at h
  simpa [Fin.prod_univ_two] using h

end stein

section lesHouches

open scoped MatrixOrder

lemma P_univ_even (m : ℕ) :
    P (Finset.univ : Finset (Fin (2 * m))) = LesHouchesWidth.pairings (2 * m) := by
  ext σ
  simp only [P, LesHouchesWidth.pairings, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.eq_univ_iff_forall, Equiv.Perm.mem_support]
  constructor
  · rintro ⟨h1, h2⟩; exact fun k => ⟨invol_apply h1 k, h2 k⟩
  · intro h; exact ⟨Equiv.ext fun i => by simpa using (h i).1, fun k => (h k).2⟩

lemma P_univ_odd (m : ℕ) : P (Finset.univ : Finset (Fin (2 * m + 1))) = ∅ := by
  ext σ
  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_and]
  intro h1 h2
  have := Equiv.Perm.two_dvd_card_support (σ := σ) (by rw [pow_two]; exact h1)
  rw [h2, Finset.card_univ, Fintype.card_fin] at this
  omega

theorem wick_mvG {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.PosSemidef) {M : ℕ}
    (μs : Fin M → Fin d) :
    ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian 0 K) =
      W (fun a b => K (μs a) (μs b)) Finset.univ := by
  set A : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt K with hAdef
  have hrep : multivariateGaussian 0 K = (Measure.pi fun _ : Fin d => gaussianReal 0 1).map
      (fun y => WithLp.toLp 2 (A *ᵥ y)) := by
    rw [multivariateGaussian, ← map_pi_eq_stdGaussian,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext y
    simp [hAdef]
  have hmeas : Measurable (fun y : Fin d → ℝ => WithLp.toLp 2 (A *ᵥ y)) := by fun_prop
  rw [hrep, integral_map hmeas.aemeasurable (by fun_prop)]
  have h1 : ∫ y, ∏ k, (WithLp.toLp 2 (A *ᵥ y)) (μs k)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) =
      W (fun a b => A (μs a) ⬝ᵥ A (μs b)) Finset.univ := by
    rw [← wick_pi (fun j => A (μs j))]
    rfl
  rw [h1]
  have hAA : A * A = K := CFC.sqrt_mul_sqrt_self K hK.nonneg
  have hsym : A.transpose = A := by
    have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg K)
    have := hA.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hs : ∀ a b, A a b = A b a := by
    intro a b
    have := (Matrix.transpose_apply A b a).symm
    rwa [hsym] at this
  have hdot : ∀ i j : Fin d, A i ⬝ᵥ A j = K i j := by
    intro i j
    rw [← hAA]
    simp only [Matrix.mul_apply, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by rw [hs j l]
  simp only [hdot]

end lesHouches

end WickLib
end LesHouchesWidth

open MeasureTheory ProbabilityTheory LesHouchesWidth in
theorem solution {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.PosSemidef) :
    (∀ (m : ℕ) (μs : Fin (2 * m) → Fin d),
      ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian 0 K) =
        ∑ π ∈ pairings (2 * m),
          ∏ k ∈ Finset.univ.filter (fun k => k < π k), K (μs k) (μs (π k))) ∧
    (∀ (m : ℕ) (μs : Fin (2 * m + 1) → Fin d),
      ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian 0 K) = 0) := by
  constructor
  · intro m μs
    rw [WickLib.wick_mvG K hK μs, WickLib.W, WickLib.P_univ_even]
  · intro m μs
    rw [WickLib.wick_mvG K hK μs, WickLib.W, WickLib.P_univ_odd, Finset.sum_empty]
