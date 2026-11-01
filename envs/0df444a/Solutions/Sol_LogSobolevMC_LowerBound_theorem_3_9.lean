-- Prove2me | solution 1 for LogSobolevMC.LowerBound.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T10:28:25.624393+00:00
-- url     : https://prove2.me/submissions/9facc3a3-2404-4a76-8739-dff2c5c2c4f1

import Mathlib
import Definitions.Def_LogSobolevMC_LowerBound_Setting

section

end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V]
lemma weighted_holder (w a b : V → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, w i * a i * b i) ≤
      (∑ i, w i * (a i)^p)^(1/p) * (∑ i, w i * (b i)^q)^(1/q) := by
  have hp : p ≠ 0 := hpq.ne_zero
  have hq : q ≠ 0 := hpq.symm.ne_zero
  have hs : 1/p + 1/q = 1 := by
    simpa only [one_div] using (Real.holderConjugate_iff.mp hpq).2
  have ht (i : V) : (w i)^(1/p) * a i * ((w i)^(1/q) * b i) = w i * a i * b i := by
    by_cases hz : w i = 0
    · simp only [hz, Real.zero_rpow (one_div_ne_zero hp), Real.zero_rpow (one_div_ne_zero hq), zero_mul, mul_zero]
    · have hpos := (hw i).lt_of_ne' hz
      calc
        _ = ((w i)^(1/p) * (w i)^(1/q)) * a i * b i := by ring
        _ = _ := by rw [← Real.rpow_add hpos, hs, Real.rpow_one]
  have hpa (i : V) : ((w i)^(1/p) * a i)^p = w i * (a i)^p := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (ha i), ← Real.rpow_mul (hw i)]
    simp only [one_div_mul_cancel hp, Real.rpow_one]
  have hqb (i : V) : ((w i)^(1/q) * b i)^q = w i * (b i)^q := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (hb i), ← Real.rpow_mul (hw i)]
    simp only [one_div_mul_cancel hq, Real.rpow_one]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i => (w i)^(1/p) * a i) (g := fun i => (w i)^(1/q) * b i) hpq
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (ha i))
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (hb i))
  simpa only [ht, hpa, hqb] using h
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V]

noncomputable def complexLp (w : V → ℝ) (p : ℝ) (f : V → ℂ) : ℝ :=
  (∑ i, w i * ‖f i‖^p)^(1/p)

lemma complexLp_real (w : V → ℝ) (p : ℝ) (f : V → ℝ) :
    complexLp w p (fun i => (f i : ℂ)) = LogSobolevMC.ChiSquare.lpNorm w p f := by
  simp only [complexLp, LogSobolevMC.ChiSquare.lpNorm, Complex.norm_real, Real.norm_eq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma complexLp_nonneg (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ℝ) (f : V → ℂ) :
    0 ≤ complexLp w p f := by
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (norm_nonneg _) _)

lemma complexLp_mono (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) {p : ℝ} (hp : 0 < p)
    (f g : V → ℂ) (h : ∀ i, ‖f i‖ ≤ ‖g i‖) : complexLp w p f ≤ complexLp w p g := by
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (norm_nonneg _) _)
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (h i) hp.le) (hw i)
  · positivity

lemma complex_holder (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) {p q : ℝ}
    (hpq : p.HolderConjugate q) (f g : V → ℂ) :
    ‖∑ i, (w i : ℂ) * f i * g i‖ ≤ complexLp w p f * complexLp w q g := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * f i * g i‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖f i‖ * ‖g i‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]
    _ ≤ _ := weighted_holder w (fun i => ‖f i‖) (fun i => ‖g i‖) hpq hw
      (fun i => norm_nonneg _) (fun i => norm_nonneg _)
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V]

noncomputable def positiveDual (u : V → ℝ) (N p : ℝ) (i : V) : ℝ := (u i / N)^(p-1)

omit [Fintype V] in
lemma positiveDual_pos (u : V → ℝ) {N p : ℝ} (hu : ∀ i, 0 < u i) (hN : 0 < N)
    (i : V) : 0 < positiveDual u N p i := Real.rpow_pos_of_pos (div_pos (hu i) hN) _

lemma conjugate_product {p q : ℝ} (hpq : p.HolderConjugate q) : (p-1)*q=p := by
  have h := (Real.holderConjugate_iff.mp hpq).2
  have hp := hpq.ne_zero
  have hq := hpq.symm.ne_zero
  field_simp at h
  nlinarith

lemma positiveDual_moment (w u : V → ℝ) {N p q : ℝ}
    (hu : ∀ i, 0 < u i) (hN : 0 < N) (hpq : p.HolderConjugate q)
    (hs : ∑ i, w i * (u i)^p = N^p) :
    ∑ i, w i * (positiveDual u N p i)^q = 1 := by
  have he (i : V) : (positiveDual u N p i)^q = (u i)^p / N^p := by
    rw [positiveDual, ← Real.rpow_mul (div_pos (hu i) hN).le,
      conjugate_product hpq, Real.div_rpow (hu i).le hN.le]
  simp only [he, ← mul_div_assoc, ← Finset.sum_div, hs]
  exact div_self (Real.rpow_pos_of_pos hN _).ne'

lemma positiveDual_pair (w u : V → ℝ) {N p : ℝ}
    (hu : ∀ i, 0 < u i) (hN : 0 < N)
    (hs : ∑ i, w i * (u i)^p = N^p) :
    ∑ i, w i * u i * positiveDual u N p i = N := by
  have he (i : V) : u i * positiveDual u N p i = (u i)^p / N^(p-1) := by
    rw [positiveDual, Real.div_rpow (hu i).le hN.le, ← mul_div_assoc]
    congr 1
    calc
      u i * (u i)^(p-1) = (u i)^(1:ℝ) * (u i)^(p-1) := by rw [Real.rpow_one]
      _ = (u i)^p := by rw [← Real.rpow_add (hu i)]; congr 1; ring
  simp_rw [mul_assoc, he, ← mul_div_assoc]
  rw [← Finset.sum_div, hs]
  apply (div_eq_iff (Real.rpow_pos_of_pos hN _).ne').2
  calc
    N^p = N^((1:ℝ)+(p-1)) := by congr 1; ring
    _ = N * N^(p-1) := by rw [Real.rpow_add hN, Real.rpow_one]
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V]

noncomputable def analyticDual (g : V → ℝ) (r q : ℝ) (z : ℂ) (i : V) : ℂ :=
  Complex.exp (((r : ℂ) * ((1-z)/2 + z/(q:ℂ))) * (Real.log (g i) : ℂ))

omit [Fintype V] in
lemma analyticDual_differentiable (g : V → ℝ) (r q : ℝ) (i : V) :
    Differentiable ℂ (fun z => analyticDual g r q z i) := by
  unfold analyticDual
  fun_prop

omit [Fintype V] in
lemma analyticDual_norm (g : V → ℝ) (hg : ∀ i, 0 < g i) (r q : ℝ) (z : ℂ) (i : V) :
    ‖analyticDual g r q z i‖ = (g i)^(r*((1-z.re)/2+z.re/q)) := by
  rw [analyticDual, Complex.norm_exp, Real.rpow_def_of_pos (hg i)]
  congr 1
  simp only [Complex.mul_re, Complex.add_re, Complex.div_ofNat_re, Complex.div_ofReal_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re, mul_zero, zero_mul, sub_zero]
  ring

omit [Fintype V] in
lemma analyticDual_at (g : V → ℝ) (hg : ∀ i, 0 < g i) (r q θ : ℝ)
    (hθ : r*((1-θ)/2+θ/q)=1) (i : V) : analyticDual g r q (θ : ℂ) i = (g i : ℂ) := by
  have hcast : (r : ℂ) * ((1-(θ:ℂ))/2+(θ:ℂ)/(q:ℂ)) = 1 := by exact_mod_cast hθ
  rw [analyticDual, hcast, one_mul, ← Complex.ofReal_exp, Real.exp_log (hg i)]

lemma analyticDual_boundary (w g : V → ℝ) (hg : ∀ i, 0 < g i)
    {r q : ℝ} (hq : q ≠ 0) (hs : ∑ i, w i * (g i)^r = 1) (z : ℂ) :
    (z.re=0 → complexLp w 2 (analyticDual g r q z)=1) ∧
    (z.re=1 → complexLp w q (analyticDual g r q z)=1) := by
  constructor
  · intro hz
    simp only [complexLp, analyticDual_norm g hg, hz, sub_zero, zero_div, add_zero]
    have he (i : V) : ((g i)^(r*(1/2:ℝ)))^(2:ℝ) = (g i)^r := by
      rw [← Real.rpow_mul (hg i).le]
      congr 1
      ring
    simp only [he, hs, Real.one_rpow]
  · intro hz
    simp only [complexLp, analyticDual_norm g hg, hz, sub_self, zero_div, zero_add]
    have he (i : V) : ((g i)^(r*(1/q)))^q = (g i)^r := by
      rw [← Real.rpow_mul (hg i).le]
      congr 1
      field_simp
    simp only [he, hs, Real.one_rpow]

omit [Fintype V] in
lemma analyticDual_strip_bound (g : V → ℝ) (r q : ℝ) (i : V) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖analyticDual g r q z i‖ ≤
      Real.exp (|r*Real.log (g i)/2| + |r*Real.log (g i)*(1/q-1/2)|) := by
  rw [analyticDual, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have he : (((r : ℂ) * ((1-z)/2+z/(q:ℂ))) * (Real.log (g i):ℂ)).re =
      r*Real.log (g i)/2 + z.re*(r*Real.log (g i)*(1/q-1/2)) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.div_ofNat_re, Complex.div_ofReal_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.one_re, mul_zero, zero_mul, sub_zero]
    ring
  rw [he]
  have h₁ := le_abs_self (r*Real.log (g i)/2)
  have h₂ := le_abs_self (r*Real.log (g i)*(1/q-1/2))
  by_cases h : 0 ≤ r*Real.log (g i)*(1/q-1/2)
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [Nonempty V]

lemma vector_interpolation (w : V → ℝ) (hw : ∀ i, 0 < w i)
    (F : ℂ → V → ℂ) (hF : ∀ i, Differentiable ℂ (fun z => F z i))
    (B : V → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hbound : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ∀ i, ‖F z i‖ ≤ B i)
    {p r q q' θ A D : ℝ} (hpr : p.HolderConjugate r) (hqq : q.HolderConjugate q')
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hrel : r*((1-θ)/2+θ/q')=1)
    (hleft : ∀ z : ℂ, z.re=0 → complexLp w 2 (F z) ≤ A)
    (hright : ∀ z : ℂ, z.re=1 → complexLp w q (F z) ≤ D)
    (u : V → ℝ) (hu : ∀ i, 0 < u i) (htu : ∀ i, F (θ:ℂ) i = (u i:ℂ)) :
    complexLp w p (F (θ:ℂ)) ≤ A^(1-θ) * D^θ := by
  let N : ℝ := (∑ i, w i * (u i)^p)^(1/p)
  have hS : 0 < ∑ i, w i * (u i)^p := Finset.sum_pos
    (fun i _ => mul_pos (hw i) (Real.rpow_pos_of_pos (hu i) _)) Finset.univ_nonempty
  have hN : 0 < N := Real.rpow_pos_of_pos hS _
  have hNp : ∑ i, w i * (u i)^p = N^p := by
    dsimp [N]
    rw [← Real.rpow_mul hS.le, one_div_mul_cancel hpr.ne_zero, Real.rpow_one]
  let g := positiveDual u N p
  have hg : ∀ i, 0 < g i := positiveDual_pos u hu hN
  have hgm : ∑ i, w i * (g i)^r = 1 := positiveDual_moment w u hu hN hpr hNp
  let f : ℂ → ℂ := fun z => ∑ i, (w i:ℂ) * F z i * analyticDual g r q' z i
  have hd : Differentiable ℂ f := by
    apply Differentiable.fun_sum
    intro i _
    exact ((hF i).const_mul _).mul (analyticDual_differentiable g r q' i)
  have hb : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ i, |w i| * B i * Real.exp (|r*Real.log (g i)/2| + |r*Real.log (g i)*(1/q'-1/2)|), ?_⟩
    rintro b ⟨z, hz, rfl⟩
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound z hz.1 hz.2 i) (abs_nonneg _))
      (analyticDual_strip_bound g r q' i hz.1 hz.2) (norm_nonneg _)
      (mul_nonneg (abs_nonneg _) (hB i))
  have hl : ∀ z ∈ Complex.re ⁻¹' ({0}:Set ℝ), ‖f z‖ ≤ A := by
    intro z hz
    have hb := (analyticDual_boundary w g hg hqq.symm.ne_zero hgm z).1 hz
    exact (complex_holder w (fun i => (hw i).le) Real.HolderConjugate.two_two
      (F z) (analyticDual g r q' z)).trans (by rw [hb, mul_one]; exact hleft z hz)
  have hr : ∀ z ∈ Complex.re ⁻¹' ({1}:Set ℝ), ‖f z‖ ≤ D := by
    intro z hz
    have hb := (analyticDual_boundary w g hg hqq.symm.ne_zero hgm z).2 hz
    exact (complex_holder w (fun i => (hw i).le) hqq
      (F z) (analyticDual g r q' z)).trans (by rw [hb, mul_one]; exact hright z hz)
  have hthree := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f
    (z := (θ:ℂ)) ⟨hθ0.le,hθ1.le⟩ ⟨hd.differentiableOn,hd.continuous.continuousOn⟩ hb hl hr
  have hvalue : f (θ:ℂ) = (N:ℂ) := by
    simp only [f, htu, analyticDual_at g hg r q' θ hrel]
    exact_mod_cast positiveDual_pair w u hu hN hNp
  have hnorm : complexLp w p (F (θ:ℂ)) = N := by
    simp only [complexLp, htu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hu _)]
    rfl
  rw [hnorm]
  simpa only [hvalue, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN, Complex.ofReal_re] using hthree
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped ComplexConjugate
namespace LogSobolevMC.LowerBound.Fresh

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def weightedFourier (w : V → ℝ) (psi : V → V → ℝ)
    (f : V → ℂ) (i : V) : ℂ := ∑ x, (w x : ℂ) * (psi i x : ℂ) * f x

lemma weighted_fourier_inverse (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (psi : V → V → ℝ)
    (hc : ∀ x y, ∑ i, psi i x * psi i y = if x = y then 1 / w x else 0)
    (f : V → ℂ) (x : V) :
    ∑ i, (psi i x : ℂ) * weightedFourier w psi f i = f x := by
  have hc' : ∀ x y, ∑ i, (psi i x : ℂ) * (psi i y : ℂ) =
      if x = y then 1 / (w x : ℂ) else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst y
      simpa using congrArg Complex.ofReal (hc x x)
    · simpa [hxy] using congrArg Complex.ofReal (hc x y)
  calc
    _ = ∑ y, ((w y : ℂ) * (∑ i, (psi i x : ℂ) * (psi i y : ℂ))) * f y := by
      simp only [weightedFourier, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = f x := by
      simp [hc', (hw x).ne']

lemma weighted_fourier_parseval (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (psi : V → V → ℝ)
    (hc : ∀ x y, ∑ i, psi i x * psi i y = if x = y then 1 / w x else 0)
    (f : V → ℂ) :
    ∑ i, ‖weightedFourier w psi f i‖ ^ 2 = ∑ x, w x * ‖f x‖ ^ 2 := by
  have hinner : ∑ i, conj (weightedFourier w psi f i) * weightedFourier w psi f i =
      ∑ x, (w x : ℂ) * (conj (f x) * f x) := by
    calc
      _ = ∑ x, ((w x : ℂ) * conj (f x)) *
          (∑ i, (psi i x : ℂ) * weightedFourier w psi f i) := by
        conv_lhs => arg 2; intro i; arg 1; unfold weightedFourier
        simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [weighted_fourier_inverse w hw psi hc f, mul_assoc]
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self] using hinner

lemma fourier_phase_preserves_norm (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (psi : V → V → ℝ)
    (hc : ∀ x y, ∑ i, psi i x * psi i y = if x = y then 1 / w x else 0)
    (f : V → ℂ) (phase : V → ℂ) (hp : ∀ i, ‖phase i‖ = 1) :
    ∑ i, ‖phase i * weightedFourier w psi f i‖ ^ 2 = ∑ x, w x * ‖f x‖ ^ 2 := by
  simpa only [norm_mul, hp, one_mul] using weighted_fourier_parseval w hw psi hc f

end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def weightedSynthesis (psi : V → V → ℝ) (c : V → ℂ) (x : V) : ℂ :=
  ∑ i, (psi i x : ℂ) * c i

lemma weighted_fourier_synthesis (w : V → ℝ) (psi : V → V → ℝ)
    (ho : ∀ i j, ∑ x, w x * psi i x * psi j x = if i = j then 1 else 0)
    (c : V → ℂ) (i : V) :
    weightedFourier w psi (weightedSynthesis psi c) i = c i := by
  have ho' : ∀ i j, ∑ x, (w x : ℂ) * (psi i x : ℂ) * (psi j x : ℂ) =
      if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa using congrArg Complex.ofReal (ho i i)
    · simpa [hij] using congrArg Complex.ofReal (ho i j)
  calc
    _ = ∑ j, (∑ x, (w x : ℂ) * (psi i x : ℂ) * (psi j x : ℂ)) * c j := by
      simp only [weightedFourier, weightedSynthesis, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = c i := by simp [ho']

lemma weighted_synthesis_parseval (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (psi : V → V → ℝ)
    (hc : ∀ x y, ∑ i, psi i x * psi i y = if x = y then 1 / w x else 0)
    (ho : ∀ i j, ∑ x, w x * psi i x * psi j x = if i = j then 1 else 0)
    (c : V → ℂ) :
    ∑ x, w x * ‖weightedSynthesis psi c x‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  rw [← weighted_fourier_parseval w hw psi hc (weightedSynthesis psi c)]
  simp only [weighted_fourier_synthesis w psi ho c]

lemma weighted_spectral_phase_isometry (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (psi : V → V → ℝ)
    (hc : ∀ x y, ∑ i, psi i x * psi i y = if x = y then 1 / w x else 0)
    (ho : ∀ i j, ∑ x, w x * psi i x * psi j x = if i = j then 1 else 0)
    (f : V → ℂ) (phase : V → ℂ) (hp : ∀ i, ‖phase i‖ = 1) :
    ∑ x, w x * ‖weightedSynthesis psi (fun i => phase i * weightedFourier w psi f i) x‖ ^ 2 =
      ∑ x, w x * ‖f x‖ ^ 2 := by
  rw [weighted_synthesis_parseval w hw psi hc ho]
  exact fourier_phase_preserves_norm w hw psi hc f phase hp

end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def complexHeat (w : V → ℝ) (psi : V → V → ℝ) (β : V → ℝ)
    (z : ℂ) (f : V → ℂ) : V → ℂ :=
  weightedSynthesis psi (fun i => Complex.exp (z * (β i : ℂ)) * weightedFourier w psi f i)

omit [DecidableEq V] in
lemma complexHeat_differentiable (w : V → ℝ) (psi : V → V → ℝ) (β : V → ℝ)
    (f : V → ℂ) (x : V) : Differentiable ℂ (fun z => complexHeat w psi β z f x) := by
  unfold complexHeat weightedSynthesis
  apply Differentiable.fun_sum
  intro i _
  exact (((differentiable_id.mul_const _).cexp).mul_const _).const_mul _

lemma complexHeat_zero (w : V → ℝ) (hw : ∀ x, 0 < w x) (psi : V → V → ℝ)
    (hc : ∀ x y, ∑ i, psi i x * psi i y = if x = y then 1 / w x else 0)
    (β : V → ℝ) (f : V → ℂ) : complexHeat w psi β 0 f = f := by
  funext x
  simpa only [complexHeat, weightedSynthesis, zero_mul, Complex.exp_zero, one_mul] using
    weighted_fourier_inverse w hw psi hc f x

lemma complexHeat_add (w : V → ℝ) (psi : V → V → ℝ)
    (ho : ∀ i j, ∑ x, w x * psi i x * psi j x = if i = j then 1 else 0)
    (β : V → ℝ) (z u : ℂ) (f : V → ℂ) :
    complexHeat w psi β (z + u) f = complexHeat w psi β z (complexHeat w psi β u f) := by
  funext x
  simp only [complexHeat, weighted_fourier_synthesis w psi ho, weightedSynthesis,
    add_mul, Complex.exp_add, mul_assoc]

lemma complexHeat_imaginary_isometry (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (psi : V → V → ℝ)
    (hc : ∀ x y, ∑ i, psi i x * psi i y = if x = y then 1 / w x else 0)
    (ho : ∀ i j, ∑ x, w x * psi i x * psi j x = if i = j then 1 else 0)
    (β : V → ℝ) (z : ℂ) (hz : z.re = 0) (f : V → ℂ) :
    complexLp w 2 (complexHeat w psi β z f) = complexLp w 2 f := by
  have h := weighted_spectral_phase_isometry w hw psi hc ho f
    (fun i => Complex.exp (z * (β i : ℂ))) (fun i => by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, hz])
  simp only [complexLp, Real.rpow_two, complexHeat]
  rw [h]

omit [DecidableEq V] in
lemma complexHeat_strip_bound (w : V → ℝ) (psi : V → V → ℝ) (β : V → ℝ)
    (f : V → ℂ) (x : V) {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖complexHeat w psi β z f x‖ ≤
      ∑ i, |psi i x| * Real.exp |β i| * ‖weightedFourier w psi f i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  by_cases h : 0 ≤ β i
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
lemma scalar_exp_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => t ^ n / (Nat.factorial n : ℝ)) (Real.exp t) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t

lemma poisson_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ)) 1 := by
  have h := (scalar_exp_hasSum t).mul_left (Real.exp (-t))
  simpa only [mul_div_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero] using h

lemma poisson_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ) := by positivity
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma diagonalized_pow (R L : Matrix V V ℝ) (κ : V → ℝ)
    (hRL : R * L = 1) (hLR : L * R = 1) (n : ℕ) :
    (R * Matrix.diagonal κ * L) ^ n = R * Matrix.diagonal (fun i => κ i ^ n) * L := by
  induction n with
  | zero => simpa using hRL.symm
  | succ n ih =>
    rw [pow_succ, ih]
    calc
      R * Matrix.diagonal (fun i => κ i ^ n) * L * (R * Matrix.diagonal κ * L) =
          R * (Matrix.diagonal (fun i => κ i ^ n) * (L * R) * Matrix.diagonal κ) * L := by
            simp only [Matrix.mul_assoc]
      _ = R * Matrix.diagonal (fun i => κ i ^ (n + 1)) * L := by
        simp only [hLR, Matrix.mul_one, Matrix.diagonal_mul_diagonal, pow_succ]

lemma poisson_eigen_hasSum (t κ : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ) * κ ^ n)
      (Real.exp (t * (κ - 1))) := by
  have h := (scalar_exp_hasSum (t * κ)).mul_left (Real.exp (-t))
  have he : Real.exp (-t) * Real.exp (t * κ) = Real.exp (t * (κ - 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  have hf : (fun n : ℕ => Real.exp (-t) * ((t * κ) ^ n / (Nat.factorial n : ℝ))) =
      (fun n : ℕ => Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ) * κ ^ n) := by
    funext n
    rw [mul_pow]
    ring
  rw [hf] at h
  exact h

lemma heat_kernel_spectral (R L : Matrix V V ℝ) (κ : V → ℝ)
    (hRL : R * L = 1) (hLR : L * R = 1) (t : ℝ) (i j : V) :
    MarkovMixing.heatKernel (R * Matrix.diagonal κ * L) t i j =
      ∑ a, R i a * Real.exp (t * (κ a - 1)) * L a j := by
  have hs : HasSum (fun n : ℕ => ∑ a, R i a *
      (Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ) * κ a ^ n) * L a j)
      (∑ a, R i a * Real.exp (t * (κ a - 1)) * L a j) := by
    exact hasSum_sum fun a _ => ((poisson_eigen_hasSum t (κ a)).mul_left (R i a)).mul_right (L a j)
  rw [MarkovMixing.heatKernel]
  convert hs.tsum_eq using 1
  congr 1
  ext n
  rw [diagonalized_pow R L κ hRL hLR n]
  change Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ) *
    (∑ a, (R * Matrix.diagonal (fun i => κ i ^ n)) i a * L a j) = _
  simp only [Matrix.mul_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma stochastic_one : MarkovMixing.IsStochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro i j
    simp only [Matrix.one_apply]
    split <;> norm_num
  · intro i
    change ∑ j, (1 : Matrix V V ℝ) i j = 1
    simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [DecidableEq V] in
lemma stochastic_mul {A B : Matrix V V ℝ}
    (hA : MarkovMixing.IsStochastic A) (hB : MarkovMixing.IsStochastic B) :
    MarkovMixing.IsStochastic (A * B) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · intro i
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

lemma stochastic_pow {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K) (n : ℕ) :
    MarkovMixing.IsStochastic (K ^ n) := by
  induction n with
  | zero => simpa using (stochastic_one (V := V))
  | succ n ih => simpa only [pow_succ] using stochastic_mul ih hK

omit [DecidableEq V] in
lemma stochastic_entry_le_one {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (i j : V) : K i j ≤ 1 := by
  rw [← hK.2 i]
  exact Finset.single_le_sum (fun k _ => hK.1 i k) (Finset.mem_univ j)
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma heat_summable {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (i j : V) :
    Summable (fun n : ℕ => Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ) * (K ^ n) i j) := by
  refine (poisson_hasSum t).summable.of_nonneg_of_le (fun n =>
    mul_nonneg (poisson_nonneg ht n) ((stochastic_pow hK n).1 i j)) ?_
  intro n
  exact mul_le_of_le_one_right (poisson_nonneg ht n)
    (stochastic_entry_le_one (stochastic_pow hK n) i j)

lemma heat_stochastic {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) : MarkovMixing.IsStochastic (MarkovMixing.heatKernel K t) := by
  constructor
  · intro i j
    exact tsum_nonneg fun n => mul_nonneg (poisson_nonneg ht n) ((stochastic_pow hK n).1 i j)
  · intro i
    simp only [MarkovMixing.heatKernel]
    rw [← Summable.tsum_finsetSum]
    · simp_rw [← Finset.mul_sum, (stochastic_pow hK _).2, mul_one]
      exact (poisson_hasSum t).tsum_eq
    · intro j _
      exact heat_summable hK ht i j

lemma heat_diagonal_pos {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (i : V) : 0 < MarkovMixing.heatKernel K t i i := by
  have h := (heat_summable hK ht i i).le_tsum 0 (fun n _ =>
    mul_nonneg (poisson_nonneg ht n) ((stochastic_pow hK n).1 i i))
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one,
    Matrix.one_apply_eq] at h
  exact (Real.exp_pos (-t)).trans_le h

lemma heatOp_pos {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) {f : V → ℝ} (hf : ∀ i, 0 < f i) (i : V) :
    0 < LogSobolevMC.ChiSquare.heatOp K t f i := by
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg ((heat_stochastic hK ht).1 i j) (hf j).le
  · exact ⟨i, Finset.mem_univ i, mul_pos (heat_diagonal_pos hK ht i) (hf i)⟩

lemma heatOp_one {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) : LogSobolevMC.ChiSquare.heatOp K t (fun _ => 1) = fun _ => 1 := by
  funext i
  simpa only [LogSobolevMC.ChiSquare.heatOp, Matrix.mulVec, dotProduct, mul_one] using
    (heat_stochastic hK ht).2 i
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma complexHeat_real_kernel (R L : Matrix V V ℝ) (κ π : V → ℝ)
    (hRL : R * L = 1) (hLR : L * R = 1) (hrel : ∀ i x, L i x = π x * R x i)
    (s t : ℝ) (f : V → ℂ) (x : V) :
    complexHeat π (fun i x => R x i) (fun i => t * (κ i - 1)) (s : ℂ) f x =
      ∑ y, (MarkovMixing.heatKernel (R * Matrix.diagonal κ * L) (s*t) x y : ℂ) * f y := by
  simp only [complexHeat, weightedSynthesis, weightedFourier, Finset.mul_sum,
    heat_kernel_spectral R L κ hRL hLR, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  rw [hrel]
  push_cast
  ring

lemma heat_complex_domination {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (f : V → ℂ) (x : V) :
    ‖∑ y, (MarkovMixing.heatKernel K t x y : ℂ) * f y‖ ≤
      LogSobolevMC.ChiSquare.heatOp K t (fun y => ‖f y‖) x := by
  apply (norm_sum_le _ _).trans
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro y _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((heat_stochastic hK ht).1 x y)]

lemma complexLp_heat_bound {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hp : ∀ x, 0 ≤ π x)
    {t q M : ℝ} (ht : 0 ≤ t) (hq : 0 < q)
    (hb : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q
      (LogSobolevMC.ChiSquare.heatOp K t f) ≤ M * LogSobolevMC.ChiSquare.lpNorm π 2 f)
    (f : V → ℂ) :
    complexLp π q (fun x => ∑ y, (MarkovMixing.heatKernel K t x y : ℂ) * f y) ≤ M * complexLp π 2 f := by
  have hpos (x : V) : 0 ≤ LogSobolevMC.ChiSquare.heatOp K t (fun y => ‖f y‖) x :=
    Finset.sum_nonneg fun y _ => mul_nonneg ((heat_stochastic hK ht).1 x y) (norm_nonneg _)
  calc
    _ ≤ complexLp π q (fun x => (LogSobolevMC.ChiSquare.heatOp K t (fun y => ‖f y‖) x : ℂ)) := by
      apply complexLp_mono π hp hq
      intro x
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos x)] using
        heat_complex_domination hK ht f x
    _ ≤ _ := by
      rw [complexLp_real]
      have h := hb (fun y => ‖f y‖)
      simpa only [LogSobolevMC.ChiSquare.lpNorm, complexLp, abs_of_nonneg (norm_nonneg _), mul_comm] using h
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def symmetrized (K : Matrix V V ℝ) (π : V → ℝ) : Matrix V V ℝ :=
  fun i j => Real.sqrt (π i) * K i j / Real.sqrt (π j)

omit [Fintype V] [DecidableEq V] in
lemma symmetrized_symmetric {K : Matrix V V ℝ} {π : V → ℝ}
    (hp : ∀ i, 0 < π i) (hr : MarkovMixing.DetailedBalance K π) :
    (symmetrized K π).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, symmetrized]
  have hi := Real.sq_sqrt (hp i).le
  have hj := Real.sq_sqrt (hp j).le
  have h := hr i j
  apply (div_eq_div_iff (Real.sqrt_pos.2 (hp i)).ne' (Real.sqrt_pos.2 (hp j)).ne').2
  calc
    Real.sqrt (π j) * K j i * Real.sqrt (π j) = π j * K j i := by nlinarith [congrArg (fun x => x * K j i) hj]
    _ = π i * K i j := h.symm
    _ = Real.sqrt (π i) * K i j * Real.sqrt (π i) := by nlinarith [congrArg (fun x => x * K i j) hi]

noncomputable def weightedDiagonal (π : V → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (π i))
noncomputable def inverseWeightedDiagonal (π : V → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (π i))⁻¹)

lemma weighted_diagonal_inverse {π : V → ℝ} (hp : ∀ i, 0 < π i) :
    weightedDiagonal π * inverseWeightedDiagonal π = 1 := by
  simp only [weightedDiagonal, inverseWeightedDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, (Real.sqrt_pos.2 (hp i)).ne']

lemma inverse_weighted_diagonal {π : V → ℝ} (hp : ∀ i, 0 < π i) :
    inverseWeightedDiagonal π * weightedDiagonal π = 1 := by
  simp only [weightedDiagonal, inverseWeightedDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, (Real.sqrt_pos.2 (hp i)).ne']

lemma symmetrized_eq (K : Matrix V V ℝ) (π : V → ℝ) :
    symmetrized K π = weightedDiagonal π * K * inverseWeightedDiagonal π := by
  ext i j
  simp [symmetrized, weightedDiagonal, inverseWeightedDiagonal, Matrix.diagonal_mul,
    Matrix.mul_diagonal, div_eq_mul_inv]

lemma reconstruct_matrix (K : Matrix V V ℝ) {π : V → ℝ} (hp : ∀ i, 0 < π i) :
    K = inverseWeightedDiagonal π * symmetrized K π * weightedDiagonal π := by
  rw [symmetrized_eq]
  simp only [← Matrix.mul_assoc, inverse_weighted_diagonal hp, Matrix.one_mul]
  rw [Matrix.mul_assoc, inverse_weighted_diagonal hp, Matrix.mul_one]
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_weighted_spectrum (K : Matrix V V ℝ) {π : V → ℝ}
    (hp : ∀ i, 0 < π i) (hr : MarkovMixing.DetailedBalance K π) :
    ∃ (R L : Matrix V V ℝ) (κ : V → ℝ),
      R * L = 1 ∧ L * R = 1 ∧ K = R * Matrix.diagonal κ * L ∧
      ∀ i x, L i x = π x * R x i := by
  let h := symmetrized_symmetric hp hr
  let U : Matrix V V ℝ := h.eigenvectorUnitary
  have hUU : U * U.transpose = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self h.eigenvectorUnitary
  have hUU' : U.transpose * U = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self h.eigenvectorUnitary
  have hs : symmetrized K π = U * Matrix.diagonal h.eigenvalues * U.transpose := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.comp_def, id_eq] using h.spectral_theorem
  refine ⟨inverseWeightedDiagonal π * U, U.transpose * weightedDiagonal π,
    h.eigenvalues, ?_, ?_, ?_, ?_⟩
  · calc
      inverseWeightedDiagonal π * U * (U.transpose * weightedDiagonal π) =
          inverseWeightedDiagonal π * (U * U.transpose) * weightedDiagonal π := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, inverse_weighted_diagonal hp]
  · calc
      U.transpose * weightedDiagonal π * (inverseWeightedDiagonal π * U) =
          U.transpose * (weightedDiagonal π * inverseWeightedDiagonal π) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [weighted_diagonal_inverse hp, Matrix.mul_one, hUU']
  · calc
      K = inverseWeightedDiagonal π * symmetrized K π * weightedDiagonal π := reconstruct_matrix K hp
      _ = _ := by
        simpa only [Matrix.mul_assoc] using congrArg
          (fun A : Matrix V V ℝ => inverseWeightedDiagonal π * A * weightedDiagonal π) hs
  · intro i x
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, weightedDiagonal,
      inverseWeightedDiagonal, Matrix.transpose_apply]
    have hx := Real.sq_sqrt (hp x).le
    have hn := (Real.sqrt_pos.2 (hp x)).ne'
    field_simp
    nlinarith [congrArg (fun z => z * U x i) hx]
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma spectrum_orthogonal (R L : Matrix V V ℝ) (π : V → ℝ)
    (hLR : L * R = 1) (hrel : ∀ i x, L i x = π x * R x i) (i j : V) :
    ∑ x, π x * R x i * R x j = if i = j then 1 else 0 := by
  have h := congrFun (congrFun hLR i) j
  simpa only [Matrix.mul_apply, hrel, Matrix.one_apply] using h

lemma spectrum_complete (R L : Matrix V V ℝ) (π : V → ℝ)
    (hp : ∀ x, 0 < π x) (hRL : R * L = 1)
    (hrel : ∀ i x, L i x = π x * R x i) (x y : V) :
    ∑ i, R x i * R y i = if x = y then 1 / π x else 0 := by
  have h := congrFun (congrFun hRL x) y
  simp only [Matrix.mul_apply, hrel, Matrix.one_apply] at h
  have he : (∑ i, R x i * R y i) * π y = if x = y then 1 else 0 := by
    rw [Finset.sum_mul]
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  by_cases hxy : x = y
  · subst y
    have he1 : (∑ i, R x i * R x i) * π x = 1 := he.trans (if_pos rfl)
    simpa using (eq_div_iff (hp x).ne').2 he1
  · simp only [if_neg hxy] at he ⊢
    exact (mul_eq_zero.mp he).resolve_right (hp y).ne'
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh

lemma interpolation_a_bounds (q : ℝ) (hq : 2 < q) :
    0 < 1 - 2 / q ∧ 1 - 2 / q < 1 := by
  have hq0 : 0 < q := by linarith
  have hlt : 2 / q < 1 := (div_lt_one hq0).mpr hq
  have hpos : 0 < 2 / q := div_pos (by norm_num) hq0
  constructor <;> linarith

lemma interpolation_denominator (q θ : ℝ) (hq : 2 < q)
    (ht0 : 0 < θ) (ht1 : θ < 1) :
    0 < 1 - (1 - 2 / q) * θ ∧ 1 - (1 - 2 / q) * θ < 1 := by
  obtain ⟨ha0, ha1⟩ := interpolation_a_bounds q hq
  have hmul0 := mul_pos ha0 ht0
  have hmul1 := mul_lt_mul_of_pos_left ht1 ha0
  constructor <;> nlinarith

lemma interpolation_p_gt_two (q θ : ℝ) (hq : 2 < q)
    (ht0 : 0 < θ) (ht1 : θ < 1) : 2 < 2 / (1 - (1 - 2 / q) * θ) := by
  obtain ⟨hd0, hd1⟩ := interpolation_denominator q θ hq ht0 ht1
  apply (lt_div_iff₀ hd0).mpr
  linarith

lemma interpolation_holder_conjugates (q θ : ℝ) (hq : 2 < q)
    (ht0 : 0 < θ) (ht1 : θ < 1) :
    let p := 2 / (1 - (1 - 2 / q) * θ)
    p.HolderConjugate (p / (p - 1)) ∧ q.HolderConjugate (q / (q - 1)) := by
  dsimp only
  constructor
  · exact (Real.holderConjugate_iff_eq_conjExponent
      (by linarith [interpolation_p_gt_two q θ hq ht0 ht1])).mpr rfl
  · exact (Real.holderConjugate_iff_eq_conjExponent (by linarith : 1 < q)).mpr rfl

lemma interpolation_dual_identity (q θ : ℝ) (hq : 2 < q)
    (ht0 : 0 < θ) (ht1 : θ < 1) :
    let p := 2 / (1 - (1 - 2 / q) * θ)
    (p / (p - 1)) * ((1 - θ) / 2 + θ / (q / (q - 1))) = 1 := by
  let p := 2 / (1 - (1 - 2 / q) * θ)
  let r := p / (p - 1)
  have hpr : p.HolderConjugate r := (interpolation_holder_conjugates q θ hq ht0 ht1).1
  have hs : p⁻¹ + r⁻¹ = 1 := (Real.holderConjugate_iff.mp hpr).2
  have hq0 : q ≠ 0 := ne_of_gt (by linarith : 0 < q)
  have hb : (1 - θ) / 2 + θ / (q / (q - 1)) = 1 - p⁻¹ := by
    dsimp [p]
    rw [inv_div, div_div_eq_mul_div]
    field_simp [hq0]
    ring
  change r * ((1 - θ) / 2 + θ / (q / (q - 1))) = 1
  have he : (1 - θ) / 2 + θ / (q / (q - 1)) = r⁻¹ := by rw [hb]; linarith
  rw [he, mul_inv_cancel₀ hpr.symm.ne_zero]

lemma interpolation_p_at_zero (a : ℝ) : 2 / (1 - a * (0 : ℝ)) = 2 := by norm_num

lemma interpolation_p_deriv_zero (a : ℝ) :
    HasDerivAt (fun θ : ℝ => 2 / (1 - a * θ)) (2 * a) 0 := by
  have hd := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
    ((hasDerivAt_const (0 : ℝ) a).mul (hasDerivAt_id (0 : ℝ)))
  have h := (hasDerivAt_const (0 : ℝ) (2 : ℝ)).div hd (by norm_num)
  simpa [Pi.div_apply, Pi.sub_apply, Pi.mul_apply] using! h

end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma lpNorm_one {π : V → ℝ} (hs : ∑ i, π i = 1) (p : ℝ) :
    LogSobolevMC.ChiSquare.lpNorm π p (fun _ => 1) = 1 := by
  simp only [LogSobolevMC.ChiSquare.lpNorm, abs_one, Real.one_rpow, one_mul, hs]

lemma heat_bound_constant {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    {q t M : ℝ} (ht : 0 ≤ t)
    (hb : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q
      (LogSobolevMC.ChiSquare.heatOp K t f) ≤ M * LogSobolevMC.ChiSquare.lpNorm π 2 f) : 1 ≤ M := by
  have h := hb (fun _ => 1)
  simpa only [heatOp_one hK ht, lpNorm_one hs.1.2, mul_one] using h

omit [DecidableEq V] in
lemma lpNorm_le_supNorm [Nonempty V] {π : V → ℝ} (hp : ∀ i, 0 ≤ π i)
    (hs : ∑ i, π i = 1) {q : ℝ} (hq : 0 < q) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.lpNorm π q f ≤ LogSobolevMC.LowerBound.supNorm f := by
  have hbound (i : V) : |f i| ≤ LogSobolevMC.LowerBound.supNorm f :=
    le_ciSup (f := fun i => |f i|) (Finite.bddAbove_range _) i
  have hnonneg : 0 ≤ LogSobolevMC.LowerBound.supNorm f :=
    (abs_nonneg (f (Classical.choice inferInstance))).trans (hbound _)
  have hm : (∑ i, |f i| ^ q * π i) ≤ (LogSobolevMC.LowerBound.supNorm f)^q := by
    calc
      _ ≤ ∑ i, (LogSobolevMC.LowerBound.supNorm f)^q * π i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (hbound i) hq.le) (hp i)
      _ = _ := by rw [← Finset.mul_sum, hs, mul_one]
  calc
    _ ≤ ((LogSobolevMC.LowerBound.supNorm f)^q)^(1/q) :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hp i)) hm (by positivity)
    _ = _ := by rw [← Real.rpow_mul hnonneg, mul_one_div_cancel hq.ne', Real.rpow_one]
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma heat_interpolation_positive (K : Matrix V V ℝ) (π : V → ℝ)
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (hp : ∀ i, 0 < π i) (hrev : MarkovMixing.DetailedBalance K π)
    (q t M : ℝ) (hq : 2 < q) (ht : 0 < t)
    (hb : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q
      (LogSobolevMC.ChiSquare.heatOp K t f) ≤ M * LogSobolevMC.ChiSquare.lpNorm π 2 f)
    (f : V → ℝ) (hf : ∀ i, 0 < f i) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    LogSobolevMC.ChiSquare.lpNorm π (2/(1-(1-2/q)*θ))
      (LogSobolevMC.ChiSquare.heatOp K (θ*t) f) ≤
      M^θ * LogSobolevMC.ChiSquare.lpNorm π 2 f := by
  obtain ⟨R,L,κ,hRL,hLR,hmat,hrel⟩ := exists_weighted_spectrum K hp hrev
  let psi := fun i x => R x i
  let β := fun i => t*(κ i-1)
  let F := fun z => complexHeat π psi β z (fun i => (f i:ℂ))
  have hc := spectrum_complete R L π hp hRL hrel
  have ho := spectrum_orthogonal R L π hLR hrel
  let N := LogSobolevMC.ChiSquare.lpNorm π 2 f
  have hN : 0 < N := by
    apply Real.rpow_pos_of_pos
    exact Finset.sum_pos (fun i _ => mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (hf i).ne') _) (hp i)) Finset.univ_nonempty
  have hM : 1 ≤ M := heat_bound_constant hK hs ht.le hb
  have hleft (z : ℂ) (hz : z.re=0) : complexLp π 2 (F z) ≤ N := by
    change complexLp π 2 (complexHeat π psi β z (fun i => (f i:ℂ))) ≤ N
    rw [complexHeat_imaginary_isometry π hp psi hc ho β z hz, complexLp_real]
  have hright (z : ℂ) (hz : z.re=1) : complexLp π q (F z) ≤ M*N := by
    have hu : (z-1).re=0 := by simp [hz]
    have he : z=1+(z-1) := by ring
    change complexLp π q (complexHeat π psi β z (fun i => (f i:ℂ))) ≤ M*N
    rw [he, complexHeat_add π psi ho]
    have hk : (fun x => complexHeat π psi β 1 (complexHeat π psi β (z-1) (fun i => (f i:ℂ))) x) =
        (fun x => ∑ y, (MarkovMixing.heatKernel K t x y:ℂ) * complexHeat π psi β (z-1) (fun i => (f i:ℂ)) y) := by
      funext x
      simpa only [one_mul, Complex.ofReal_one, ← hmat] using
        complexHeat_real_kernel R L κ π hRL hLR hrel 1 t (complexHeat π psi β (z-1) (fun i => (f i:ℂ))) x
    change complexHeat π psi β 1 (complexHeat π psi β (z-1) (fun i => (f i:ℂ))) = _ at hk
    rw [hk]
    have hh := complexLp_heat_bound hK (fun i => (hp i).le) ht.le (by linarith : 0<q) hb
      (complexHeat π psi β (z-1) (fun i => (f i:ℂ)))
    simpa only [complexHeat_imaginary_isometry π hp psi hc ho β (z-1) hu, complexLp_real] using hh
  let u := LogSobolevMC.ChiSquare.heatOp K (θ*t) f
  have hu : ∀ i, 0 < u i := heatOp_pos hK (mul_pos hθ0 ht).le hf
  have hFu : ∀ i, F (θ:ℂ) i = (u i:ℂ) := by
    intro i
    have h := complexHeat_real_kernel R L κ π hRL hLR hrel θ t (fun i => (f i:ℂ)) i
    simpa only [F, psi, β, u, ← hmat, LogSobolevMC.ChiSquare.heatOp, Matrix.mulVec, dotProduct,
      Complex.ofReal_sum, Complex.ofReal_mul] using h
  let B := fun x => ∑ i, |psi i x| * Real.exp |β i| * ‖weightedFourier π psi (fun i => (f i:ℂ)) i‖
  have hB : ∀ x, 0 ≤ B x := fun x => Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨hpr,hqq⟩ := interpolation_holder_conjugates q θ hq hθ0 hθ1
  have hv := vector_interpolation π hp F
    (fun x => complexHeat_differentiable π psi β (fun i => (f i:ℂ)) x) B hB
    (fun z hz0 hz1 x => complexHeat_strip_bound π psi β (fun i => (f i:ℂ)) x hz0 hz1)
    hpr hqq hθ0 hθ1 (interpolation_dual_identity q θ hq hθ0 hθ1) hleft hright u hu hFu
  have hFn : complexLp π (2/(1-(1-2/q)*θ)) (F (θ:ℂ)) =
      LogSobolevMC.ChiSquare.lpNorm π (2/(1-(1-2/q)*θ)) u := by
    have he : F (θ:ℂ) = fun i => (u i:ℂ) := funext hFu
    rw [he, complexLp_real]
  rw [hFn] at hv
  calc
    _ ≤ N^(1-θ)*(M*N)^θ := hv
    _ = M^θ*N := by
      rw [Real.mul_rpow (by linarith : 0≤M) hN.le]
      calc
        N^(1-θ)*(M^θ*N^θ) = M^θ*(N^(1-θ)*N^θ) := by ring
        _ = _ := by rw [← Real.rpow_add hN]; simp
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma heatOp_spectral (R L : Matrix V V ℝ) (κ : V → ℝ)
    (hRL : R * L = 1) (hLR : L * R = 1) (t : ℝ) (f : V → ℝ) (x : V) :
    LogSobolevMC.ChiSquare.heatOp (R * Matrix.diagonal κ * L) t f x =
      ∑ a, R x a * Real.exp (t * (κ a - 1)) * L.mulVec f a := by
  simp only [LogSobolevMC.ChiSquare.heatOp, Matrix.mulVec, dotProduct,
    heat_kernel_spectral R L κ hRL hLR, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma spectral_generator (R L : Matrix V V ℝ) (κ : V → ℝ) (hRL : R * L = 1)
    (f : V → ℝ) (x : V) :
    ∑ a, R x a * (κ a - 1) * L.mulVec f a =
      (R * Matrix.diagonal κ * L).mulVec f x - f x := by
  have hi : (R * L).mulVec f x = f x := by rw [hRL, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec] at hi
  simp only [Matrix.mulVec, dotProduct] at hi
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hdiag : (Matrix.diagonal κ).mulVec (L.mulVec f) = fun a => κ a * L.mulVec f a :=
    funext fun a => Matrix.mulVec_diagonal κ (L.mulVec f) a
  rw [hdiag]
  simp only [Matrix.mulVec, dotProduct]
  calc
    _ = (∑ a, R x a * (κ a * ∑ j, L a j * f j)) -
        (∑ a, R x a * ∑ j, L a j * f j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hi]

lemma heatOp_deriv_zero (K : Matrix V V ℝ) {π : V → ℝ}
    (hp : ∀ i, 0 < π i) (hr : MarkovMixing.DetailedBalance K π)
    (t : ℝ) (f : V → ℝ) (x : V) :
    HasDerivAt (fun s : ℝ => LogSobolevMC.ChiSquare.heatOp K (s*t) f x)
      (t * (K.mulVec f x - f x)) 0 := by
  obtain ⟨R,L,κ,hRL,hLR,hK,_⟩ := exists_weighted_spectrum K hp hr
  have hterm (a : V) : HasDerivAt
      (fun s : ℝ => R x a * Real.exp ((s*t)*(κ a-1)) * L.mulVec f a)
      (R x a * (t*(κ a-1)) * L.mulVec f a) 0 := by
    have hh := ((((hasDerivAt_id (0:ℝ)).mul_const t).mul_const (κ a-1)).exp.const_mul (R x a)).mul_const (L.mulVec f a)
    simpa only [id_eq, one_mul, zero_mul, Real.exp_zero, mul_one] using hh
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a)
  have he : (∑ a, R x a * (t*(κ a-1)) * L.mulVec f a) = t*(K.mulVec f x-f x) := by
    rw [hK, ← spectral_generator R L κ hRL]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he] at hh
  have hf : (fun s : ℝ => ∑ a, R x a * Real.exp ((s*t)*(κ a-1)) * L.mulVec f a) =
      (fun s : ℝ => LogSobolevMC.ChiSquare.heatOp K (s*t) f x) := by
    funext s
    rw [hK, heatOp_spectral R L κ hRL hLR]
  rw [hf] at hh
  exact hh
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma heatKernel_zero (K : Matrix V V ℝ) : MarkovMixing.heatKernel K 0 = 1 := by
  ext i j
  unfold MarkovMixing.heatKernel
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]
lemma heatOp_zero (K : Matrix V V ℝ) (f : V → ℝ) : LogSobolevMC.ChiSquare.heatOp K 0 f = f := by
  rw [LogSobolevMC.ChiSquare.heatOp, heatKernel_zero, Matrix.one_mulVec]
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh

noncomputable section

variable {ι : Type*} [Fintype ι]

def positiveMoment (w f : ι → ℝ) (p : ℝ) : ℝ := ∑ i, w i * f i ^ p

theorem positiveMoment_pos [Nonempty ι] {w f : ι → ℝ} {p : ℝ}
    (hw : ∀ i, 0 < w i) (hf : ∀ i, 0 < f i) : 0 < positiveMoment w f p := by
  classical
  exact Finset.sum_pos (fun i _ => mul_pos (hw i) (Real.rpow_pos_of_pos (hf i) p))
    Finset.univ_nonempty

theorem positiveMoment_deriv (w : ι → ℝ) {f : ℝ → ι → ℝ} {v : ι → ℝ}
    {p : ℝ → ℝ} {p' t : ℝ}
    (hf : ∀ i, HasDerivAt (fun s => f s i) (v i) t)
    (hp : HasDerivAt p p' t) (hpos : ∀ i, 0 < f t i) :
    HasDerivAt (fun s => positiveMoment w (f s) (p s))
      (∑ i, w i * (v i * p t * f t i ^ (p t - 1) +
        p' * f t i ^ p t * Real.log (f t i))) t := by
  simpa only [positiveMoment] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => ((hf i).rpow hp (hpos i)).const_mul (w i)))

theorem positive_logNorm_deriv [Nonempty ι] (w : ι → ℝ)
    {f : ℝ → ι → ℝ} {v : ι → ℝ} {p : ℝ → ℝ} {p' t : ℝ}
    (hw : ∀ i, 0 < w i) (hf : ∀ i, HasDerivAt (fun s => f s i) (v i) t)
    (hp : HasDerivAt p p' t) (hpos : ∀ i, 0 < f t i) (hp0 : p t ≠ 0) :
    HasDerivAt (fun s => Real.log (positiveMoment w (f s) (p s)) / p s)
      (((∑ i, w i * (v i * p t * f t i ^ (p t - 1) +
        p' * f t i ^ p t * Real.log (f t i))) /
        positiveMoment w (f t) (p t) * p t -
        Real.log (positiveMoment w (f t) (p t)) * p') / (p t)^2) t := by
  exact ((positiveMoment_deriv w hf hp hpos).log
    (ne_of_gt (positiveMoment_pos hw hpos))).div hp hp0

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma lpNorm_eq_moment (w f : ι → ℝ) (p : ℝ) :
    ChiSquare.lpNorm w p f = (positiveMoment w (fun i => |f i|) p) ^ (1 / p) := by
  unfold ChiSquare.lpNorm positiveMoment
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma moment_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) (p : ℝ) :
    0 ≤ positiveMoment w (fun i => |f i|) p := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _))

lemma lpNorm_rpow {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ)
    {p : ℝ} (hp : p ≠ 0) :
    (ChiSquare.lpNorm w p f) ^ p = positiveMoment w (fun i => |f i|) p := by
  rw [lpNorm_eq_moment, ← Real.rpow_mul (moment_nonneg hw f p)]
  simp [hp]

lemma entLp_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ)
    {p : ℝ} (hp : p ≠ 0) :
    ChiSquare.entLp w p f =
      p * (∑ i, w i * |f i| ^ p * Real.log |f i|) -
      positiveMoment w (fun i => |f i|) p *
        Real.log (positiveMoment w (fun i => |f i|) p) := by
  classical
  rw [ChiSquare.entLp, lpNorm_rpow hw f hp]
  have hi (i : ι) : |f i| ^ p *
      Real.log (|f i| ^ p / positiveMoment w (fun i => |f i|) p) * w i =
      p * (w i * |f i| ^ p * Real.log |f i|) -
      w i * |f i| ^ p * Real.log (positiveMoment w (fun i => |f i|) p) := by
    by_cases hf : f i = 0
    · simp [hf, Real.zero_rpow hp]
    · by_cases hwi : w i = 0
      · simp [hwi]
      · have hS : 0 < positiveMoment w (fun j => |f j|) p := by
          apply Finset.sum_pos' (fun j _ => mul_nonneg (hw j)
            (Real.rpow_nonneg (abs_nonneg _) _))
          exact ⟨i, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hwi))
            (Real.rpow_pos_of_pos (abs_pos.mpr hf) p)⟩
        rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr hf) p))
          (ne_of_gt hS), Real.log_rpow (abs_pos.mpr hf)]
        ring
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

lemma entL_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) :
    ChiSquare.entL w f =
      2 * (∑ i, w i * |f i| ^ (2:ℝ) * Real.log |f i|) -
      positiveMoment w (fun i => |f i|) 2 *
        Real.log (positiveMoment w (fun i => |f i|) 2) := by
  exact entLp_expansion hw f (by norm_num)

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
open Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma log_lpNorm_positive {w f : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hf : ∀ i, 0 < f i) (p : ℝ) :
    Real.log (ChiSquare.lpNorm w p f) = Real.log (positiveMoment w f p) / p := by
  rw [lpNorm_eq_moment]
  simp_rw [abs_of_pos (hf _)]
  rw [Real.log_rpow (positiveMoment_pos hw hf)]
  ring

theorem native_logNorm_deriv (w : ι → ℝ)
    {f : ℝ → ι → ℝ} {v : ι → ℝ} {p : ℝ → ℝ} {p' t : ℝ}
    (hw : ∀ i, 0 < w i) (hf : ∀ i, HasDerivAt (fun s => f s i) (v i) t)
    (hp : HasDerivAt p p' t) (hpos : ∀ i, 0 < f t i) (hp0 : p t ≠ 0) :
    HasDerivAt (fun s => Real.log (ChiSquare.lpNorm w (p s) (f s)))
      (((∑ i, w i * (v i * p t * f t i ^ (p t - 1) +
        p' * f t i ^ p t * Real.log (f t i))) /
        positiveMoment w (f t) (p t) * p t -
        Real.log (positiveMoment w (f t) (p t)) * p') / (p t)^2) t := by
  apply (positive_logNorm_deriv w hw hf hp hpos hp0).congr_of_eventuallyEq
  have he : ∀ᶠ s in 𝓝 t, ∀ i, 0 < f s i := by
    rw [Filter.eventually_all]
    intro i
    exact (hf i).continuousAt.eventually (lt_mem_nhds (hpos i))
  filter_upwards [he] with s hs
  exact log_lpNorm_positive hw hs (p s)

theorem native_logNorm_deriv_two (w : ι → ℝ)
    {f : ℝ → ι → ℝ} {v : ι → ℝ} {p : ℝ → ℝ} {p' t : ℝ}
    (hw : ∀ i, 0 < w i) (hf : ∀ i, HasDerivAt (fun s => f s i) (v i) t)
    (hp : HasDerivAt p p' t) (hpos : ∀ i, 0 < f t i) (hp2 : p t = 2) :
    HasDerivAt (fun s => Real.log (ChiSquare.lpNorm w (p s) (f s)))
      (p' / 4 * ChiSquare.entL w (f t) / positiveMoment w (f t) 2 +
        (∑ i, w i * f t i * v i) / positiveMoment w (f t) 2) t := by
  have hh := native_logNorm_deriv w hw hf hp hpos (by rw [hp2]; norm_num)
  rw [hp2] at hh
  have hE := entL_expansion (fun i => (hw i).le) (f t)
  simp_rw [abs_of_pos (hpos _)] at hE
  have hsum : (∑ i, w i * (v i * 2 * f t i ^ (2 - 1 : ℝ) +
      p' * f t i ^ (2:ℝ) * Real.log (f t i))) =
      2 * (∑ i, w i * f t i * v i) +
      p' * (∑ i, w i * f t i ^ (2:ℝ) * Real.log (f t i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    norm_num
    ring
  rw [hsum] at hh
  convert hh using 1
  rw [hE]
  field_simp [ne_of_gt (positiveMoment_pos hw hpos (p := 2))]
  ring

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
open Filter
open scoped Topology

lemma right_derivative_comparison {f g : ℝ → ℝ} {f' g' a : ℝ}
    (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a)
    (he : f a = g a) (hle : ∀ᶠ x in 𝓝[>] a, f x ≤ g x) : f' ≤ g' := by
  have hfl := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have hgl := (hasDerivAt_iff_tendsto_slope_left_right.mp hg).2
  apply le_of_tendsto_of_tendsto hfl hgl
  filter_upwards [hle, self_mem_nhdsWithin] with x hx hxa
  change a < x at hxa
  simp only [slope, smul_eq_mul, vsub_eq_sub, he]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hx _) (inv_nonneg.mpr (sub_pos.mpr hxa).le)

end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators Topology
open Filter
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma defective_positive (K : Matrix V V ℝ) (π : V → ℝ)
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (hp : ∀ i, 0 < π i) (hr : MarkovMixing.DetailedBalance K π)
    (q t M : ℝ) (hq : 2 < q) (ht : 0 < t)
    (hb : ∀ f : V → ℝ, ChiSquare.lpNorm π q (ChiSquare.heatOp K t f) ≤ M*ChiSquare.lpNorm π 2 f)
    (f : V → ℝ) (hf : ∀ i, 0 < f i) :
    ChiSquare.entL π f ≤ (2*t/(1-2/q))*ChiSquare.dirichlet K π f f +
      (2*Real.log M/(1-2/q))*(ChiSquare.lpNorm π 2 f)^(2:ℝ) := by
  let a := 1-2/q
  have ha : 0 < a := (interpolation_a_bounds q hq).1
  let S := positiveMoment π f 2
  have hS : 0 < S := positiveMoment_pos hp hf
  let N := ChiSquare.lpNorm π 2 f
  have hN : 0 < N := by
    change 0 < ChiSquare.lpNorm π 2 f
    rw [lpNorm_eq_moment]
    simp_rw [abs_of_pos (hf _)]
    exact Real.rpow_pos_of_pos hS _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (heat_bound_constant hK hs ht.le hb)
  have hd := native_logNorm_deriv_two π hp (fun i => heatOp_deriv_zero K hp hr t f i)
    (interpolation_p_deriv_zero a) (by simpa only [zero_mul, heatOp_zero] using hf)
    (interpolation_p_at_zero a)
  simp only [zero_mul, heatOp_zero] at hd
  have he : (∑ i, π i * f i * (t*(K.mulVec f i-f i))) = -t*ChiSquare.dirichlet K π f f := by
    simp only [ChiSquare.dirichlet, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hd
  have hg : HasDerivAt (fun s : ℝ => s*Real.log M + Real.log N) (Real.log M) 0 := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (Real.log M)).add_const (Real.log N)
  have heq : Real.log (ChiSquare.lpNorm π (2/(1-a*0)) (ChiSquare.heatOp K (0*t) f)) =
      (0:ℝ)*Real.log M+Real.log N := by simp [N, heatOp_zero]
  have hle : ∀ᶠ s in 𝓝[>] (0:ℝ),
      Real.log (ChiSquare.lpNorm π (2/(1-a*s)) (ChiSquare.heatOp K (s*t) f)) ≤
      s*Real.log M+Real.log N := by
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with s hs0 hs1
    have hh := heat_interpolation_positive K π hK hs hp hr q t M hq ht hb f hf s hs0 hs1
    have hup : ∀ i, 0 < ChiSquare.heatOp K (s*t) f i := heatOp_pos hK (mul_pos hs0 ht).le hf
    have hn : 0 < ChiSquare.lpNorm π (2/(1-a*s)) (ChiSquare.heatOp K (s*t) f) := by
      rw [lpNorm_eq_moment]
      simp_rw [abs_of_pos (hup _)]
      exact Real.rpow_pos_of_pos (positiveMoment_pos hp hup) _
    have hhlog := Real.log_le_log hn hh
    rw [Real.log_mul (Real.rpow_pos_of_pos hM _).ne' hN.ne', Real.log_rpow hM] at hhlog
    exact hhlog
  have hh := right_derivative_comparison hd hg heq hle
  have hh' : (a/2*ChiSquare.entL π f-t*ChiSquare.dirichlet K π f f)/S ≤ Real.log M := by
    convert hh using 1
    ring
  have hmul := (div_le_iff₀ hS).mp hh'
  have hnorm : (ChiSquare.lpNorm π 2 f)^(2:ℝ) = S := by
    rw [lpNorm_rpow (fun i => (hp i).le) f (by norm_num)]
    simp only [S, abs_of_pos (hf _)]
  rw [hnorm]
  have he : ((2*t/a)*ChiSquare.dirichlet K π f f+(2*Real.log M/a)*S)*a =
      2*t*ChiSquare.dirichlet K π f f+2*Real.log M*S := by field_simp
  nlinarith
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma entropy_square_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) :
    ChiSquare.entL w f =
      (∑ i, w i*((f i)^2*Real.log ((f i)^2))) -
      (∑ i, w i*(f i)^2)*Real.log (∑ i, w i*(f i)^2) := by
  rw [entL_expansion hw]
  have hi (i : ι) : 2*(w i*|f i|^(2:ℝ)*Real.log |f i|) =
      w i*((f i)^2*Real.log ((f i)^2)) := by
    by_cases hf : f i = 0
    · simp [hf]
    · have hl := Real.log_rpow (abs_pos.mpr hf) (2:ℝ)
      rw [Real.rpow_two, sq_abs] at hl
      rw [Real.rpow_two, sq_abs, hl]
      ring
  rw [Finset.mul_sum]
  simp_rw [hi]
  simp only [positiveMoment, Real.rpow_two, sq_abs]

lemma continuous_entL {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Continuous (fun f : ι → ℝ => ChiSquare.entL w f) := by
  simp_rw [entropy_square_expansion hw]
  apply Continuous.sub
  · apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (Real.continuous_mul_log.comp ((continuous_apply i).pow 2))
  · apply Real.continuous_mul_log.comp
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul ((continuous_apply i).pow 2)

lemma continuous_lpNorm_two (w : ι → ℝ) :
    Continuous (fun f : ι → ℝ => ChiSquare.lpNorm w 2 f) := by
  unfold ChiSquare.lpNorm
  apply Continuous.rpow_const _ (fun _ => Or.inr (by norm_num : 0 ≤ (1:ℝ)/2))
  apply continuous_finsetSum
  intro i _
  rw [show (fun f : ι → ℝ => |f i|^(2:ℝ)*w i) =
      (fun f => (f i)^2*w i) by funext f; rw [Real.rpow_two, sq_abs]]
  exact ((continuous_apply i).pow 2).mul continuous_const

end
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped BigOperators
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V]

lemma stationary_column {K : Matrix V V ℝ} {π : V → ℝ}
    (hs : MarkovMixing.IsStationary K π) (j : V) : ∑ i, π i * K i j = π j := by
  exact congrFun hs.2 j

lemma dirichlet_edge_square {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (f : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π f f =
      (1 / 2 : ℝ) * ∑ i, ∑ j, π i * K i j * (f i - f j)^2 := by
  have hrow : ∑ i, ∑ j, π i * K i j * f i ^ 2 = ∑ i, π i * f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = π i * f i ^ 2 * ∑ j, K i j := by rw [Finset.mul_sum]; congr 1; funext j; ring
      _ = _ := by rw [hK.2 i, mul_one]
  have hcol : ∑ i, ∑ j, π i * K i j * f j ^ 2 = ∑ j, π j * f j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, stationary_column hs j]
  have hcross : ∑ i, ∑ j, π i * K i j * (f i * f j) =
      ∑ i, π i * f i * K.mulVec f i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : (∑ i, ∑ j, π i * K i j * (f i - f j)^2) =
      (∑ i, ∑ j, π i * K i j * f i^2) +
      (∑ i, ∑ j, π i * K i j * f j^2) -
      2 * (∑ i, ∑ j, π i * K i j * (f i * f j)) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, hrow, hcol, hcross]
  simp only [LogSobolevMC.ChiSquare.dirichlet, sub_mul, Finset.sum_sub_distrib]
  have h₁ : (∑ x, f x * f x * π x) = ∑ x, π x * f x ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h₂ : (∑ x, K.mulVec f x * f x * π x) = ∑ x, π x * f x * K.mulVec f x := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h₁, h₂]
  ring

lemma dirichlet_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (f : V → ℝ) : 0 ≤ LogSobolevMC.ChiSquare.dirichlet K π f f := by
  rw [dirichlet_edge_square hK hs]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hs.1.1 i) (hK.1 i j)) (sq_nonneg _))

lemma dirichlet_center {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (f : V → ℝ) (a : ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π (fun i => f i - a) (fun i => f i - a) =
      LogSobolevMC.ChiSquare.dirichlet K π f f := by
  simp only [dirichlet_edge_square hK hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  ring

lemma dirichlet_abs_le {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (f : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π (fun i => |f i|) (fun i => |f i|) ≤
      LogSobolevMC.ChiSquare.dirichlet K π f f := by
  rw [dirichlet_edge_square hK hs, dirichlet_edge_square hK hs]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hs.1.1 i) (hK.1 i j))
  have h := abs_abs_sub_abs_le (f i) (f j)
  have hp := mul_self_le_mul_self (abs_nonneg (|f i| - |f j|)) h
  nlinarith [sq_abs (|f i| - |f j|), sq_abs (f i - f j)]
end LogSobolevMC.LowerBound.Fresh
end

section

open scoped Topology
open Filter
namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma defective_lsi (K : Matrix V V ℝ) (π : V → ℝ)
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (hp : ∀ i, 0 < π i) (hr : MarkovMixing.DetailedBalance K π)
    (q t M : ℝ) (hq : 2 < q) (ht : 0 < t)
    (hb : ∀ f : V → ℝ, ChiSquare.lpNorm π q (ChiSquare.heatOp K t f) ≤ M*ChiSquare.lpNorm π 2 f)
    (f : V → ℝ) :
    ChiSquare.entL π f ≤ (2*t/(1-2/q))*ChiSquare.dirichlet K π f f +
      (2*Real.log M/(1-2/q))*(ChiSquare.lpNorm π 2 f)^(2:ℝ) := by
  let u : ℝ → V → ℝ := fun ε i => |f i|+ε
  have hu : Continuous u := continuous_pi fun i => continuous_const.add continuous_id
  have hl := ((continuous_entL (fun i => (hp i).le)).comp hu).tendsto (0:ℝ)
  have hn := ((continuous_lpNorm_two π).comp hu).tendsto (0:ℝ)
  have hL : Tendsto (fun ε => ChiSquare.entL π (u ε)) (𝓝[>] (0:ℝ)) (𝓝 (ChiSquare.entL π f)) := by
    apply (show Tendsto (fun ε => ChiSquare.entL π (u ε)) (𝓝 (0:ℝ)) (𝓝 (ChiSquare.entL π f)) from ?_).mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_def, u, add_zero, ChiSquare.entL, ChiSquare.lpNorm, abs_abs] using hl
  have hN : Tendsto (fun ε => ChiSquare.lpNorm π 2 (u ε)) (𝓝[>] (0:ℝ)) (𝓝 (ChiSquare.lpNorm π 2 f)) := by
    apply (show Tendsto (fun ε => ChiSquare.lpNorm π 2 (u ε)) (𝓝 (0:ℝ)) (𝓝 (ChiSquare.lpNorm π 2 f)) from ?_).mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_def, u, add_zero, ChiSquare.lpNorm, abs_abs] using hn
  have hR := ((hN.rpow_const (p := (2:ℝ)) (Or.inr (by norm_num))).const_mul (2*Real.log M/(1-2/q))).const_add ((2*t/(1-2/q))*ChiSquare.dirichlet K π f f)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hh := defective_positive K π hK hs hp hr q t M hq ht hb (u ε)
    (fun i => add_pos_of_nonneg_of_pos (abs_nonneg _) hε0)
  have he : ChiSquare.dirichlet K π (u ε) (u ε) =
      ChiSquare.dirichlet K π (fun i => |f i|) (fun i => |f i|) := by
    simpa only [sub_neg_eq_add] using dirichlet_center hK hs (fun i => |f i|) (-ε)
  rw [he] at hh
  apply hh.trans
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left (dirichlet_abs_le hK hs f)
    (div_nonneg (mul_nonneg (by norm_num) ht.le) (interpolation_a_bounds q hq).1.le)
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh

lemma xlog_ratio_lower (a S : ℝ) (ha : 0 ≤ a) (hS : 0 < S) :
    a - S ≤ a * Real.log (a / S) := by
  obtain rfl | ha := ha.eq_or_lt
  · simp only [zero_div, Real.log_zero, zero_mul, zero_sub]
    linarith
  · have h := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos ha hS)) ha.le
    have heq : a * (1 - (a / S)⁻¹) = a - S := by
      field_simp [ha.ne', hS.ne']
    rwa [heq] at h

lemma finite_entropy_nonneg {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, w i = 1) :
    0 ≤ ∑ i, a i * Real.log (a i / (∑ j, a j * w j)) * w i := by
  let S := ∑ i, a i * w i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hw i))
  change 0 ≤ ∑ i, a i * Real.log (a i / S) * w i
  obtain hzero | hpos := hS.eq_or_lt
  · rw [← hzero]
    simp
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (xlog_ratio_lower (a i) S (ha i) hpos) (hw i))
    have hc : (∑ i, (a i - S) * w i) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
      change S - S = 0
      ring
    rwa [hc] at h

lemma native_entropy_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hp : ∀ x, 0 ≤ π x) (hs : ∑ x, π x = 1) (f : V → ℝ) :
    0 ≤ ChiSquare.entL π f := by
  unfold ChiSquare.entL
  rw [lpNorm_rpow hp f (by norm_num : (2 : ℝ) ≠ 0)]
  unfold positiveMoment
  have h := finite_entropy_nonneg π (fun x => |f x| ^ (2 : ℝ)) hp
    (fun x => Real.rpow_nonneg (abs_nonneg _) _) hs
  simpa only [mul_comm] using h

end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh

lemma real_sInf_nonneg {S : Set ℝ} (hS : ∀ r ∈ S, 0 ≤ r) : 0 ≤ sInf S := by
  by_cases hn : S.Nonempty
  · exact le_csInf hn hS
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    simp

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma native_variance_nonneg (π : V → ℝ) (hp : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    0 ≤ MarkovMixing.distVar π f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (hp x))

omit [DecidableEq V] in
lemma native_gap_nonneg (K : Matrix V V ℝ) (π : V → ℝ)
    (hp : ∀ x, 0 ≤ π x)
    (hE : ∀ f, 0 ≤ ChiSquare.dirichlet K π f f) : 0 ≤ ChiSquare.gap K π := by
  apply real_sInf_nonneg
  rintro r ⟨f, _, rfl⟩
  exact div_nonneg (hE f) (native_variance_nonneg π hp f)

lemma native_logSobolev_nonneg (K : Matrix V V ℝ) (π : V → ℝ)
    (hp : ∀ x, 0 ≤ π x) (hs : ∑ x, π x = 1)
    (hE : ∀ f, 0 ≤ ChiSquare.dirichlet K π f f) : 0 ≤ ChiSquare.logSobolev K π := by
  apply real_sInf_nonneg
  rintro r ⟨f, _, rfl⟩
  exact div_nonneg (hE f) (native_entropy_nonneg π hp hs f)

omit [DecidableEq V] in
lemma native_poincare (K : Matrix V V ℝ) (π : V → ℝ)
    (hp : ∀ x, 0 ≤ π x) (hE : ∀ f, 0 ≤ ChiSquare.dirichlet K π f f)
    (f : V → ℝ) :
    ChiSquare.gap K π * MarkovMixing.distVar π f ≤ ChiSquare.dirichlet K π f f := by
  by_cases hv : MarkovMixing.distVar π f = 0
  · simpa only [hv, mul_zero] using hE f
  · have hb : BddBelow {r : ℝ | ∃ g : V → ℝ,
        MarkovMixing.distVar π g ≠ 0 ∧ r = ChiSquare.dirichlet K π g g / MarkovMixing.distVar π g} := by
      refine ⟨0, ?_⟩
      rintro r ⟨g, _, rfl⟩
      exact div_nonneg (hE g) (native_variance_nonneg π hp g)
    have h := csInf_le hb (show ChiSquare.dirichlet K π f f / MarkovMixing.distVar π f ∈
        {r : ℝ | ∃ g : V → ℝ, MarkovMixing.distVar π g ≠ 0 ∧
          r = ChiSquare.dirichlet K π g g / MarkovMixing.distVar π g} from ⟨f, hv, rfl⟩)
    have hm := mul_le_mul_of_nonneg_right h (native_variance_nonneg π hp f)
    rw [div_mul_cancel₀ _ hv] at hm
    exact hm

lemma native_logSobolev_lower (K : Matrix V V ℝ) (π : V → ℝ)
    (hp : ∀ x, 0 ≤ π x) (hs : ∑ x, π x = 1)
    (hne : ∃ f : V → ℝ, ChiSquare.entL π f ≠ 0) (c : ℝ)
    (hb : ∀ f, c * ChiSquare.entL π f ≤ ChiSquare.dirichlet K π f f) :
    c ≤ ChiSquare.logSobolev K π := by
  apply le_csInf
  · obtain ⟨f, hf⟩ := hne
    exact ⟨_, f, hf, rfl⟩
  · rintro r ⟨f, hf, rfl⟩
    have hpos := lt_of_le_of_ne (native_entropy_nonneg π hp hs f) (Ne.symm hf)
    exact (le_div_iff₀ hpos).mpr (hb f)

end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma native_gap_subsingleton [Subsingleton V] (K : Matrix V V ℝ) (π : V → ℝ)
    (hs : ∑ x, π x = 1) : ChiSquare.gap K π = 0 := by
  have hv : ∀ f : V → ℝ, MarkovMixing.distVar π f = 0 := by
    intro f
    have hm : ∀ x, MarkovMixing.distExp π f = f x := by
      intro x
      unfold MarkovMixing.distExp
      calc
        _ = ∑ y, f x * π y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Subsingleton.elim y x]
        _ = f x := by rw [← Finset.mul_sum, hs, mul_one]
    have hz : ∀ x, f x - MarkovMixing.distExp π f = 0 := by
      intro x
      rw [hm x, sub_self]
    simp [MarkovMixing.distVar, hz]
  unfold ChiSquare.gap
  have he : {r : ℝ | ∃ f : V → ℝ, MarkovMixing.distVar π f ≠ 0 ∧
      r = ChiSquare.dirichlet K π f f / MarkovMixing.distVar π f} = ∅ := by
    ext r
    simp [hv]
  rw [he]
  simp

omit [DecidableEq V] in
lemma native_gap_pos_nontrivial (K : Matrix V V ℝ) (π : V → ℝ)
    (hs : ∑ x, π x = 1) (hg : 0 < ChiSquare.gap K π) : Nontrivial V := by
  by_contra hn
  let _ : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
  rw [native_gap_subsingleton K π hs] at hg
  exact lt_irrefl 0 hg

lemma native_indicator_entropy (π : V → ℝ) (hp : ∀ x, 0 ≤ π x) (x : V) :
    ChiSquare.entL π (fun y => if y = x then 1 else 0) =
      π x * Real.log (1 / π x) := by
  unfold ChiSquare.entL
  rw [lpNorm_rpow hp _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp [positiveMoment, mul_comm]

lemma native_entropy_witness [Nontrivial V] (π : V → ℝ)
    (hp : ∀ x, 0 < π x) (hs : ∑ x, π x = 1) :
    ∃ f : V → ℝ, ChiSquare.entL π f ≠ 0 := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  have hpair : π x + π y ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({x, y} : Finset V) ⊆ Finset.univ from Finset.subset_univ _)
      (fun z _ _ => (hp z).le)
    simpa [hxy, hs] using h
  have hxlt : π x < 1 := by linarith [hp y]
  have hlog : 0 < Real.log (1 / π x) := by
    apply Real.log_pos
    exact (one_lt_div (hp x)).mpr hxlt
  refine ⟨fun z => if z = x then 1 else 0, ?_⟩
  rw [native_indicator_entropy π (fun z => (hp z).le) x]
  exact (mul_pos (hp x) hlog).ne'

end LogSobolevMC.LowerBound.Fresh
end

section

open Filter Topology
namespace LogSobolevMC.LowerBound.Fresh

lemma entropy_coefficient_conversion (lam t M a E V H : ℝ)
    (hlam : 0 < lam) (ht : 0 < t) (hM : 1 ≤ M) (ha : 0 < a)
    (hent : H ≤ (2 * t / a) * E + (2 * Real.log M / a + 2) * V)
    (hgap : lam * V ≤ E) :
    (a * lam / (2 * (lam * t + Real.log M + a))) * H ≤ E := by
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM
  have hden : 0 < 2 * (lam * t + Real.log M + a) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hent (le_of_lt (mul_pos ha hlam))
  have heq : a * lam * ((2 * t / a) * E + (2 * Real.log M / a + 2) * V) =
      2 * lam * t * E + (2 * Real.log M + 2 * a) * (lam * V) := by
    field_simp [ha.ne']
  rw [heq] at hmul
  have hgap' := mul_le_mul_of_nonneg_left hgap
    (by positivity : 0 ≤ 2 * Real.log M + 2 * a)
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

lemma finite_q_bound_implies_infinity (lam t M alpha : ℝ)
    (hlam : 0 ≤ lam) (ht : 0 < t) (hM : 1 ≤ M)
    (hfinite : ∀ q : ℝ, 2 < q →
      (1 - 2 / q) * lam / (2 * (lam * t + Real.log M + (q - 2) / q)) ≤ alpha) :
    lam / (2 * (lam * t + Real.log M + 1)) ≤ alpha := by
  have hdiv : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 3)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 3).2 (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  have ha : Tendsto (fun n : ℕ => 1 - 2 / ((n : ℝ) + 3)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hdiv
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM
  have hden : 2 * (lam * t + Real.log M + 1) ≠ 0 := by positivity
  have hlim : Tendsto (fun n : ℕ =>
      (1 - 2 / ((n : ℝ) + 3)) * lam /
        (2 * (lam * t + Real.log M + (1 - 2 / ((n : ℝ) + 3)))))
      atTop (𝓝 (lam / (2 * (lam * t + Real.log M + 1)))) := by
    simpa only [Pi.div_apply, one_mul] using! (ha.mul_const lam).div
      (tendsto_const_nhds.mul (tendsto_const_nhds.add ha)) hden
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  have hq : 2 < (n : ℝ) + 3 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have heq : ((n : ℝ) + 3 - 2) / ((n : ℝ) + 3) =
      1 - 2 / ((n : ℝ) + 3) := by
    have hq0 : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hq0]
  simpa only [heq] using hfinite ((n : ℝ) + 3) hq

end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma centered_lpNorm_square (π : V → ℝ) (hp : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    (ChiSquare.lpNorm π 2 (fun x => f x - MarkovMixing.distExp π f)) ^ (2 : ℝ) =
      MarkovMixing.distVar π f := by
  rw [lpNorm_rpow hp _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [positiveMoment, MarkovMixing.distVar, Real.rpow_two, sq_abs, mul_comm]

lemma native_lower_from_defective {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hs : MarkovMixing.IsStationary K π)
    (hp : ∀ x, 0 < π x) (q t M : ℝ) (hq : 2 < q) (ht : 0 < t) (hM : 1 ≤ M)
    (hdef : ∀ f : V → ℝ,
      ChiSquare.entL π f ≤ (2 * t / (1 - 2 / q)) * ChiSquare.dirichlet K π f f +
        (2 * Real.log M / (1 - 2 / q)) * (ChiSquare.lpNorm π 2 f) ^ (2 : ℝ))
    (hroth : ∀ f : V → ℝ,
      ChiSquare.entL π f ≤ ChiSquare.entL π (fun x => f x - MarkovMixing.distExp π f) +
        2 * MarkovMixing.distVar π f) :
    (1 - 2 / q) * ChiSquare.gap K π /
      (2 * (ChiSquare.gap K π * t + Real.log M + (q - 2) / q)) ≤
        ChiSquare.logSobolev K π := by
  have hE := dirichlet_nonneg hK hs
  have hpn : ∀ x, 0 ≤ π x := fun x => (hp x).le
  have ha : 0 < 1 - 2 / q := by
    have hq0 : 0 < q := by linarith
    have hlt : 2 / q < 1 := (div_lt_one hq0).mpr hq
    linarith
  have heq : (q - 2) / q = 1 - 2 / q := by
    have hq0 : q ≠ 0 := ne_of_gt (by linarith : 0 < q)
    field_simp [hq0]
  rw [heq]
  by_cases hg : ChiSquare.gap K π = 0
  · simpa only [hg, mul_zero, zero_mul, zero_div] using
      native_logSobolev_nonneg K π hpn hs.1.2 hE
  · have hgp : 0 < ChiSquare.gap K π :=
      lt_of_le_of_ne (native_gap_nonneg K π hpn hE) (Ne.symm hg)
    let _ : Nontrivial V := native_gap_pos_nontrivial K π hs.1.2 hgp
    apply native_logSobolev_lower K π hpn hs.1.2 (native_entropy_witness π hp hs.1.2)
    intro f
    have hd := hdef (fun x => f x - MarkovMixing.distExp π f)
    rw [dirichlet_center hK hs, centered_lpNorm_square π hpn] at hd
    have hh : ChiSquare.entL π f ≤
        (2 * t / (1 - 2 / q)) * ChiSquare.dirichlet K π f f +
        (2 * Real.log M / (1 - 2 / q) + 2) * MarkovMixing.distVar π f := by
      nlinarith [hroth f]
    exact entropy_coefficient_conversion _ _ _ _ _ _ _ hgp ht hM ha hh
      (native_poincare K π hpn hE f)

end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section

def regBase (a g ε t : ℝ) : ℝ := (a + t*g)^2 + ε

def regFirst (a g ε p t : ℝ) : ℝ :=
  p*g*(a+t*g)*(regBase a g ε t)^(p/2-1)

def regSecond (a g ε p t : ℝ) : ℝ :=
  p*g^2*(regBase a g ε t)^(p/2-1) +
  p*(p-2)*g^2*(a+t*g)^2*(regBase a g ε t)^(p/2-2)

lemma regBase_pos (a g t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < regBase a g ε t := by
  unfold regBase
  positivity

lemma regBase_deriv (a g ε t : ℝ) :
    HasDerivAt (regBase a g ε) (2*(a+t*g)*g) t := by
  have hh := ((((hasDerivAt_id t).mul_const g).const_add a).fun_pow 2).add_const ε
  simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul] using! hh

lemma reg_power_deriv (a g p t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasDerivAt (fun s => (regBase a g ε s)^(p/2)) (regFirst a g ε p t) t := by
  convert (regBase_deriv a g ε t).rpow_const
    (Or.inl (ne_of_gt (regBase_pos a g t hε))) using 1
  unfold regFirst
  ring

lemma reg_first_deriv (a g p t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasDerivAt (regFirst a g ε p) (regSecond a g ε p t) t := by
  have hh := (((hasDerivAt_id t).mul_const g).const_add a).const_mul (p*g)
  have hu := (regBase_deriv a g ε t).rpow_const
    (p := p/2-1) (Or.inl (ne_of_gt (regBase_pos a g t hε)))
  have hd := hh.mul hu
  have he : regSecond a g ε p t =
      p*g*(1*g)*(regBase a g ε t)^(p/2-1) +
      p*g*(a+id t*g)*(2*(a+t*g)*g*(p/2-1)*(regBase a g ε t)^(p/2-1-1)) := by
    unfold regSecond
    simp only [id_eq]
    rw [show p/2-1-1=p/2-2 by ring]
    ring
  rw [← he] at hd
  exact hd

lemma regSecond_le (a g t : ℝ) {ε p : ℝ} (hε : 0 < ε) (hp : 2 < p) :
    regSecond a g ε p t ≤
      p*(p-1)*g^2*(regBase a g ε t)^((p-2)/2) := by
  have hu := regBase_pos a g t hε
  have hpow : regBase a g ε t * (regBase a g ε t)^(p/2-2) =
      (regBase a g ε t)^(p/2-1) := by
    calc
      _ = (regBase a g ε t)^(1:ℝ) * (regBase a g ε t)^(p/2-2) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hu]
        congr 1
        ring
  have hbase : (a+t*g)^2 ≤ regBase a g ε t := by
    unfold regBase
    linarith
  have h := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ p*(p-2)*g^2*(regBase a g ε t)^(p/2-2) by positivity)
  have hmul : p*(p-2)*g^2*(regBase a g ε t)^(p/2-2)*regBase a g ε t =
      p*(p-2)*g^2*(regBase a g ε t)^(p/2-1) := by
    calc
      _ = p*(p-2)*g^2*(regBase a g ε t*(regBase a g ε t)^(p/2-2)) := by ring
      _ = _ := by rw [hpow]
  rw [hmul] at h
  unfold regSecond
  rw [show (p-2)/2=p/2-1 by ring]
  nlinarith

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section

lemma power_first_deriv {F G : ℝ → ℝ} {H r t : ℝ}
    (hF : HasDerivAt F (G t) t) (hG : HasDerivAt G H t) (hpos : 0 < F t) :
    HasDerivAt (fun s => r * F s ^ (r-1) * G s)
      (r*(r-1)*F t^(r-2)*(G t)^2 + r*F t^(r-1)*H) t := by
  have hh := ((hF.rpow_const (p := r-1) (Or.inl (ne_of_gt hpos))).const_mul r).mul hG
  have he : r*(r-1)*F t^(r-2)*(G t)^2 + r*F t^(r-1)*H =
      r*(G t*(r-1)*F t^(r-1-1))*G t + r*F t^(r-1)*H := by
    rw [show r-1-1=r-2 by ring]
    ring
  rw [← he] at hh
  exact hh

lemma power_second_bound {p u A B G : ℝ} (hp : 2 < p) (hu : 0 < u)
    (hB : B ≤ p*(p-1)*u^((p-2)/p)*G) :
    (2/p)*(2/p-1)*u^(2/p-2)*A^2 + (2/p)*u^(2/p-1)*B ≤
      2*(p-1)*G := by
  have hp0 : 0 < p := by linarith
  have hr : 2/p-1 ≤ 0 := by
    have := (div_lt_one hp0).mpr hp
    linarith
  have hneg : (2/p)*(2/p-1)*u^(2/p-2)*A^2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hr)
        (Real.rpow_nonneg hu.le _)) (sq_nonneg A)
  have hb := mul_le_mul_of_nonneg_left hB
    (show 0 ≤ (2/p)*u^(2/p-1) by positivity)
  have he : (2/p)*u^(2/p-1)*(p*(p-1)*u^((p-2)/p)*G) =
      2*(p-1)*G := by
    calc
      _ = ((2/p)*p)*(p-1)*G*(u^(2/p-1)*u^((p-2)/p)) := by ring
      _ = 2*(p-1)*G := by
        rw [← Real.rpow_add hu]
        have hex : 2/p-1+(p-2)/p = 0 := by field_simp; ring
        rw [hex, Real.rpow_zero]
        field_simp
  rw [he] at hb
  linarith

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh

lemma second_order_bound {F F' F'' : ℝ → ℝ} {C : ℝ}
    (hF : ∀ t, HasDerivAt F (F' t) t)
    (hF' : ∀ t, HasDerivAt F' (F'' t) t)
    (hbound : ∀ t, F'' t ≤ 2*C) (hz : F' 0 = 0) :
    F 1 ≤ F 0 + C := by
  let G := fun t => F t - C*t^2
  let G' := fun t => F' t - 2*C*t
  have hg (t : ℝ) : HasDerivAt G (G' t) t := by
    have hh := (((hasDerivAt_id t).pow 2).const_mul C)
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hh
    have he : C*(2*t) = 2*C*t := by ring
    rw [he] at hh
    exact (hF t).sub hh
  have hg' (t : ℝ) : HasDerivAt G' (F'' t - 2*C) t := by
    have hh : HasDerivAt (fun s : ℝ => 2*C*s) (2*C) t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (2*C)
    exact (hF' t).sub hh
  have hc : ConcaveOn ℝ Set.univ G :=
    concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).hasDerivWithinAt)
      (fun t _ => (hg' t).hasDerivWithinAt)
      (fun t _ => sub_nonpos.mpr (hbound t))
  have hh := hc.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0:ℝ)<1) (hg 0)
  simp only [slope, G, G', hz, zero_pow (by decide : 2 ≠ 0), one_pow,
    mul_zero, mul_one, sub_zero, inv_one, one_smul, vsub_eq_sub] at hh
  linarith

end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def regMoment (w g : ι → ℝ) (a ε p t : ℝ) : ℝ :=
  ∑ i, w i * (regBase a (g i) ε t)^(p/2)
def regMomentFirst (w g : ι → ℝ) (a ε p t : ℝ) : ℝ :=
  ∑ i, w i * regFirst a (g i) ε p t
def regMomentSecond (w g : ι → ℝ) (a ε p t : ℝ) : ℝ :=
  ∑ i, w i * regSecond a (g i) ε p t

lemma regMoment_pos {w : ι → ℝ} (hw : ∀ i, 0 < w i) (g : ι → ℝ)
    (a p t : ℝ) {ε : ℝ} (hε : 0 < ε) : 0 < regMoment w g a ε p t := by
  exact Finset.sum_pos (fun i _ => mul_pos (hw i)
    (Real.rpow_pos_of_pos (regBase_pos a (g i) t hε) _)) Finset.univ_nonempty

omit [Nonempty ι] in
lemma regMoment_deriv (w g : ι → ℝ) (a p t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasDerivAt (regMoment w g a ε p) (regMomentFirst w g a ε p t) t := by
  exact HasDerivAt.fun_sum (fun i _ => (reg_power_deriv a (g i) p t hε).const_mul (w i))

omit [Nonempty ι] in
lemma regMoment_first_deriv (w g : ι → ℝ) (a p t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasDerivAt (regMomentFirst w g a ε p) (regMomentSecond w g a ε p t) t := by
  exact HasDerivAt.fun_sum (fun i _ => (reg_first_deriv a (g i) p t hε).const_mul (w i))

omit [Nonempty ι] in
lemma regMoment_second_bound {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (g : ι → ℝ)
    (a t : ℝ) {ε p G : ℝ} (hε : 0 < ε) (hp : 2 < p)
    (hh : (∑ i, w i * (g i)^2 * (regBase a (g i) ε t)^((p-2)/2)) ≤
      regMoment w g a ε p t ^ ((p-2)/p)*G) :
    regMomentSecond w g a ε p t ≤
      p*(p-1)*regMoment w g a ε p t ^ ((p-2)/p)*G := by
  calc
    _ ≤ ∑ i, w i * (p*(p-1)*(g i)^2*(regBase a (g i) ε t)^((p-2)/2)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (regSecond_le a (g i) t hε hp) (hw i))
    _ = p*(p-1)*(∑ i, w i*(g i)^2*(regBase a (g i) ε t)^((p-2)/2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hh (show 0 ≤ p*(p-1) by nlinarith)
      simpa only [mul_assoc] using this

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma hessian_holder (w g u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hu : ∀ i, 0 < u i) {p : ℝ} (hp : 2 < p) :
    (∑ i, w i * (g i)^2 * (u i)^((p-2)/2)) ≤
      (∑ i, w i * (u i)^(p/2))^((p-2)/p) *
      (∑ i, w i * |g i|^p)^(2/p) := by
  have hp0 : p ≠ 0 := by linarith
  have hp2 : p-2 ≠ 0 := by linarith
  have hc : (p/(p-2)).HolderConjugate (p/2) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · apply (one_lt_div (by linarith : 0 < p-2)).mpr
      linarith
    · field_simp
      ring
  have ha (i : ι) : ((u i)^((p-2)/2))^(p/(p-2)) = (u i)^(p/2) := by
    rw [← Real.rpow_mul (hu i).le]
    congr 1
    field_simp
  have hb (i : ι) : ((g i)^2)^(p/2) = |g i|^p := by
    rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hh := weighted_holder w (fun i => (u i)^((p-2)/2)) (fun i => (g i)^2)
    hc hw (fun i => Real.rpow_nonneg (hu i).le _) (fun i => sq_nonneg _)
  simp_rw [ha, hb] at hh
  have hr : 1/(p/(p-2)) = (p-2)/p := by field_simp
  have hs : 1/(p/2) = 2/p := by field_simp
  rw [hr, hs] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma regularized_smoothness {w g : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) (hg : ∑ i, w i*g i = 0)
    (a : ℝ) {ε p : ℝ} (hε : 0 < ε) (hp : 2 < p) :
    regMoment w g a ε p 1 ^ (2/p) ≤
      a^2+ε+(p-1)*(∑ i, w i*|g i|^p)^(2/p) := by
  let S := regMoment w g a ε p
  let A := regMomentFirst w g a ε p
  let B := regMomentSecond w g a ε p
  let F := fun t => S t ^ (2/p)
  let F' := fun t => (2/p)*S t^(2/p-1)*A t
  let F'' := fun t => (2/p)*(2/p-1)*S t^(2/p-2)*(A t)^2 +
    (2/p)*S t^(2/p-1)*B t
  have hS (t : ℝ) : 0 < S t := regMoment_pos hw g a p t hε
  have hF (t : ℝ) : HasDerivAt F (F' t) t := by
    have hh := (regMoment_deriv w g a p t hε).rpow_const
      (p := 2/p) (Or.inl (ne_of_gt (hS t)))
    have he : A t*(2/p)*S t^(2/p-1) = F' t := by dsimp [F']; ring
    rw [he] at hh
    exact hh
  have hF' (t : ℝ) : HasDerivAt F' (F'' t) t :=
    power_first_deriv (regMoment_deriv w g a p t hε)
      (regMoment_first_deriv w g a p t hε) (hS t)
  have hbound (t : ℝ) : F'' t ≤ 2*((p-1)*(∑ i, w i*|g i|^p)^(2/p)) := by
    have hh := hessian_holder w g (fun i => regBase a (g i) ε t)
      (fun i => (hw i).le) (fun i => regBase_pos a (g i) t hε) hp
    have hB := regMoment_second_bound (fun i => (hw i).le) g a t hε hp hh
    simpa only [F'', S, A, B, mul_assoc] using power_second_bound (A := A t) hp (hS t) hB
  have hA : A 0 = 0 := by
    change (∑ i, w i*regFirst a (g i) ε p 0) = 0
    have he (i : ι) : w i*regFirst a (g i) ε p 0 =
        (p*a*(a^2+ε)^(p/2-1))*(w i*g i) := by
      unfold regFirst regBase
      simp only [zero_mul, add_zero]
      ring
    simp_rw [he]
    rw [← Finset.mul_sum, hg, mul_zero]
  have hzero : F' 0 = 0 := by dsimp [F']; rw [hA, mul_zero]
  have hstart : F 0 = a^2+ε := by
    have he : S 0 = (a^2+ε)^(p/2) := by
      dsimp [S, regMoment, regBase]
      simp only [zero_mul, add_zero]
      rw [← Finset.sum_mul, hw1, one_mul]
    dsimp [F]
    rw [he, ← Real.rpow_mul (by positivity : 0 ≤ a^2+ε)]
    have hx : p/2*(2/p) = 1 := by field_simp
    rw [hx, Real.rpow_one]
  have hh := second_order_bound hF hF' hbound hzero
  rw [hstart] at hh
  exact hh

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
open Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

lemma abs_rpow_exponent_deriv (x : ℝ) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun q : ℝ => |x| ^ q) (|x| ^ p * Real.log |x|) p := by
  by_cases hx : x = 0
  · subst x
    simp only [abs_zero, Real.log_zero, mul_zero]
    apply (hasDerivAt_const p (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hp] with q hq
    exact Real.zero_rpow (ne_of_gt hq)
  · simpa only [id_eq, mul_one, one_mul, mul_comm] using
      (hasDerivAt_id p).const_rpow (abs_pos.mpr hx)

lemma moment_exponent_deriv (w f : ι → ℝ) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun q => positiveMoment w (fun i => |f i|) q)
      (∑ i, w i * |f i| ^ p * Real.log |f i|) p := by
  simpa only [positiveMoment, mul_assoc] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (abs_rpow_exponent_deriv (f i) hp).const_mul (w i)))

lemma lpNorm_sq_eq (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ℝ) :
    (ChiSquare.lpNorm w p f)^2 =
      positiveMoment w (fun i => |f i|) p ^ (2 / p) := by
  rw [lpNorm_eq_moment, ← Real.rpow_natCast, ← Real.rpow_mul (moment_nonneg hw f p)]
  congr 1
  ring

lemma lpNorm_sq_exponent_deriv_of_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (f : ι → ℝ) (hS : 0 < positiveMoment w (fun i => |f i|) 2) :
    HasDerivAt (fun p : ℝ => (ChiSquare.lpNorm w p f)^2)
      (ChiSquare.entL w f / 2) 2 := by
  have hp : HasDerivAt (fun p : ℝ => 2 / p) (-(1/2:ℝ)) 2 := by
    have hh := (hasDerivAt_const (2:ℝ) (2:ℝ)).fun_div (hasDerivAt_id (2:ℝ)) (by norm_num)
    norm_num at hh
    exact hh
  have hh := (moment_exponent_deriv w f (by norm_num : (0:ℝ)<2)).rpow hp hS
  simp only [show (2:ℝ)/2=1 by norm_num, sub_self, Real.rpow_zero,
    Real.rpow_one, mul_one] at hh
  have he := entL_expansion hw f
  convert hh using 1
  · funext p
    exact lpNorm_sq_eq w f hw p
  · rw [he]
    ring

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
open Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma lp_smoothness {w g : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) (hg : ∑ i, w i*g i = 0)
    (a : ℝ) {p : ℝ} (hp : 2 < p) :
    (ChiSquare.lpNorm w p (fun i => a+g i))^2 ≤
      a^2+(p-1)*(ChiSquare.lpNorm w p g)^2 := by
  let F := fun ε : ℝ => regMoment w g a ε p 1 ^ (2/p)
  have hc : ContinuousAt F 0 := by
    apply ContinuousAt.rpow_const _ (Or.inr (by positivity : 0 ≤ 2/p))
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact continuousAt_const.mul
      ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inr (by linarith : 0 ≤ p/2)))
  have hr : ContinuousAt (fun ε : ℝ => a^2+ε+
      (p-1)*(∑ i, w i*|g i|^p)^(2/p)) 0 := by fun_prop
  have hh := le_of_tendsto_of_tendsto
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (hr.tendsto.mono_left nhdsWithin_le_nhds)
    (show ∀ᶠ ε in 𝓝[>] (0:ℝ), F ε ≤
      a^2+ε+(p-1)*(∑ i, w i*|g i|^p)^(2/p) from by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact regularized_smoothness hw hw1 hg a hε hp)
  have hi (i : ι) : (regBase a (g i) 0 1)^(p/2) = |a+g i|^p := by
    simp only [regBase, one_mul, add_zero]
    rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  dsimp [F, regMoment] at hh
  simp_rw [hi] at hh
  rw [lpNorm_sq_eq w _ (fun i => (hw i).le), lpNorm_sq_eq w _ (fun i => (hw i).le)]
  simpa only [add_zero, positiveMoment] using hh

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
open Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma lpNorm_sq_exponent_deriv {w : ι → ℝ} (hw : ∀ i, 0 < w i) (f : ι → ℝ) :
    HasDerivAt (fun p : ℝ => (ChiSquare.lpNorm w p f)^2)
      (ChiSquare.entL w f / 2) 2 := by
  classical
  by_cases hz : ∀ i, f i = 0
  · have hE : ChiSquare.entL w f = 0 := by
      simp [ChiSquare.entL, hz, Real.zero_rpow (by norm_num : (2:ℝ)≠0)]
    rw [hE, zero_div]
    apply (hasDerivAt_const (2:ℝ) (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (by norm_num : (0:ℝ)<2)] with p hp
    simp [ChiSquare.lpNorm, hz, Real.zero_rpow (ne_of_gt hp),
      Real.zero_rpow (inv_ne_zero (ne_of_gt hp))]
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    apply lpNorm_sq_exponent_deriv_of_pos (fun j => (hw j).le)
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le
      (Real.rpow_nonneg (abs_nonneg _) _))
    exact ⟨i, Finset.mem_univ _, mul_pos (hw i) (Real.rpow_pos_of_pos (abs_pos.mpr hi) _)⟩

omit [Nonempty ι] in
lemma lpNorm_two_sq {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) :
    (ChiSquare.lpNorm w 2 f)^2 = ∑ i, w i*(f i)^2 := by
  have hh := lpNorm_rpow hw f (by norm_num : (2:ℝ)≠0)
  simpa only [Real.rpow_two, positiveMoment, sq_abs] using hh

omit [Nonempty ι] in
lemma centered_two_sq {w g : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hg : ∑ i, w i*g i = 0) (a : ℝ) :
    (ChiSquare.lpNorm w 2 (fun i => a+g i))^2 =
      a^2+(ChiSquare.lpNorm w 2 g)^2 := by
  rw [lpNorm_two_sq hw, lpNorm_two_sq hw]
  have hi (i : ι) : w i*(a+g i)^2 = a^2*w i + 2*a*(w i*g i) + w i*(g i)^2 := by ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hw1, hg]
  ring

lemma rothaus_centered {w g : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) (hg : ∑ i, w i*g i = 0) (a : ℝ) :
    ChiSquare.entL w (fun i => a+g i) ≤
      ChiSquare.entL w g + 2*(ChiSquare.lpNorm w 2 g)^2 := by
  have hl := lpNorm_sq_exponent_deriv hw (fun i => a+g i)
  have hgder := lpNorm_sq_exponent_deriv hw g
  have hr := (((hasDerivAt_id (2:ℝ)).sub_const 1).mul hgder).const_add (a^2)
  have he := centered_two_sq (fun i => (hw i).le) hw1 hg a
  have hle : ∀ᶠ p in 𝓝[>] (2:ℝ), (ChiSquare.lpNorm w p (fun i => a+g i))^2 ≤
      a^2+(p-1)*(ChiSquare.lpNorm w p g)^2 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact lp_smoothness hw hw1 hg a hp
  have hh := right_derivative_comparison hl hr (by norm_num only [Pi.mul_apply, id_eq, one_mul]; exact he) hle
  norm_num only [id_eq] at hh
  linarith

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma rothaus_native {π : ι → ℝ} (hπ : ∀ i, 0 < π i)
    (hπ1 : ∑ i, π i = 1) (f : ι → ℝ) :
    ChiSquare.entL π f ≤
      ChiSquare.entL π (fun i => f i - MarkovMixing.distExp π f) +
        2*MarkovMixing.distVar π f := by
  let a := MarkovMixing.distExp π f
  let g := fun i => f i-a
  have hg : ∑ i, π i*g i = 0 := by
    dsimp [g]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hπ1, one_mul]
    dsimp [a, MarkovMixing.distExp]
    apply sub_eq_zero.mpr
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hv : (ChiSquare.lpNorm π 2 g)^2 = MarkovMixing.distVar π f := by
    rw [lpNorm_two_sq (fun i => (hπ i).le)]
    unfold MarkovMixing.distVar
    apply Finset.sum_congr rfl
    intro i _
    dsimp [g, a]
    ring
  have hh := rothaus_centered hπ hπ1 hg a
  have he : (fun i => a+g i) = f := by funext i; dsimp [g]; ring
  rw [he, hv] at hh
  exact hh

end
end LogSobolevMC.LowerBound.Fresh
end

section

namespace LogSobolevMC.LowerBound.Fresh

theorem native_full_root {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (_hirr : MarkovMixing.Irreducible K)
    (hrev : MarkovMixing.DetailedBalance K π) :
    (∀ (q t_q M_q : ℝ), 2 < q → 0 < t_q →
      (∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) →
      (1 - 2 / q) * LogSobolevMC.ChiSquare.gap K π /
        (2 * (LogSobolevMC.ChiSquare.gap K π * t_q + Real.log M_q + (q - 2) / q)) ≤ LogSobolevMC.ChiSquare.logSobolev K π) ∧
    (∀ (t_q M_q : ℝ), 0 < t_q →
      (∀ f : V → ℝ, supNorm (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) →
      LogSobolevMC.ChiSquare.gap K π /
        (2 * (LogSobolevMC.ChiSquare.gap K π * t_q + Real.log M_q + 1)) ≤ LogSobolevMC.ChiSquare.logSobolev K π) := by
  classical
  let _ : Nonempty V := by
    by_contra hn
    let _ : IsEmpty V := not_nonempty_iff.mp hn
    have hz : (0 : ℝ) = 1 := by simpa using hπ.1.2
    norm_num at hz
  have hfinite : ∀ (q t M : ℝ), 2 < q → 0 < t →
      (∀ f : V → ℝ, ChiSquare.lpNorm π q (ChiSquare.heatOp K t f) ≤
        M * ChiSquare.lpNorm π 2 f) →
      (1 - 2 / q) * ChiSquare.gap K π /
        (2 * (ChiSquare.gap K π * t + Real.log M + (q - 2) / q)) ≤
          ChiSquare.logSobolev K π := by
    intro q t M hq ht hb
    apply native_lower_from_defective hK hπ hπpos q t M hq ht
      (heat_bound_constant hK hπ ht.le hb)
    · exact fun f => defective_lsi K π hK hπ hπpos hrev q t M hq ht hb f
    · exact fun f => rothaus_native hπpos hπ.1.2 f
  refine ⟨hfinite, ?_⟩
  intro t M ht hb
  have hqbound : ∀ q : ℝ, 2 < q → ∀ f : V → ℝ,
      ChiSquare.lpNorm π q (ChiSquare.heatOp K t f) ≤ M * ChiSquare.lpNorm π 2 f := by
    intro q hq f
    exact (lpNorm_le_supNorm hπ.1.1 hπ.1.2 (by linarith : 0 < q) _).trans (hb f)
  have hM : 1 ≤ M := heat_bound_constant hK hπ ht.le (hqbound 3 (by norm_num))
  apply finite_q_bound_implies_infinity (ChiSquare.gap K π) t M (ChiSquare.logSobolev K π)
    (native_gap_nonneg K π hπ.1.1 (dirichlet_nonneg hK hπ)) ht hM
  intro q hq
  exact hfinite q t M hq ht (hqbound q hq)

end LogSobolevMC.LowerBound.Fresh
end

open LogSobolevMC.LowerBound

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (hrev : MarkovMixing.DetailedBalance K π) :
    (∀ (q t_q M_q : ℝ), 2 < q → 0 < t_q →
      (∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) →
      (1 - 2 / q) * LogSobolevMC.ChiSquare.gap K π /
        (2 * (LogSobolevMC.ChiSquare.gap K π * t_q + Real.log M_q + (q - 2) / q)) ≤ LogSobolevMC.ChiSquare.logSobolev K π) ∧
    (∀ (t_q M_q : ℝ), 0 < t_q →
      (∀ f : V → ℝ, supNorm (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) →
      LogSobolevMC.ChiSquare.gap K π /
        (2 * (LogSobolevMC.ChiSquare.gap K π * t_q + Real.log M_q + 1)) ≤ LogSobolevMC.ChiSquare.logSobolev K π)  := by
  exact Fresh.native_full_root K hK π hπ hπpos hirr hrev
