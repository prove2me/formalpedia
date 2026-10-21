-- Prove2me | solution 1 for NesterovRCD.Sublinear.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T03:21:58.369359+00:00
-- url     : https://prove2.me/submissions/1e24cc14-067b-4f75-ac36-8ec10b9fe47d

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic
open scoped BigOperators
open NesterovRCD.Sublinear

namespace RCDMProof

end RCDMProof

open NesterovRCD.Sublinear

namespace RCDMProof

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma sharp_apply_norm {s : F →L[ℝ] ℝ} {v : F} (h : IsSharp s v) :
    s v = ‖v‖ ^ 2 := by
  have hq (t : ℝ) : t * s v - t ^ 2 * ‖v‖ ^ 2 / 2 ≤ s v - ‖v‖ ^ 2 / 2 := by
    have ht := h (t • v)
    simpa only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs] using ht
  have hm : IsLocalMax (fun t : ℝ => t * s v - t ^ 2 * ‖v‖ ^ 2 / 2) 1 := by
    filter_upwards [] with t
    simpa using hq t
  have hd : HasDerivAt (fun t : ℝ => t * s v - t ^ 2 * ‖v‖ ^ 2 / 2)
      (s v - ‖v‖ ^ 2) 1 := by
    convert (((hasDerivAt_id (1 : ℝ)).mul_const (s v)).sub
      ((((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (‖v‖ ^ 2)).div_const 2)) using 1 <;> first | rfl | norm_num
  have hz := hm.hasDerivAt_eq_zero hd
  linarith

lemma sharp_norm {s : F →L[ℝ] ℝ} {v : F} (h : IsSharp s v) : ‖v‖ = ‖s‖ := by
  have hv := sharp_apply_norm h
  have he (w : F) : |s w| ≤ ‖v‖ * ‖w‖ := by
    by_cases hw : w = 0
    · simp [hw]
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hw2 : ‖w‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hw0)
    have ht := h ((s w / ‖w‖ ^ 2) • w)
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, hv] at ht
    have hs : (s w) ^ 2 ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
      field_simp at ht
      nlinarith [sq_nonneg (s w)]
    apply (sq_le_sq₀ (abs_nonneg (s w)) (mul_nonneg (norm_nonneg v) (norm_nonneg w))).mp
    simpa only [sq_abs, mul_pow] using hs
  have hle : ‖s‖ ≤ ‖v‖ := s.opNorm_le_bound (norm_nonneg v) fun w => by
    simpa only [Real.norm_eq_abs] using he w
  have hr := s.le_opNorm v
  rw [Real.norm_eq_abs, hv, abs_of_nonneg (sq_nonneg _)] at hr
  nlinarith [norm_nonneg v, norm_nonneg s]

lemma sharp_apply {s : F →L[ℝ] ℝ} {v : F} (h : IsSharp s v) : s v = ‖s‖ ^ 2 := by
  rw [sharp_apply_norm h, sharp_norm h]

end RCDMProof

open scoped BigOperators
open NesterovRCD.Sublinear

namespace RCDMProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

lemma line_derivative {f : Blocks E → ℝ} (hf : Differentiable ℝ f)
    (x h : Blocks E) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (x + u • h)) (fderiv ℝ f (x + t • h) h) t := by
  exact (hf (x + t • h)).hasFDerivAt.comp_hasDerivAt t
    (by simpa only [id_eq, one_smul] using (((hasDerivAt_id t).smul_const h).const_add x))

lemma coordinate_upper {f : Blocks E → ℝ} {L : Fin n → ℝ}
    (hL : CoordLipschitz f L) (x : Blocks E) (i : Fin n) (h : E i) :
    f (x + Pi.single i h) ≤ f x + partialGrad f x i h + L i / 2 * ‖h‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => f (x + t • Pi.single i h) - f x -
    t * partialGrad f x i h - L i / 2 * t ^ 2 * ‖h‖ ^ 2
  have hd (t : ℝ) : HasDerivAt g
      (partialGrad f (x + t • Pi.single i h) i h - partialGrad f x i h -
        L i * t * ‖h‖ ^ 2) t := by
    have hf := line_derivative hL.1 x (Pi.single i h) t
    convert ((hf.sub_const (f x)).sub ((hasDerivAt_id t).mul_const
      (partialGrad f x i h))).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L i / 2)).mul_const (‖h‖ ^ 2)) using 1
    all_goals
      first
      | rfl
      | dsimp [g, partialGrad]
        simp only [ContinuousLinearMap.single_apply]
        ring

  have hsign (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      partialGrad f (x + t • Pi.single i h) i h - partialGrad f x i h -
        L i * t * ‖h‖ ^ 2 ≤ 0 := by
    have hn := hL.2.2 i x (t • h)
    have he := (partialGrad f (x + t • Pi.single i h) i - partialGrad f x i).le_opNorm h
    have hp : Pi.single i (t • h) = t • Pi.single i h := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    rw [hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hn
    have hh := mul_le_mul_of_nonneg_right hn (norm_nonneg h)
    simp only [sub_apply, Real.norm_eq_abs] at he
    have ha := le_abs_self (partialGrad f (x + t • Pi.single i h) i h - partialGrad f x i h)
    nlinarith
  have hg : AntitoneOn g (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => hsign t (interior_subset ht))
  have hh := hg (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num) zero_le_one
  dsimp [g] at hh
  simp only [zero_smul, add_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    one_smul, one_mul, one_pow, mul_one] at hh
  linarith

lemma coordStep_decrease {f : Blocks E → ℝ} {L : Fin n → ℝ}
    (hL : CoordLipschitz f L) {sharp : ∀ i, (E i →L[ℝ] ℝ) → E i}
    (hsharp : IsSharpSelection sharp) (x : Blocks E) (i : Fin n) :
    ‖partialGrad f x i‖ ^ 2 / (2 * L i) ≤ f x - f (coordStep f L sharp i x) := by
  have hi := hL.2.1 i
  have hv := hsharp i (partialGrad f x i)
  have h := coordinate_upper hL x i (-((L i)⁻¹ • sharp i (partialGrad f x i)))
  have hp : Pi.single i (-((L i)⁻¹ • sharp i (partialGrad f x i))) =
      -Pi.single i ((L i)⁻¹ • sharp i (partialGrad f x i)) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  rw [hp, ← sub_eq_add_neg] at h
  simp only [map_neg, map_smul, smul_eq_mul, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hi), sharp_apply hv, sharp_norm hv] at h
  change ‖partialGrad f x i‖ ^ 2 / (2 * L i) ≤ f x -
    f (x - Pi.single i ((L i)⁻¹ • sharp i (partialGrad f x i)))
  have he : L i / 2 * ((L i)⁻¹ * ‖partialGrad f x i‖) ^ 2 =
      (L i)⁻¹ * ‖partialGrad f x i‖ ^ 2 / 2 := by field_simp
  rw [he] at h
  have hd : ‖partialGrad f x i‖ ^ 2 / (2 * L i) =
      (L i)⁻¹ * ‖partialGrad f x i‖ ^ 2 / 2 := by ring
  rw [hd]
  linarith

lemma coordStep_le {f : Blocks E → ℝ} {L : Fin n → ℝ}
    (hL : CoordLipschitz f L) {sharp : ∀ i, (E i →L[ℝ] ℝ) → E i}
    (hsharp : IsSharpSelection sharp) (x : Blocks E) (i : Fin n) :
    f (coordStep f L sharp i x) ≤ f x := by
  have h := coordStep_decrease hL hsharp x i
  have hi := hL.2.1 i
  have hn : 0 ≤ ‖partialGrad f x i‖ ^ 2 / (2 * L i) := by positivity
  linarith

end RCDMProof

open scoped BigOperators
open NesterovRCD.Sublinear

namespace RCDMProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

theorem S_pos (hn : 0 < n) {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (α : ℝ) :
    0 < S L α := by
  apply Finset.sum_pos
  · intro i _
    exact Real.rpow_pos_of_pos (hL i) α
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem prob_pos (hn : 0 < n) {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (α : ℝ)
    (i : Fin n) : 0 < prob L α i :=
  div_pos (Real.rpow_pos_of_pos (hL i) α) (S_pos hn hL α)

theorem prob_nonneg (hn : 0 < n) {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (α : ℝ)
    (i : Fin n) : 0 ≤ prob L α i := (prob_pos hn hL α i).le

theorem prob_sum (hn : 0 < n) {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (α : ℝ) :
    ∑ i, prob L α i = 1 := by
  simp only [prob, ← Finset.sum_div]
  exact div_self (S_pos hn hL α).ne'

omit [∀ i, NormedSpace ℝ (E i)] in
theorem wnorm_nonneg (L : Fin n → ℝ) (β : ℝ) (x : Blocks E) :
    0 ≤ wnorm L β x := Real.sqrt_nonneg _

theorem wdual_nonneg (L : Fin n → ℝ) (β : ℝ) (g : ∀ i, E i →L[ℝ] ℝ) :
    0 ≤ wdual L β g := Real.sqrt_nonneg _

omit [∀ i, NormedSpace ℝ (E i)] in
theorem wnorm_sq {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (β : ℝ) (x : Blocks E) :
    wnorm L β x ^ 2 = ∑ i, L i ^ β * ‖x i‖ ^ 2 := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_pos_of_pos (hL i) β).le (sq_nonneg _)

theorem wdual_sq {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (β : ℝ)
    (g : ∀ i, E i →L[ℝ] ℝ) :
    wdual L β g ^ 2 = ∑ i, (L i ^ β)⁻¹ * ‖g i‖ ^ 2 := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr
    (Real.rpow_pos_of_pos (hL i) β).le) (sq_nonneg _)

theorem weight_identity {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (α : ℝ) (i : Fin n) :
    L i ^ α * (L i ^ (1 - α)) = L i := by
  rw [← Real.rpow_add (hL i)]
  simp

theorem prob_div_L (hn : 0 < n) {L : Fin n → ℝ} (hL : ∀ i, 0 < L i)
    (α : ℝ) (i : Fin n) :
    prob L α i / L i = (L i ^ (1 - α))⁻¹ / S L α := by
  have h := weight_identity hL α i
  have hw := (Real.rpow_pos_of_pos (hL i) (1 - α)).ne'
  have he : L i ^ α = L i / L i ^ (1 - α) := (eq_div_iff hw).mpr h
  dsimp [prob]
  rw [he]
  field_simp [(hL i).ne', (S_pos hn hL α).ne', hw]

theorem L_div_prob (hn : 0 < n) {L : Fin n → ℝ} (hL : ∀ i, 0 < L i)
    (α : ℝ) (i : Fin n) : L i / prob L α i = S L α * L i ^ (1 - α) := by
  have h := weight_identity hL α i
  have hp := (Real.rpow_pos_of_pos (hL i) α).ne'
  have hs := (S_pos hn hL α).ne'
  dsimp [prob]
  field_simp
  nlinarith [h]

theorem weighted_duality {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (β : ℝ)
    (g : ∀ i, E i →L[ℝ] ℝ) (x : Blocks E) :
    (∑ i, g i (x i)) ≤ wdual L β g * wnorm L β x := by
  have hw (i : Fin n) : 0 < L i ^ β := Real.rpow_pos_of_pos (hL i) β
  have hid (i : Fin n) : Real.sqrt ((L i ^ β)⁻¹) * Real.sqrt (L i ^ β) = 1 := by
    rw [← Real.sqrt_mul (inv_nonneg.mpr (hw i).le), inv_mul_cancel₀ (hw i).ne', Real.sqrt_one]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => Real.sqrt ((L i ^ β)⁻¹) * ‖g i‖)
    (fun i => Real.sqrt (L i ^ β) * ‖x i‖)
  simp only [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (hw _).le),
    Real.sq_sqrt (hw _).le] at hcs
  calc
    (∑ i, g i (x i)) ≤ ∑ i, ‖g i‖ * ‖x i‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (g i).le_opNorm (x i))
    _ = ∑ i, (Real.sqrt ((L i ^ β)⁻¹) * ‖g i‖) *
        (Real.sqrt (L i ^ β) * ‖x i‖) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        ‖g i‖ * ‖x i‖ = (Real.sqrt ((L i ^ β)⁻¹) * Real.sqrt (L i ^ β)) *
            (‖g i‖ * ‖x i‖) := by rw [hid i, one_mul]
        _ = _ := by ring
    _ ≤ wdual L β g * wnorm L β x := hcs

end RCDMProof

open scoped BigOperators
open NesterovRCD.Sublinear

namespace RCDMProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

lemma partial_sum (f : Blocks E → ℝ) (x h : Blocks E) :
    (∑ i, partialGrad f x i (h i)) = fderiv ℝ f x h := by
  conv_rhs => rw [← Finset.univ_sum_single h, map_sum]
  rfl

lemma convex_support {f : Blocks E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    (hf : Differentiable ℝ f) (x y : Blocks E) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  have hline : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • (y - x))) := by
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a b ha hb hab
    convert hc.2 (Set.mem_univ (x + u • (y - x)))
      (Set.mem_univ (x + v • (y - x))) ha hb hab using 1
    apply congrArg f
    calc
      x + (a * u + b * v) • (y - x) = (a + b) • x + (a * u + b * v) • (y - x) := by rw [hab, one_smul]
      _ = a • (x + u • (y - x)) + b • (x + v • (y - x)) := by module
  have hd := line_derivative hf x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have hs := hline.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) zero_lt_one hd
  simp only [slope, zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero,
    inv_one, one_smul, vsub_eq_sub] at hs
  linarith

lemma minimizer_derivative_zero {f : Blocks E → ℝ} {xs : Blocks E}
    (hxs : IsMinimizer f xs) : fderiv ℝ f xs = 0 := by
  have hm : IsLocalMin f xs := Filter.Eventually.of_forall hxs
  exact hm.fderiv_eq_zero

lemma full_upper_model {f : Blocks E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    {L : Fin n → ℝ} (hL : CoordLipschitz f L) (hn : 0 < n)
    (α : ℝ) (x h : Blocks E) :
    f (x + h) ≤ f x + fderiv ℝ f x h + S L α / 2 * wnorm L (1 - α) h ^ 2 := by
  have hp (i : Fin n) : 0 < prob L α i := prob_pos hn hL.2.1 α i
  have he (i : Fin n) : prob L α i •
      (x + Pi.single i ((prob L α i)⁻¹ • h i)) =
      prob L α i • x + Pi.single i (h i) := by
    ext j
    by_cases hj : j = i
    · subst j; simp [smul_add, smul_smul, (hp i).ne']
    · simp [hj]
  have hmean : (∑ i, prob L α i • (x + Pi.single i ((prob L α i)⁻¹ • h i))) = x + h := by
    simp only [he, Finset.sum_add_distrib, ← Finset.sum_smul, prob_sum hn hL.2.1 α,
      one_smul, Finset.univ_sum_single h]
  have hj := hc.map_sum_le (t := Finset.univ) (w := prob L α)
    (fun i _ => (hp i).le) (prob_sum hn hL.2.1 α)
    (fun i _ => Set.mem_univ (x + Pi.single i ((prob L α i)⁻¹ • h i)))
  rw [hmean] at hj
  have hi (i : Fin n) : prob L α i * f (x + Pi.single i ((prob L α i)⁻¹ • h i)) ≤
      prob L α i * f x + partialGrad f x i (h i) +
        S L α / 2 * (L i ^ (1 - α) * ‖h i‖ ^ 2) := by
    have hu := mul_le_mul_of_nonneg_left
      (coordinate_upper hL x i ((prob L α i)⁻¹ • h i)) (hp i).le
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hp i))] at hu
    have hid := L_div_prob hn hL.2.1 α i
    have halg : prob L α i * (f x + (prob L α i)⁻¹ * partialGrad f x i (h i) +
        L i / 2 * ((prob L α i)⁻¹ * ‖h i‖) ^ 2) =
        prob L α i * f x + partialGrad f x i (h i) +
          S L α / 2 * (L i ^ (1 - α) * ‖h i‖ ^ 2) := by
      calc
        _ = prob L α i * f x + partialGrad f x i (h i) +
            (L i / prob L α i) / 2 * ‖h i‖ ^ 2 := by
          field_simp [(hp i).ne']
        _ = _ := by rw [hid]; ring

    rwa [halg] at hu
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hsum : (∑ i, (prob L α i * f x + partialGrad f x i (h i) +
        S L α / 2 * (L i ^ (1 - α) * ‖h i‖ ^ 2))) =
      f x + fderiv ℝ f x h + S L α / 2 * wnorm L (1 - α) h ^ 2 := by
    rw [wnorm_sq hL.2.1]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      prob_sum hn hL.2.1 α, one_mul, partial_sum]
  rw [hsum] at hs
  exact hj.trans hs

omit [∀ i, NormedSpace ℝ (E i)] in
lemma radius_nonneg {f : Blocks E → ℝ} {L : Fin n → ℝ} {β : ℝ}
    {x0 xs : Blocks E} (hxs : IsMinimizer f xs) {R : ℝ}
    (hR : LevelRadiusLE f L β x0 R) : 0 ≤ R :=
  (wnorm_nonneg L β (x0 - xs)).trans (hR x0 le_rfl xs hxs)

lemma initial_gap {f : Blocks E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    {L : Fin n → ℝ} (hL : CoordLipschitz f L) (hn : 0 < n) (α : ℝ)
    {x0 xs : Blocks E} (hxs : IsMinimizer f xs) {R : ℝ}
    (hR : LevelRadiusLE f L (1 - α) x0 R) :
    f x0 - f xs ≤ S L α / 2 * R ^ 2 := by
  have h := full_upper_model hc hL hn α xs (x0 - xs)
  rw [add_sub_cancel, minimizer_derivative_zero hxs, zero_apply, add_zero] at h
  have hr := hR x0 le_rfl xs hxs
  have hr0 := radius_nonneg hxs hR
  have hn0 := wnorm_nonneg L (1 - α) (x0 - xs)
  have hsq : wnorm L (1 - α) (x0 - xs) ^ 2 ≤ R ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (div_nonneg (S_pos hn hL.2.1 α).le (by norm_num : (0:ℝ)≤2))
  linarith

lemma gap_sq {f : Blocks E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    {L : Fin n → ℝ} (hL : CoordLipschitz f L) (α : ℝ)
    {x0 xs : Blocks E} (hxs : IsMinimizer f xs) {R : ℝ}
    (hR : LevelRadiusLE f L (1 - α) x0 R) {x : Blocks E} (hx : f x ≤ f x0) :
    (f x - f xs) ^ 2 ≤ R ^ 2 * wdual L (1 - α) (gradBlocks f x) ^ 2 := by
  have hs := convex_support hc hL.1 x xs
  have he : fderiv ℝ f x (xs - x) = -fderiv ℝ f x (x - xs) := by
    rw [← map_neg, neg_sub]
  rw [he] at hs
  have hw := weighted_duality hL.2.1 (1 - α) (gradBlocks f x) (x - xs)
  change (∑ i, partialGrad f x i ((x - xs) i)) ≤ _ at hw
  rw [partial_sum] at hw
  have hr := mul_le_mul_of_nonneg_left (hR x hx xs hxs)
    (wdual_nonneg L (1 - α) (gradBlocks f x))
  have hh : 0 ≤ f x - f xs := sub_nonneg.mpr (hxs x)
  have hb : f x - f xs ≤ wdual L (1 - α) (gradBlocks f x) * R := by linarith
  have hb0 := mul_nonneg (wdual_nonneg L (1 - α) (gradBlocks f x)) (radius_nonneg hxs hR)
  have hsq := (sq_le_sq₀ hh hb0).mpr hb
  nlinarith [hsq]

lemma expected_step_gap {f : Blocks E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    {L : Fin n → ℝ} (hL : CoordLipschitz f L) (hn : 0 < n)
    {sharp : ∀ i, (E i →L[ℝ] ℝ) → E i} (hsharp : IsSharpSelection sharp) (α : ℝ)
    {x0 xs : Blocks E} (hxs : IsMinimizer f xs) {R : ℝ}
    (hR : LevelRadiusLE f L (1 - α) x0 R) {x : Blocks E} (hx : f x ≤ f x0) :
    (f x - f xs) ^ 2 ≤ (2 * S L α * R ^ 2) *
      (f x - ∑ i, prob L α i * f (coordStep f L sharp i x)) := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (coordStep_decrease hL hsharp x i)
      (prob_nonneg hn hL.2.1 α i))
  have hid (i : Fin n) : prob L α i * (‖partialGrad f x i‖ ^ 2 / (2 * L i)) =
      ((L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * S L α) := by
    have hi := prob_div_L hn hL.2.1 α i
    calc
      _ = (prob L α i / L i) * ‖partialGrad f x i‖ ^ 2 / 2 := by ring
      _ = _ := by rw [hi]; ring
  simp only [hid, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, prob_sum hn hL.2.1 α, one_mul] at hs
  have hw := wdual_sq hL.2.1 (1 - α) (gradBlocks f x)
  change wdual L (1 - α) (gradBlocks f x) ^ 2 = ∑ i, (L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2 at hw
  rw [← hw] at hs
  have hd := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) (S_pos hn hL.2.1 α))).mp hs
  have hm := mul_le_mul_of_nonneg_left hd (sq_nonneg R)
  have hg := gap_sq hc hL α hxs hR hx
  nlinarith [hg, hm]

end RCDMProof

open scoped BigOperators
open NesterovRCD.Sublinear

namespace RCDMProof

variable {n : ℕ}

theorem expect_zero (p : Fin n → ℝ) (F : (Fin 0 → Fin n) → ℝ) :
    expect p 0 F = F Fin.elim0 := by
  simp [expect]
  exact congrArg F (Subsingleton.elim _ _)

theorem expect_succ (p : Fin n → ℝ) (k : ℕ) (F : (Fin (k + 1) → Fin n) → ℝ) :
    expect p (k + 1) F = expect p k (fun idx => ∑ i, p i * F (Fin.snoc idx i)) := by
  classical
  unfold expect
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply]
  have hw (i : Fin n) (idx : Fin k → Fin n) :
      (∏ j : Fin (k + 1), p ((Fin.snoc idx i : Fin (k + 1) → Fin n) j)) = (∏ j, p (idx j)) * p i := by
    rw [Fin.prod_univ_castSucc]
    simp
  simp_rw [hw]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro idx _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (∏ j, p (idx j)) * p i * F (Fin.snoc idx i) =
    (∏ j, p (idx j)) * (p i * F (Fin.snoc idx i))
  ring

theorem expect_one {p : Fin n → ℝ} (hp : ∑ i, p i = 1) :
    ∀ k, expect p k (fun _ => 1) = 1 := by
  intro k
  induction k with
  | zero => simp [expect]
  | succ k ih =>
    rw [expect_succ]
    simpa only [mul_one, hp] using ih

theorem expect_const {p : Fin n → ℝ} (hp : ∑ i, p i = 1) (k : ℕ) (c : ℝ) :
    expect p k (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul]
  have h := expect_one hp k
  simp only [expect, mul_one] at h
  rw [h, one_mul]

theorem expect_add (p : Fin n → ℝ) (k : ℕ) (F G : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => F idx + G idx) = expect p k F + expect p k G := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (p : Fin n → ℝ) (k : ℕ) (F G : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => F idx - G idx) = expect p k F - expect p k G := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (p : Fin n → ℝ) (k : ℕ) (c : ℝ) (F : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => c * F idx) = c * expect p k F := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro idx _
  ring

theorem expect_mono {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    {F G : (Fin k → Fin n) → ℝ} (h : ∀ idx, F idx ≤ G idx) :
    expect p k F ≤ expect p k G := by
  apply Finset.sum_le_sum
  intro idx _
  exact mul_le_mul_of_nonneg_left (h idx) (Finset.prod_nonneg fun j _ => hp (idx j))

theorem expect_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    {F : (Fin k → Fin n) → ℝ} (h : ∀ idx, 0 ≤ F idx) : 0 ≤ expect p k F := by
  apply Finset.sum_nonneg
  intro idx _
  exact mul_nonneg (Finset.prod_nonneg fun j _ => hp (idx j)) (h idx)

theorem expect_sq {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (k : ℕ) (F : (Fin k → Fin n) → ℝ) :
    expect p k F ^ 2 ≤ expect p k (fun idx => F idx ^ 2) := by
  have h := expect_nonneg hp k (fun idx => sq_nonneg (F idx - expect p k F))
  have he : expect p k (fun idx => (F idx - expect p k F) ^ 2) =
      expect p k (fun idx => F idx ^ 2) - expect p k F ^ 2 := by
    have hf : (fun idx => (F idx - expect p k F) ^ 2) =
        (fun idx => F idx ^ 2 - (2 * expect p k F) * F idx + expect p k F ^ 2) := by
      funext idx
      ring
    rw [hf, expect_add, expect_sub, expect_mul, expect_const hs]
    ring
  rw [he] at h
  linarith

variable {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

theorem run_level (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (hstep : ∀ x i, f (coordStep f L sharp i x) ≤ f x) (x0 : Blocks E) :
    ∀ k idx, f (rcdm f L sharp x0 k idx) ≤ f x0 := by
  intro k
  induction k with
  | zero => intro idx; exact le_refl _
  | succ k ih =>
    intro idx
    exact (hstep _ _).trans (ih (Fin.init idx))

theorem run_expect_succ (p : Fin n → ℝ) (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (x0 : Blocks E) (k : ℕ) :
    expect p (k + 1) (fun idx => f (rcdm f L sharp x0 (k + 1) idx)) =
      expect p k (fun idx => ∑ i, p i * f (coordStep f L sharp i
        (rcdm f L sharp x0 k idx))) := by
  rw [expect_succ]
  simp only [rcdm, Fin.snoc_last, Fin.init_snoc]

end RCDMProof

namespace RCDMProof

theorem scalar_rate {C : ℝ} (hC : 0 ≤ C) (a : ℕ → ℝ)
    (_ha : ∀ k, 0 ≤ a k) (hzero : a 0 ≤ C / 4)
    (hstep : ∀ k, a k ^ 2 ≤ C * (a k - a (k + 1))) :
    ∀ k, a k ≤ C / ((k : ℝ) + 4) := by
  by_cases hc : C = 0
  · intro k
    have h := hstep k
    rw [hc] at h ⊢
    simp only [zero_mul, zero_div] at h ⊢
    nlinarith [sq_nonneg (a k)]
  have hcp : 0 < C := lt_of_le_of_ne hC (Ne.symm hc)
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have hd : 0 < (k : ℝ) + 4 := by positivity
    have hd' : 0 < (k : ℝ) + 5 := by positivity
    have hbound : a k * ((k : ℝ) + 4) ≤ C := (le_div_iff₀ hd).mp ih
    have hhalf : a k ≤ C / 2 := by nlinarith [_ha k]
    have hu : C / ((k : ℝ) + 4) ≤ C / 2 := by
      apply div_le_div_of_nonneg_left hC (by norm_num)
      linarith
    have hmono : C * a k - a k ^ 2 ≤
        C * (C / ((k : ℝ) + 4)) - (C / ((k : ℝ) + 4)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ih)
        (show 0 ≤ C - a k - C / ((k : ℝ) + 4) by linarith)]
    have hnext : C * (C / ((k : ℝ) + 4)) - (C / ((k : ℝ) + 4)) ^ 2 ≤
        C * (C / ((k : ℝ) + 5)) := by
      field_simp
      nlinarith [sq_nonneg C]
    have hs := hstep k
    have hn : C * a (k + 1) ≤ C * (C / ((k : ℝ) + 5)) := by linarith
    have hr := (mul_le_mul_iff_right₀ hcp).mp hn
    rw [Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ) + 1 + 4 = (k : ℝ) + 5 by ring]
    exact hr

end RCDMProof

open scoped BigOperators
open RCDMProof

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem theorem1 (hn : 0 < n) (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (α : ℝ) (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hR : LevelRadiusLE f L (1 - α) x0 R) (k : ℕ) :
    expect (prob L α) k (fun idx => f (rcdm f L sharp x0 k idx)) - f xs
      ≤ 2 / ((k : ℝ) + 4) * S L α * R ^ 2 := by
  let _ := (inferInstance : ∀ i, FiniteDimensional ℝ (E i))
  let p := prob L α
  let a : ℕ → ℝ := fun j => expect p j (fun idx => f (rcdm f L sharp x0 j idx)) - f xs
  let C : ℝ := 2 * S L α * R ^ 2
  have hp : ∀ i, 0 ≤ p i := prob_nonneg hn hL.2.1 α
  have hpsum : ∑ i, p i = 1 := prob_sum hn hL.2.1 α
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) (S_pos hn hL.2.1 α).le) (sq_nonneg R)
  have hlevel := run_level f L sharp (coordStep_le hL hsharp) x0
  have hgap (j : ℕ) : expect p j (fun idx => f (rcdm f L sharp x0 j idx) - f xs) = a j := by
    rw [expect_sub, expect_const hpsum]
  have ha (j : ℕ) : 0 ≤ a j := by
    rw [← hgap j]
    exact expect_nonneg hp j (fun idx => sub_nonneg.mpr (hxs _))
  have hz : a 0 ≤ C / 4 := by
    have h := initial_gap hconv hL hn α hxs hR
    dsimp [a, C]
    rw [expect_zero]
    change f x0 - f xs ≤ 2 * S L α * R ^ 2 / 4
    linarith
  have hs (j : ℕ) : a j ^ 2 ≤ C * (a j - a (j + 1)) := by
    calc
      a j ^ 2 = expect p j (fun idx => f (rcdm f L sharp x0 j idx) - f xs) ^ 2 := by rw [hgap]
      _ ≤ expect p j (fun idx => (f (rcdm f L sharp x0 j idx) - f xs) ^ 2) :=
        expect_sq hp hpsum j _
      _ ≤ expect p j (fun idx => C * (f (rcdm f L sharp x0 j idx) -
          ∑ i, p i * f (coordStep f L sharp i (rcdm f L sharp x0 j idx)))) := by
        apply expect_mono hp
        intro idx
        exact expected_step_gap hconv hL hn hsharp α hxs hR (hlevel j idx)
      _ = C * (a j - a (j + 1)) := by
        rw [expect_mul, expect_sub, ← run_expect_succ]
        dsimp [a]
        ring
  have h := scalar_rate hC a ha hz hs k
  dsimp [a, C, p] at h
  convert h using 1
  ring


end NesterovRCD.Sublinear

open NesterovRCD.Sublinear
variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem solution (hn : 0 < n) (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (α : ℝ) (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hR : LevelRadiusLE f L (1 - α) x0 R) (k : ℕ) :
    expect (prob L α) k (fun idx => f (rcdm f L sharp x0 k idx)) - f xs
      ≤ 2 / ((k : ℝ) + 4) * S L α * R ^ 2 := by
  let _ := (inferInstance : ∀ i, FiniteDimensional ℝ (E i))
  exact NesterovRCD.Sublinear.theorem1 hn f hconv L hL sharp hsharp α x0 xs hxs R hR k
