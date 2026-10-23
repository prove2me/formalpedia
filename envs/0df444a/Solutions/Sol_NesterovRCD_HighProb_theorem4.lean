-- Prove2me | solution 1 for NesterovRCD.HighProb.theorem4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T05:01:09.417799+00:00
-- url     : https://prove2.me/submissions/b5443e74-3a69-4720-929d-2419346ddb13

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic

open Classical

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb

namespace RCDHighProbProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

noncomputable def sqNorm (x : Blocks E) : ℝ := ∑ i, ‖x i‖ ^ 2
noncomputable def infValue (F : Blocks E → ℝ) : ℝ := sInf (Set.range F)

end RCDHighProbProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb

namespace RCDHighProbProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

omit [∀ i, FiniteDimensional ℝ (E i)] [∀ i, InnerProductSpace ℝ (E i)] in
theorem wnorm_zero_sq (L : Fin n → ℝ) (x : Blocks E) :
    wnorm L 0 x ^ 2 = sqNorm x := by
  simp only [wnorm, Real.rpow_zero, one_mul, sqNorm]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖x i‖)

theorem sharp_spec (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (hsharp : IsSharpSelection sharp) (i : Fin n) (u : E i →L[ℝ] ℝ) :
    ‖sharp i u‖ = ‖u‖ ∧ u (sharp i u) = ‖u‖ ^ 2 := by
  let v := (InnerProductSpace.toDual ℝ (E i)).symm u
  have hv (w : E i) : inner ℝ v w = u w := InnerProductSpace.toDual_symm_apply
  have hn : ‖v‖ = ‖u‖ := (InnerProductSpace.toDual ℝ (E i)).symm.norm_map u
  have hs := hsharp i u v
  rw [← hv v, ← hv (sharp i u), real_inner_self_eq_norm_sq] at hs
  have hsq := norm_sub_sq_real (sharp i u) v
  have hc : inner ℝ (sharp i u) v = inner ℝ v (sharp i u) := real_inner_comm _ _
  rw [hc] at hsq
  have hz : ‖sharp i u - v‖ = 0 := by
    have := sq_nonneg ‖sharp i u - v‖
    nlinarith [norm_nonneg (sharp i u - v)]
  have he : sharp i u = v := sub_eq_zero.mp (norm_eq_zero.mp hz)
  rw [he, ← hv v, real_inner_self_eq_norm_sq, hn]
  exact ⟨rfl, rfl⟩

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem derivative_blocks (f : Blocks E → ℝ) (x v : Blocks E) :
    fderiv ℝ f x v = ∑ i, partialGrad f x i (v i) := by
  classical
  have he : (∑ i, Pi.single i (v i)) = v := by ext i; simp
  conv_lhs => rw [← he]
  rw [map_sum]
  rfl

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem convex_support (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hd : Differentiable ℝ f) (x y : Blocks E) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  let g : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hc : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ c d hc hd hcd
    have he : x + (c * a + d * b) • (y - x) =
        c • (x + a • (y - x)) + d • (x + b • (y - x)) := by
      calc
        _ = (c + d) • x + (c * a + d * b) • (y - x) := by rw [hcd, one_smul]
        _ = _ := by module
    simpa only [g, smul_eq_mul, he] using
      hconv.2 (Set.mem_univ _) (Set.mem_univ _) hc hd hcd
  have hg : HasDerivAt g (fderiv ℝ f x (y - x)) 0 := by
    convert! (hd (x + (0 : ℝ) • (y - x))).hasFDerivAt.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x) using 1
    simp
  have hh := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hg
  simp [g, slope] at hh
  rw [map_sub]
  linarith

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem coordinate_upper (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (hL : CoordLipschitz f L) (x : Blocks E) (i : Fin n) (v : E i) :
    f (x + Pi.single i v) ≤ f x + partialGrad f x i v + L i / 2 * ‖v‖ ^ 2 := by
  classical
  let u : Blocks E := Pi.single i v
  let g : ℝ → ℝ := fun t => f (x + t • u)
  let B : ℝ → ℝ := fun t => f x + t * partialGrad f x i v + L i / 2 * ‖v‖ ^ 2 * t ^ 2
  have hg (t : ℝ) : HasDerivAt g (partialGrad f (x + t • u) i v) t := by
    convert! (hL.1 (x + t • u)).hasFDerivAt.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const u).const_add x) using 1
    simp [partialGrad, u]
  have hB (t : ℝ) : HasDerivAt B (partialGrad f x i v + L i * ‖v‖ ^ 2 * t) t := by
    convert! (((hasDerivAt_id t).mul_const (partialGrad f x i v)).const_add (f x)).add
      (((hasDerivAt_id t).pow 2).const_mul (L i / 2 * ‖v‖ ^ 2)) using 1
    dsimp
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      partialGrad f (x + t • u) i v ≤ partialGrad f x i v + L i * ‖v‖ ^ 2 * t := by
    have he : t • u = Pi.single i (t • v) := by exact (ContinuousLinearMap.single ℝ E i).map_smul t v |>.symm
    have hnorm := hL.2.2 i x (t • v)
    rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hnorm
    have hop := (partialGrad f (x + t • u) i - partialGrad f x i).le_opNorm v
    have habs : partialGrad f (x + t • u) i v - partialGrad f x i v ≤
        ‖(partialGrad f (x + t • u) i - partialGrad f x i) v‖ := by
      exact le_abs_self _
    have hm := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
    nlinarith only [habs, hop, hm]
  have hh := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hg t).continuousAt.continuousWithinAt)
    (fun t _ => (hg t).hasDerivWithinAt)
    (show g 0 ≤ B 0 by simp [g, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hbound
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  simpa [g, B, u] using hh

theorem coordinate_decrease (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (x : Blocks E) (i : Fin n) :
    f (coordStep f L sharp i x) ≤ f x - ‖partialGrad f x i‖ ^ 2 / (2 * L i) := by
  have hs := sharp_spec sharp hsharp i (partialGrad f x i)
  have hh := coordinate_upper f L hL x i (-((L i)⁻¹ • sharp i (partialGrad f x i)))
  have he : x + Pi.single i (-((L i)⁻¹ • sharp i (partialGrad f x i))) =
      coordStep f L sharp i x := by
    change x + (ContinuousLinearMap.single ℝ E i) (-_) = _
    rw [map_neg]
    simp only [coordStep, sub_eq_add_neg, ContinuousLinearMap.single_apply]
  rw [he] at hh
  simp only [map_neg, map_smul, smul_eq_mul, hs.2, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hL.2.1 i)), hs.1] at hh
  convert hh using 1
  field_simp
  ring

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem derivative_at_minimizer (f : Blocks E → ℝ) (hd : Differentiable ℝ f)
    (xs : Blocks E) (hxs : IsMinimizer f xs) : fderiv ℝ f xs = 0 := by
  have _ := hd
  exact (show IsLocalMin f xs from Filter.Eventually.of_forall hxs).fderiv_eq_zero

end RCDHighProbProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb

namespace RCDHighProbProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

noncomputable def quadDeriv (x0 x : Blocks E) : Blocks E →L[ℝ] ℝ :=
  ∑ i, 2 • (innerSL ℝ (x i - x0 i)).comp (ContinuousLinearMap.proj i)

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem quad_derivative (x0 x : Blocks E) :
    HasFDerivAt (fun y => sqNorm (y - x0)) (quadDeriv x0 x) x := by
  apply HasFDerivAt.fun_sum
  intro i _
  exact ((ContinuousLinearMap.proj i).hasFDerivAt.sub_const (x0 i)).norm_sq

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem quad_deriv_apply (x0 x v : Blocks E) :
    quadDeriv x0 x v = 2 * ∑ i, inner ℝ (x i - x0 i) (v i) := by
  simp [quadDeriv, inner_sub_left]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem reg_derivative (f : Blocks E → ℝ) (hd : Differentiable ℝ f)
    (L : Fin n → ℝ) (μ : ℝ) (x0 x : Blocks E) :
    HasFDerivAt (fReg f L μ x0)
      (fderiv ℝ f x + (μ / 2) • quadDeriv x0 x) x := by
  convert! (hd x).hasFDerivAt.add ((quad_derivative x0 x).const_mul (μ / 2)) using 1
  funext y
  simp only [fReg, wnorm_zero_sq, Pi.add_apply]

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem reg_partial (f : Blocks E → ℝ) (hd : Differentiable ℝ f)
    (L : Fin n → ℝ) (μ : ℝ) (x0 x : Blocks E) (i : Fin n) :
    partialGrad (fReg f L μ x0) x i = partialGrad f x i + μ • innerSL ℝ (x i - x0 i) := by
  classical
  ext v
  simp only [partialGrad, (reg_derivative f hd L μ x0 x).fderiv,
    ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, smul_eq_mul]
  rw [quad_deriv_apply]
  have hs : (∑ j, inner ℝ (x j - x0 j) (Pi.single i v j)) = inner ℝ (x i - x0 i) v := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  simp only [ContinuousLinearMap.single_apply, hs, innerSL_apply_apply]
  ring

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem reg_coord_lipschitz (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (hL : CoordLipschitz f L) (μ : ℝ) (hμ : 0 < μ) (x0 : Blocks E) :
    CoordLipschitz (fReg f L μ x0) (fun i => L i + μ) := by
  refine ⟨fun x => (reg_derivative f hL.1 L μ x0 x).differentiableAt,
    fun i => add_pos (hL.2.1 i) hμ, ?_⟩
  intro i x v
  rw [reg_partial f hL.1, reg_partial f hL.1]
  have he : partialGrad f (x + Pi.single i v) i + μ • innerSL ℝ ((x + Pi.single i v) i - x0 i) -
      (partialGrad f x i + μ • innerSL ℝ (x i - x0 i)) =
      (partialGrad f (x + Pi.single i v) i - partialGrad f x i) + μ • innerSL ℝ v := by
    simp only [Pi.add_apply, Pi.single_eq_same]
    ext w
    simp
    ring
  rw [he]
  calc
    _ ≤ ‖partialGrad f (x + Pi.single i v) i - partialGrad f x i‖ + ‖μ • innerSL ℝ v‖ := norm_add_le _ _
    _ ≤ L i * ‖v‖ + μ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ, innerSL_apply_norm]
      exact add_le_add (hL.2.2 i x v) le_rfl
    _ = (L i + μ) * ‖v‖ := by ring

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem quad_expansion (x0 x y : Blocks E) :
    sqNorm (y - x0) = sqNorm (x - x0) + 2 * (∑ i, inner ℝ (x i - x0 i) ((y - x) i)) + sqNorm (y - x) := by
  simp only [sqNorm, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : y i - x0 i = (x i - x0 i) + (y i - x i) := by abel
  rw [he, norm_add_sq_real]

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem reg_strong (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (μ : ℝ) (hμ : 0 < μ) (x0 : Blocks E) :
    StronglyConvexW (fReg f L μ x0) L 0 μ := by
  have _ := hμ
  refine ⟨fun x => (reg_derivative f hL.1 L μ x0 x).differentiableAt, ?_⟩
  intro x y
  rw [(reg_derivative f hL.1 L μ x0 x).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    quad_deriv_apply, fReg, wnorm_zero_sq]
  rw [quad_expansion x0 x y]
  nlinarith only [convex_support f hconv hL.1 x y]

omit [∀ i, FiniteDimensional ℝ (E i)] [∀ i, InnerProductSpace ℝ (E i)] in
theorem reg_lower (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ) (x0 x : Blocks E) : f x ≤ fReg f L μ x0 x := by
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hμ (by norm_num)) (sq_nonneg _))

omit [∀ i, FiniteDimensional ℝ (E i)] [∀ i, InnerProductSpace ℝ (E i)] in
theorem reg_at_center (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (μ : ℝ) (x0 : Blocks E) : fReg f L μ x0 x0 = f x0 := by
  simp [fReg, wnorm]

theorem inf_gradient_bound (F : Blocks E → ℝ) (L : Fin n → ℝ)
    (μ : ℝ) (hμ : 0 < μ) (hF : StronglyConvexW F L 0 μ)
    (hb : BddBelow (Set.range F)) (x : Blocks E) :
    F x - infValue F ≤ (∑ i, ‖partialGrad F x i‖ ^ 2) / (2 * μ) := by
  have _ := hb
  have hlow (y : Blocks E) : F x - (∑ i, ‖partialGrad F x i‖ ^ 2) / (2 * μ) ≤ F y := by
    have hi (i : Fin n) : -(‖partialGrad F x i‖ ^ 2 / (2 * μ)) ≤
        partialGrad F x i ((y - x) i) + μ / 2 * ‖(y - x) i‖ ^ 2 := by
      let v := (InnerProductSpace.toDual ℝ (E i)).symm (partialGrad F x i)
      have hn : ‖v‖ = ‖partialGrad F x i‖ := (InnerProductSpace.toDual ℝ (E i)).symm.norm_map _
      have he : inner ℝ v ((y - x) i) = partialGrad F x i ((y - x) i) :=
        InnerProductSpace.toDual_symm_apply
      have hz := sq_nonneg ‖v + μ • (y - x) i‖
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, hn, he] at hz
      rw [← neg_div]
      apply (div_le_iff₀ (mul_pos (by norm_num) hμ)).2
      nlinarith only [hz]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    simp only [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, Pi.sub_apply] at hs
    have hf := hF.2 x y
    rw [derivative_blocks, wnorm_zero_sq] at hf
    dsimp [sqNorm] at hf
    linarith only [hs, hf]
  have hm : F x - (∑ i, ‖partialGrad F x i‖ ^ 2) / (2 * μ) ≤ infValue F :=
    le_csInf (Set.range_nonempty F) (by rintro z ⟨y, rfl⟩; exact hlow y)
  linarith only [hm]

end RCDHighProbProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb

namespace RCDHighProbProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem sqNorm_sub_comm (x y : Blocks E) : sqNorm (x - y) = sqNorm (y - x) := by
  unfold sqNorm
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, norm_sub_rev]

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem level_sq_distance (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hRpos : 0 < R) (hR : LevelRadiusLE f L 0 x0 R) :
    sqNorm (x0 - xs) ≤ R ^ 2 := by
  have h := hR x0 le_rfl xs hxs
  have hw : 0 ≤ wnorm L 0 (x0 - xs) := Real.sqrt_nonneg _
  have hs := wnorm_zero_sq L (x0 - xs)
  nlinarith

theorem global_model_at_min (hn : 0 < n)
    (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (xs : Blocks E) (hxs : IsMinimizer f xs) (x : Blocks E) :
    f x - f xs ≤ S L 1 / 2 * sqNorm (x - xs) := by
  have hS : 0 < S L 1 := by
    simp only [S, Real.rpow_one]
    exact Finset.sum_pos (fun i _ => hL.2.1 i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let w : Fin n → ℝ := fun i => L i / S L 1
  let v : Blocks E := x - xs
  let y : Fin n → Blocks E := fun i => xs + Pi.single i ((S L 1 / L i) • v i)
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (hL.2.1 i).le hS.le
  have hsum : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div, S, Real.rpow_one]
    exact div_self (by simpa [S] using ne_of_gt hS)
  have hscale (i : Fin n) : w i * (S L 1 / L i) = 1 := by
    dsimp [w]
    field_simp [ne_of_gt hS, ne_of_gt (hL.2.1 i)]
  have hy : ∑ i, w i • y i = x := by
    calc
      ∑ i, w i • y i = (∑ i, w i) • xs + ∑ i, Pi.single i (v i) := by
        simp only [y, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [← Pi.single_smul, smul_smul, hscale, one_smul]
      _ = x := by rw [hsum, one_smul, LinearMap.sum_single_apply]; dsimp [v]; abel
  have hj := hconv.map_sum_le (t := Finset.univ) (w := w) (p := y)
    (fun i _ => hw i) hsum (fun _ _ => Set.mem_univ _)
  simp only [hy, smul_eq_mul] at hj
  have hd := derivative_at_minimizer f hL.1 xs hxs
  have hgrad (i : Fin n) (u : E i) : partialGrad f xs i u = 0 := by
    simp [partialGrad, hd]
  have hmodel (i : Fin n) :
      w i * f (y i) ≤ w i * f xs + S L 1 / 2 * ‖v i‖ ^ 2 := by
    have hi := coordinate_upper f L hL xs i ((S L 1 / L i) • v i)
    rw [hgrad] at hi
    have hi' := mul_le_mul_of_nonneg_left hi (hw i)
    have hratio : 0 ≤ S L 1 / L i := div_nonneg hS.le (hL.2.1 i).le
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio, mul_pow] at hi'
    have heq : w i * (L i / 2 * ((S L 1 / L i) ^ 2 * ‖v i‖ ^ 2)) =
        S L 1 / 2 * ‖v i‖ ^ 2 := by
      dsimp [w]
      field_simp [ne_of_gt hS, ne_of_gt (hL.2.1 i)]
    change w i * f (xs + Pi.single i ((S L 1 / L i) • v i)) ≤ _
    nlinarith only [hi', heq]
  have htot := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmodel i)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, ← Finset.mul_sum] at htot
  change (∑ i, w i * f (y i)) ≤ f xs + S L 1 / 2 * sqNorm (x - xs) at htot
  linarith

theorem initial_gap_le (hn : 0 < n)
    (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hRpos : 0 < R) (hR : LevelRadiusLE f L 0 x0 R) :
    f x0 - f xs ≤ S L 1 * R ^ 2 / 2 := by
  have hS : 0 ≤ S L 1 := by
    simp only [S, Real.rpow_one]
    exact Finset.sum_nonneg fun i _ => (hL.2.1 i).le
  calc
    f x0 - f xs ≤ S L 1 / 2 * sqNorm (x0 - xs) :=
      global_model_at_min hn f hconv L hL xs hxs x0
    _ ≤ S L 1 / 2 * R ^ 2 := mul_le_mul_of_nonneg_left
      (level_sq_distance f L x0 xs hxs R hRpos hR) (by positivity)
    _ = _ := by ring

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem reg_inf_bounds (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hRpos : 0 < R) (hR : LevelRadiusLE f L 0 x0 R)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    f xs ≤ infValue (fReg f L μ x0) ∧
      infValue (fReg f L μ x0) ≤ f xs + μ / 2 * R ^ 2 := by
  have hl (x : Blocks E) : f xs ≤ fReg f L μ x0 x :=
    (hxs x).trans (reg_lower f L μ hμ x0 x)
  have hb : BddBelow (Set.range (fReg f L μ x0)) := ⟨f xs, by rintro _ ⟨x, rfl⟩; exact hl x⟩
  constructor
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hl x)
  · calc
      infValue (fReg f L μ x0) ≤ fReg f L μ x0 xs := csInf_le hb ⟨xs, rfl⟩
      _ = f xs + μ / 2 * sqNorm (x0 - xs) := by
        rw [fReg, wnorm_zero_sq, sqNorm_sub_comm]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (level_sq_distance f L x0 xs hxs R hRpos hR) (by positivity))

end RCDHighProbProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb

namespace RCDHighProbProof

variable {n : ℕ}

theorem S_one (L : Fin n → ℝ) : S L 1 = ∑ i, L i := by
  simp [S]

theorem S_one_pos (hn : 0 < n) (L : Fin n → ℝ) (hL : ∀ i, 0 < L i) :
    0 < S L 1 := by
  rw [S_one]
  exact Finset.sum_pos (fun i _ => hL i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem prob_one_nonneg (L : Fin n → ℝ) (hL : ∀ i, 0 < L i) (i : Fin n) :
    0 ≤ prob L 1 i := by
  simp only [prob, Real.rpow_one, S_one]
  exact div_nonneg (hL i).le (Finset.sum_nonneg fun j _ => (hL j).le)

theorem prob_one_sum (hn : 0 < n) (L : Fin n → ℝ) (hL : ∀ i, 0 < L i) :
    ∑ i, prob L 1 i = 1 := by
  simp only [prob, Real.rpow_one, ← Finset.sum_div, ← S_one]
  exact div_self (ne_of_gt (S_one_pos hn L hL))

theorem expect_snoc (p : Fin n → ℝ) (k : ℕ)
    (F : (Fin (k + 1) → Fin n) → ℝ) :
    expect p (k + 1) F = expect p k (fun idx => ∑ i, p i * F (Fin.snoc idx i)) := by
  unfold expect
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp
    (fun idx => (∏ s, p (idx s)) * F idx)]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply]
  simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro idx _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((∏ s, p (idx s)) * p i) * F (Fin.snoc idx i) =
    (∏ s, p (idx s)) * (p i * F (Fin.snoc idx i))
  ring

theorem expect_mono (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    (F G : (Fin k → Fin n) → ℝ) (h : ∀ idx, F idx ≤ G idx) :
    expect p k F ≤ expect p k G := by
  exact Finset.sum_le_sum fun idx _ => mul_le_mul_of_nonneg_left (h idx)
    (Finset.prod_nonneg fun s _ => hp (idx s))

theorem expect_nonneg (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    (F : (Fin k → Fin n) → ℝ) (h : ∀ idx, 0 ≤ F idx) : 0 ≤ expect p k F := by
  exact Finset.sum_nonneg fun idx _ => mul_nonneg
    (Finset.prod_nonneg fun s _ => hp (idx s)) (h idx)

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

theorem expect_const (p : Fin n → ℝ) (hp : ∑ i, p i = 1) (k : ℕ) (c : ℝ) :
    expect p k (fun _ => c) = c := by
  induction k with
  | zero => simp [expect]
  | succ k ih =>
      rw [expect_snoc]
      simp only [← Finset.sum_mul, hp, one_mul]
      exact ih

theorem expect_markov (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    (F : (Fin k → Fin n) → ℝ) (hF : ∀ idx, 0 ≤ F idx)
    (c : ℝ) (hc : 0 < c) :
    expect p k (fun idx => if c < F idx then 1 else 0) ≤ expect p k F / c := by
  apply (le_div_iff₀ hc).2
  rw [mul_comm, ← expect_mul]
  apply expect_mono p hp k
  intro idx
  split_ifs with h
  · simpa using h.le
  · simpa using hF idx

end RCDHighProbProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb

namespace RCDHighProbProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem one_step_gap (hn : 0 < n)
    (F : Blocks E → ℝ) (K : Fin n → ℝ) (hK : CoordLipschitz F K)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (μ : ℝ) (hμ : 0 < μ) (hF : StronglyConvexW F K 0 μ)
    (hb : BddBelow (Set.range F)) (x : Blocks E) :
    (∑ i, prob K 1 i * (F (coordStep F K sharp i x) - infValue F)) ≤
      (1 - μ / S K 1) * (F x - infValue F) := by
  have hA := S_one_pos hn K hK.2.1
  have hp := prob_one_sum hn K hK.2.1
  have hstep (i : Fin n) :
      prob K 1 i * (F (coordStep F K sharp i x) - infValue F) ≤
        prob K 1 i * (F x - infValue F) - ‖partialGrad F x i‖ ^ 2 / (2 * S K 1) := by
    have h := mul_le_mul_of_nonneg_left
      (sub_le_sub_right (coordinate_decrease F K hK sharp hsharp x i) (infValue F))
      (prob_one_nonneg K hK.2.1 i)
    have he : prob K 1 i * (F x - ‖partialGrad F x i‖ ^ 2 / (2 * K i) - infValue F) =
        prob K 1 i * (F x - infValue F) - ‖partialGrad F x i‖ ^ 2 / (2 * S K 1) := by
      simp only [prob, Real.rpow_one]
      field_simp [ne_of_gt (hK.2.1 i), ne_of_gt hA]
      ring
    exact he ▸ h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, ← Finset.sum_div] at hsum
  have hg := (le_div_iff₀ (show 0 < 2 * μ by positivity)).mp
    (inf_gradient_bound F K μ hμ hF hb x)
  have hgd : μ / S K 1 * (F x - infValue F) ≤
      (∑ i, ‖partialGrad F x i‖ ^ 2) / (2 * S K 1) := by
    apply (le_div_iff₀ (show 0 < 2 * S K 1 by positivity)).2
    calc
      μ / S K 1 * (F x - infValue F) * (2 * S K 1) =
          (F x - infValue F) * (2 * μ) := by
            field_simp [ne_of_gt hA]
      _ ≤ _ := hg
  nlinarith only [hsum, hgd]

theorem expected_gap_bound (hn : 0 < n)
    (F : Blocks E → ℝ) (K : Fin n → ℝ) (hK : CoordLipschitz F K)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ S K 1)
    (hF : StronglyConvexW F K 0 μ) (hb : BddBelow (Set.range F))
    (x0 : Blocks E) (k : ℕ) :
    expect (prob K 1) k (fun idx => F (rcdm F K sharp x0 k idx) - infValue F) ≤
      (1 - μ / S K 1) ^ k * (F x0 - infValue F) := by
  have hA := S_one_pos hn K hK.2.1
  have hq : 0 ≤ 1 - μ / S K 1 := sub_nonneg.mpr ((div_le_one hA).mpr hμK)
  induction k with
  | zero => simp [expect, rcdm]
  | succ k ih =>
      rw [expect_snoc]
      simp only [rcdm, Fin.snoc_last, Fin.init_snoc]
      calc
        expect (prob K 1) k (fun idx => ∑ i, prob K 1 i *
            (F (coordStep F K sharp i (rcdm F K sharp x0 k idx)) - infValue F)) ≤
            expect (prob K 1) k (fun idx => (1 - μ / S K 1) *
              (F (rcdm F K sharp x0 k idx) - infValue F)) :=
          expect_mono _ (prob_one_nonneg K hK.2.1) _ _ _
            (fun idx => one_step_gap hn F K hK sharp hsharp μ hμ hF hb _)
        _ = (1 - μ / S K 1) * expect (prob K 1) k
            (fun idx => F (rcdm F K sharp x0 k idx) - infValue F) := expect_mul _ _ _ _
        _ ≤ (1 - μ / S K 1) * ((1 - μ / S K 1) ^ k * (F x0 - infValue F)) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = _ := by rw [pow_succ]; ring

theorem regularized_expected_gap (hn : 0 < n)
    (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hRpos : 0 < R) (hR : LevelRadiusLE f L 0 x0 R)
    (μ : ℝ) (hμ : 0 < μ) (k : ℕ) :
    expect (prob (fun i => L i + μ) 1) k
      (fun idx => fReg f L μ x0 (rcdm (fReg f L μ x0)
        (fun i => L i + μ) sharp x0 k idx) - infValue (fReg f L μ x0)) ≤
      (1 - μ / (S L 1 + (n : ℝ) * μ)) ^ k * (S L 1 * R ^ 2 / 2) := by
  let K : Fin n → ℝ := fun i => L i + μ
  let F := fReg f L μ x0
  have hK := reg_coord_lipschitz f L hL μ hμ x0
  have hstrong : StronglyConvexW F K 0 μ := by
    have hs := reg_strong f hconv L hL μ hμ x0
    refine ⟨hs.1, fun x y => ?_⟩
    simpa only [wnorm_zero_sq] using hs.2 x y
  have hsum : S K 1 = S L 1 + (n : ℝ) * μ := by
    simp [S_one, K, Finset.sum_add_distrib]
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS := S_one_pos hn L hL.2.1
  have hμK : μ ≤ S K 1 := by rw [hsum]; nlinarith
  have hb : BddBelow (Set.range F) := ⟨f xs, by
    rintro _ ⟨x, rfl⟩
    exact (hxs x).trans (reg_lower f L μ hμ.le x0 x)⟩
  have hbound := expected_gap_bound hn F K hK sharp hsharp μ hμ hμK hstrong hb x0 k
  have hi := (reg_inf_bounds f L x0 xs hxs R hRpos hR μ hμ.le).1
  have hinit : F x0 - infValue F ≤ S L 1 * R ^ 2 / 2 := by
    dsimp [F]
    rw [reg_at_center]
    exact (sub_le_sub_left hi _).trans (initial_gap_le hn f hconv L hL x0 xs hxs R hRpos hR)
  have hq : 0 ≤ 1 - μ / S K 1 := sub_nonneg.mpr
    ((div_le_one (S_one_pos hn K hK.2.1)).mpr hμK)
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hinit (pow_nonneg hq k))
  simpa only [hsum] using hfinal

end RCDHighProbProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb

namespace RCDHighProbProof

theorem printed_decay_bound (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ)
    (hk : 2 * ((n : ℝ) + 4 * t) *
      (Real.log (1 / (1 - β)) + Real.log (1 / 2 + 2 * t)) ≤ k) :
    (4 * t / 7) * (1 - 1 / ((n : ℝ) + 4 * t)) ^ k ≤ 1 - β := by
  let D : ℝ := n + 4 * t
  let C : ℝ := 1 / 2 + 2 * t
  let a : ℝ := 1 - β
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD1 : 1 < D := by dsimp [D]; linarith
  have hD : 0 < D := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have ha : 0 < a := sub_pos.mpr hβ1
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hq : 0 ≤ 1 - 1 / D := sub_nonneg.mpr ((div_le_one hD).mpr hD1.le)
  have hpow : (1 - 1 / D) ^ k ≤ Real.exp (-(k : ℝ) / D) := by
    calc
      (1 - 1 / D) ^ k ≤ (Real.exp (-(1 / D))) ^ k :=
        pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg _) k
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hdiv : 2 * (Real.log (1 / a) + Real.log C) ≤ (k : ℝ) / D := by
    apply (le_div_iff₀ hD).2
    dsimp [D, C, a]
    nlinarith only [hk]
  have hexp : Real.exp (-(k : ℝ) / D) ≤ (a / C) ^ 2 := by
    calc
      Real.exp (-(k : ℝ) / D) ≤ Real.exp (-2 * (Real.log (1 / a) + Real.log C)) :=
        Real.exp_le_exp.mpr (by simpa only [neg_div, neg_mul] using neg_le_neg hdiv)
      _ = Real.exp (Real.log (a / C) + Real.log (a / C)) := by
        congr 1
        rw [Real.log_div (by norm_num) (ne_of_gt ha), Real.log_one,
          Real.log_div (ne_of_gt ha) (ne_of_gt hC)]
        ring
      _ = (a / C) ^ 2 := by rw [Real.exp_add, Real.exp_log (div_pos ha hC), pow_two]
  have hC2 : 4 * t ≤ C ^ 2 := by dsimp [C]; nlinarith [sq_nonneg (2 * t - 1 / 2)]
  calc
    (4 * t / 7) * (1 - 1 / D) ^ k ≤ (4 * t / 7) * (a / C) ^ 2 :=
      mul_le_mul_of_nonneg_left (hpow.trans hexp) (by positivity)
    _ = (4 * t / C ^ 2) * (a ^ 2 / 7) := by ring
    _ ≤ 1 * (a ^ 2 / 7) := mul_le_mul_of_nonneg_right
      ((div_le_one (sq_pos_of_pos hC)).mpr hC2) (by positivity)
    _ ≤ a := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem high_probability_bound (hn : 0 < n)
    (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hRpos : 0 < R) (hR : LevelRadiusLE f L 0 x0 R)
    (ε β : ℝ) (hε : 0 < ε) (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : ℝ) (hμ : μ = ε / (4 * R ^ 2)) (k : ℕ)
    (hk : 2 * ((n : ℝ) + 4 * S L 1 * R ^ 2 / ε) *
      (Real.log (1 / (1 - β)) + Real.log (1 / 2 + 2 * S L 1 * R ^ 2 / ε)) ≤ k) :
    β ≤ expect (prob (fun i => L i + μ) 1) k
      (fun idx => if f (rcdm (fReg f L μ x0) (fun i => L i + μ) sharp x0 k idx) - f xs ≤ ε
        then 1 else 0) := by
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hS := S_one_pos hn L hL.2.1
  let K : Fin n → ℝ := fun i => L i + μ
  let F := fReg f L μ x0
  let X : (Fin k → Fin n) → Blocks E := rcdm F K sharp x0 k
  let G : (Fin k → Fin n) → ℝ := fun idx => F (X idx) - infValue F
  let p := prob K 1
  let t : ℝ := S L 1 * R ^ 2 / ε
  have ht : 0 < t := by dsimp [t]; positivity
  have hKpos : ∀ i, 0 < K i := fun i => add_pos (hL.2.1 i) hμpos
  have hp : ∀ i, 0 ≤ p i := prob_one_nonneg K hKpos
  have hp1 : ∑ i, p i = 1 := prob_one_sum hn K hKpos
  have hb : BddBelow (Set.range F) := ⟨f xs, by
    rintro _ ⟨x, rfl⟩
    exact (hxs x).trans (reg_lower f L μ hμpos.le x0 x)⟩
  have hG : ∀ idx, 0 ≤ G idx := fun idx => sub_nonneg.mpr (csInf_le hb ⟨X idx, rfl⟩)
  have hm := (reg_inf_bounds f L x0 xs hxs R hRpos hR μ hμpos.le).2
  have hbias : μ / 2 * R ^ 2 = ε / 8 := by
    rw [hμ]
    field_simp [ne_of_gt hRpos]
    norm_num
  rw [hbias] at hm
  have hbad (idx : Fin k → Fin n) (h : ε < f (X idx) - f xs) : 7 * ε / 8 < G idx := by
    have hl := reg_lower f L μ hμpos.le x0 (X idx)
    dsimp [G, F]
    linarith
  have hprob : expect p k (fun idx => if ε < f (X idx) - f xs then 1 else 0) ≤
      expect p k G / (7 * ε / 8) := by
    calc
      expect p k (fun idx => if ε < f (X idx) - f xs then 1 else 0) ≤
          expect p k (fun idx => if 7 * ε / 8 < G idx then 1 else 0) := by
        apply expect_mono p hp k
        intro idx
        by_cases h : ε < f (X idx) - f xs
        · simp only [h, hbad idx h, if_true, le_refl]
        · simp only [h, if_false]
          split_ifs <;> norm_num
      _ ≤ _ := expect_markov p hp k G hG _ (by positivity)
  have hA : 0 < S L 1 + (n : ℝ) * μ := by positivity
  have hD : 0 < (n : ℝ) + 4 * t := by positivity
  have hratio : μ / (S L 1 + (n : ℝ) * μ) = 1 / ((n : ℝ) + 4 * t) := by
    apply (div_eq_div_iff (ne_of_gt hA) (ne_of_gt hD)).2
    dsimp [t]
    rw [hμ]
    field_simp [ne_of_gt hε, ne_of_gt hRpos]
    ring
  have hexpect := regularized_expected_gap hn f hconv L hL sharp hsharp x0 xs hxs R hRpos hR μ hμpos k
  have hbadbound : expect p k (fun idx => if ε < f (X idx) - f xs then 1 else 0) ≤
      (4 * t / 7) * (1 - 1 / ((n : ℝ) + 4 * t)) ^ k := by
    calc
      _ ≤ expect p k G / (7 * ε / 8) := hprob
      _ ≤ ((1 - μ / (S L 1 + (n : ℝ) * μ)) ^ k * (S L 1 * R ^ 2 / 2)) /
          (7 * ε / 8) := div_le_div_of_nonneg_right hexpect (by positivity)
      _ = _ := by rw [hratio]; dsimp [t]; ring
  have hk' : 2 * ((n : ℝ) + 4 * t) *
      (Real.log (1 / (1 - β)) + Real.log (1 / 2 + 2 * t)) ≤ k := by
    have h4 : 4 * t = 4 * S L 1 * R ^ 2 / ε := by dsimp [t]; ring
    have h2 : 2 * t = 2 * S L 1 * R ^ 2 / ε := by dsimp [t]; ring
    rw [h4, h2]
    exact hk
  have hlast := hbadbound.trans (printed_decay_bound n hn t ht β hβ0 hβ1 k hk')
  have hcomp : expect p k (fun idx => if f (X idx) - f xs ≤ ε then 1 else 0) +
      expect p k (fun idx => if ε < f (X idx) - f xs then 1 else 0) = 1 := by
    rw [← expect_add]
    convert expect_const p hp1 k 1 using 1
    congr 1
    funext idx
    by_cases h : f (X idx) - f xs ≤ ε
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  change β ≤ expect p k (fun idx => if f (X idx) - f xs ≤ ε then 1 else 0)
  linarith

end RCDHighProbProof

open Classical

namespace NesterovRCD.HighProb

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem theorem4 (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs)
    (R : ℝ) (hRpos : 0 < R) (hR : NesterovRCD.Sublinear.LevelRadiusLE f L 0 x0 R)
    (ε β : ℝ) (hε : 0 < ε) (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : ℝ) (hμ : μ = ε / (4 * R ^ 2)) (k : ℕ)
    (hk : 2 * ((n : ℝ) + 4 * NesterovRCD.Sublinear.S L 1 * R ^ 2 / ε) *
        (Real.log (1 / (1 - β)) + Real.log (1 / 2 + 2 * NesterovRCD.Sublinear.S L 1 * R ^ 2 / ε)) ≤ k) :
    β ≤ NesterovRCD.Sublinear.expect (NesterovRCD.Sublinear.prob (fun i => L i + μ) 1) k
      (fun idx => if f (NesterovRCD.Sublinear.rcdm (fReg f L μ x0) (fun i => L i + μ) sharp x0 k idx) - f xs ≤ ε
        then 1 else 0) := by
  exact RCDHighProbProof.high_probability_bound hn f hconv L hL sharp hsharp x0 xs hxs R hRpos hR ε β hε hβ0 hβ1 μ hμ k hk

end NesterovRCD.HighProb

open NesterovRCD.HighProb


variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem solution (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs)
    (R : ℝ) (hRpos : 0 < R) (hR : NesterovRCD.Sublinear.LevelRadiusLE f L 0 x0 R)
    (ε β : ℝ) (hε : 0 < ε) (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : ℝ) (hμ : μ = ε / (4 * R ^ 2)) (k : ℕ)
    (hk : 2 * ((n : ℝ) + 4 * NesterovRCD.Sublinear.S L 1 * R ^ 2 / ε) *
        (Real.log (1 / (1 - β)) + Real.log (1 / 2 + 2 * NesterovRCD.Sublinear.S L 1 * R ^ 2 / ε)) ≤ k) :
    β ≤ NesterovRCD.Sublinear.expect (NesterovRCD.Sublinear.prob (fun i => L i + μ) 1) k
      (fun idx => if f (NesterovRCD.Sublinear.rcdm (fReg f L μ x0) (fun i => L i + μ) sharp x0 k idx) - f xs ≤ ε
        then 1 else 0) := by
  exact NesterovRCD.HighProb.theorem4 hn f hconv L hL sharp hsharp x0 xs hxs R hRpos hR ε β hε hβ0 hβ1 μ hμ k hk
