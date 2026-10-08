-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.cutoff2
-- status  : ACCEPTED   (prove)
-- author  : @sorry_not_sorry
-- created : 2026-10-08T07:50:31.844169+00:00
-- url     : https://prove2.me/submissions/c93a051d-5921-47e4-a3d2-30b85b525140

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib
import Theorems.Thm_HlawkaGaussian_gauss_integral_scaling
import Theorems.Thm_HlawkaGaussian_gaussAbsConst_pos
import Theorems.Thm_Hlawka1D_hlawka_1d

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open MeasureTheory ProbabilityTheory

/-!
# The sharp diagonal Hlawka constant at `p = 2` is `1`

Proof via Hlawka's one-dimensional inequality integrated against the
standard Gaussian measure (which is provably the right tool here: the
box-SOS method is powerless at `p = 2`).

* Lemma A (real case): on a real inner product space, each norm is
  `C⁻¹` times the Gaussian integral of `|⟪·, w⟫|`; the seven integrals
  combine into one whose pointwise integrand is nonnegative by the 1D
  Hlawka inequality.
* Lemma B (complex case): transport along the real-linear isometry
  `(x i) ↦ ((x i).re, (x i).im)`.
* Sharpness: the triple `(1, 1, -2)` on `Fin 1 → ℂ` attains ratio `1`.
-/

/-- Pushforward of the standard Gaussian along the inner-product functional. -/
theorem map_innerSL_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (v : E) :
    (stdGaussian E).map (innerSL ℝ v)
      = gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  have h0 : IsGaussian (stdGaussian E) := inferInstance
  rw [h0.map_eq_gaussianReal (innerSL ℝ v), integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

/-- Integrability of `w ↦ |⟪v, w⟫|` against the standard Gaussian, via the
pushforward: it is the pullback of `|·|`, integrable against every 1D
Gaussian. -/
theorem integrable_abs_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (v : E) :
    Integrable (fun w => |inner (𝕜 := ℝ) v w|) (stdGaussian E) := by
  have hmap : (stdGaussian E).map (innerSL ℝ v)
      = gaussianReal 0 (‖v‖ ^ 2).toNNReal := map_innerSL_stdGaussian v
  have h1 : Integrable (fun t : ℝ => |t|) (gaussianReal 0 (‖v‖ ^ 2).toNNReal) :=
    ((memLp_id_gaussianReal 1).integrable (by simp)).abs
  rw [← hmap] at h1
  have hAES : AEStronglyMeasurable (fun t : ℝ => |t|)
      ((stdGaussian E).map ⇑(innerSL ℝ v)) :=
    continuous_abs.aestronglyMeasurable
  have h2 : Integrable ((fun t : ℝ => |t|) ∘ ⇑(innerSL ℝ v)) (stdGaussian E) :=
    (integrable_map_measure hAES (innerSL ℝ v).continuous.aemeasurable).mp h1
  have heq : (fun w : E => |inner (𝕜 := ℝ) v w|)
      = (fun t : ℝ => |t|) ∘ ⇑(innerSL ℝ v) := by
    funext w
    simp only [Function.comp_apply]
    have hcoe : inner (𝕜 := ℝ) v w = ⇑(innerSL ℝ v) w := by simp
    rw [hcoe]
  rw [heq]
  exact h2

/-- Each norm is `C⁻¹` times its Gaussian integral. -/
theorem norm_eq_inv_mul_gauss {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (v : E) :
    ‖v‖ = (∫ t, |t| ∂(gaussianReal 0 1))⁻¹
      * ∫ w, |inner (𝕜 := ℝ) v w| ∂(stdGaussian E) := by
  have hCne : (∫ t, |t| ∂(gaussianReal 0 1)) ≠ 0 :=
    ne_of_gt HlawkaGaussian.gaussAbsConst_pos
  rw [HlawkaGaussian.gauss_integral_scaling v, eq_inv_mul_iff_mul_eq₀ hCne]
  exact mul_comm _ _

/-- Hlawka's inequality at `p = 2` on a real inner product space. -/
theorem hlawka_two_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (x y z : E) :
    ‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖ ≥ ‖x + y‖ + ‖y + z‖ + ‖z + x‖ := by
  have hC : 0 < ∫ t, |t| ∂(gaussianReal 0 1) := HlawkaGaussian.gaussAbsConst_pos
  have hCinv : 0 ≤ (∫ t, |t| ∂(gaussianReal 0 1))⁻¹ := inv_nonneg.mpr hC.le
  have hint : ∀ v : E, Integrable (fun w => |inner (𝕜 := ℝ) v w|) (stdGaussian E) :=
    fun v => integrable_abs_inner_stdGaussian v
  -- Pointwise nonnegativity from the one-dimensional Hlawka inequality.
  have hF : ∀ w : E, 0 ≤ (|inner (𝕜:=ℝ) x w| + |inner (𝕜:=ℝ) y w| + |inner (𝕜:=ℝ) z w|
      + |inner (𝕜:=ℝ) (x+y+z) w|)
      - (|inner (𝕜:=ℝ) (x+y) w| + |inner (𝕜:=ℝ) (y+z) w| + |inner (𝕜:=ℝ) (z+x) w|) := by
    intro w
    have h1 := Hlawka1D.hlawka_1d (inner (𝕜:=ℝ) x w) (inner (𝕜:=ℝ) y w) (inner (𝕜:=ℝ) z w)
    simp only [inner_add_left] at h1 ⊢
    linarith
  -- The seven integrals combine into the integral of the pointwise deficit.
  -- (Intermediate `Integrable` hypotheses are stated in beta-reduced form to
  -- match what `integral_add` produces.)
  have hxy : Integrable (fun a : E => |inner (𝕜:=ℝ) x a| + |inner (𝕜:=ℝ) y a|)
      (stdGaussian E) := (hint x).add (hint y)
  have hxyz : Integrable (fun a : E => |inner (𝕜:=ℝ) x a| + |inner (𝕜:=ℝ) y a|
      + |inner (𝕜:=ℝ) z a|) (stdGaussian E) := hxy.add (hint z)
  have hxyz4 : Integrable (fun a : E => |inner (𝕜:=ℝ) x a| + |inner (𝕜:=ℝ) y a|
      + |inner (𝕜:=ℝ) z a| + |inner (𝕜:=ℝ) (x+y+z) a|) (stdGaussian E) :=
    hxyz.add (hint (x + y + z))
  have hyz : Integrable (fun a : E => |inner (𝕜:=ℝ) (x+y) a| + |inner (𝕜:=ℝ) (y+z) a|)
      (stdGaussian E) := (hint (x + y)).add (hint (y + z))
  have hyzx : Integrable (fun a : E => |inner (𝕜:=ℝ) (x+y) a| + |inner (𝕜:=ℝ) (y+z) a|
      + |inner (𝕜:=ℝ) (z+x) a|) (stdGaussian E) := hyz.add (hint (z + x))
  have hcomb : ∫ w, |inner (𝕜:=ℝ) x w| ∂(stdGaussian E)
        + ∫ w, |inner (𝕜:=ℝ) y w| ∂(stdGaussian E)
        + ∫ w, |inner (𝕜:=ℝ) z w| ∂(stdGaussian E)
        + ∫ w, |inner (𝕜:=ℝ) (x+y+z) w| ∂(stdGaussian E)
        - (∫ w, |inner (𝕜:=ℝ) (x+y) w| ∂(stdGaussian E)
          + ∫ w, |inner (𝕜:=ℝ) (y+z) w| ∂(stdGaussian E)
          + ∫ w, |inner (𝕜:=ℝ) (z+x) w| ∂(stdGaussian E))
      = ∫ w, ((|inner (𝕜:=ℝ) x w| + |inner (𝕜:=ℝ) y w| + |inner (𝕜:=ℝ) z w|
          + |inner (𝕜:=ℝ) (x+y+z) w|)
          - (|inner (𝕜:=ℝ) (x+y) w| + |inner (𝕜:=ℝ) (y+z) w|
            + |inner (𝕜:=ℝ) (z+x) w|)) ∂(stdGaussian E) := by
    rw [← integral_add (hint x) (hint y), ← integral_add hxy (hint z),
      ← integral_add hxyz (hint (x + y + z)),
      ← integral_add (hint (x + y)) (hint (y + z)),
      ← integral_add hyz (hint (z + x)),
      ← integral_sub hxyz4 hyzx]
  rw [norm_eq_inv_mul_gauss x, norm_eq_inv_mul_gauss y, norm_eq_inv_mul_gauss z,
    norm_eq_inv_mul_gauss (x + y + z), norm_eq_inv_mul_gauss (x + y),
    norm_eq_inv_mul_gauss (y + z), norm_eq_inv_mul_gauss (z + x), ge_iff_le]
  have hnn : 0 ≤ (∫ t, |t| ∂(gaussianReal 0 1))⁻¹ *
      ∫ w, ((|inner (𝕜:=ℝ) x w| + |inner (𝕜:=ℝ) y w| + |inner (𝕜:=ℝ) z w|
        + |inner (𝕜:=ℝ) (x+y+z) w|)
        - (|inner (𝕜:=ℝ) (x+y) w| + |inner (𝕜:=ℝ) (y+z) w|
          + |inner (𝕜:=ℝ) (z+x) w|)) ∂(stdGaussian E) :=
    mul_nonneg hCinv (integral_nonneg (fun w => hF w))
  have hdiff : (∫ t, |t| ∂(gaussianReal 0 1))⁻¹ *
        (∫ w, |inner (𝕜:=ℝ) x w| ∂(stdGaussian E) + ∫ w, |inner (𝕜:=ℝ) y w| ∂(stdGaussian E)
          + ∫ w, |inner (𝕜:=ℝ) z w| ∂(stdGaussian E)
          + ∫ w, |inner (𝕜:=ℝ) (x+y+z) w| ∂(stdGaussian E))
        - (∫ t, |t| ∂(gaussianReal 0 1))⁻¹ *
        (∫ w, |inner (𝕜:=ℝ) (x+y) w| ∂(stdGaussian E)
          + ∫ w, |inner (𝕜:=ℝ) (y+z) w| ∂(stdGaussian E)
          + ∫ w, |inner (𝕜:=ℝ) (z+x) w| ∂(stdGaussian E))
      = (∫ t, |t| ∂(gaussianReal 0 1))⁻¹ *
        ∫ w, ((|inner (𝕜:=ℝ) x w| + |inner (𝕜:=ℝ) y w| + |inner (𝕜:=ℝ) z w|
          + |inner (𝕜:=ℝ) (x+y+z) w|)
          - (|inner (𝕜:=ℝ) (x+y) w| + |inner (𝕜:=ℝ) (y+z) w|
            + |inner (𝕜:=ℝ) (z+x) w|)) ∂(stdGaussian E) := by
    rw [← mul_sub, hcomb]
  linarith

/-- `DiagonalConstruction.lpNorm 2` on `ι → ℝ` is the `PiLp 2` norm. -/
theorem hlawka_two_real_lpNorm {ι : Type*} [Fintype ι] (x y z : ι → ℝ) :
    DiagonalConstruction.lpNorm 2 x + DiagonalConstruction.lpNorm 2 y + DiagonalConstruction.lpNorm 2 z + DiagonalConstruction.lpNorm 2 (x + y + z)
      ≥ DiagonalConstruction.lpNorm 2 (x + y) + DiagonalConstruction.lpNorm 2 (y + z) + DiagonalConstruction.lpNorm 2 (z + x) := by
  have e : ∀ v : ι → ℝ, DiagonalConstruction.lpNorm 2 v = ‖WithLp.toLp (2:ENNReal) v‖ := by
    intro v
    simp only [DiagonalConstruction.lpNorm]
    rw [PiLp.norm_eq_sum (by norm_num : (0:ℝ) < (2:ENNReal).toReal)]
    simp
  rw [e x, e y, e z, e (x + y + z), e (x + y), e (y + z), e (z + x)]
  simp only [WithLp.toLp_add]
  exact hlawka_two_real _ _ _

/-- Realification: view `x : Fin n → ℂ` as a real vector indexed by `Fin n × Fin 2`. -/
def Xc {n : ℕ} (x : Fin n → ℂ) : Fin n × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then (x p.1).re else (x p.1).im

/-- Realification preserves addition. -/
theorem Xc_add {n : ℕ} (u v : Fin n → ℂ) : Xc (u + v) = Xc u + Xc v := by
  funext ⟨i, k⟩
  by_cases h : k = 0
  · simp [Xc, h, Pi.add_apply, Complex.add_re]
  · simp [Xc, h, Pi.add_apply, Complex.add_im]

/-- Realification preserves `DiagonalConstruction.lpNorm 2`. -/
theorem Xc_norm {n : ℕ} (x : Fin n → ℂ) : DiagonalConstruction.lpNorm 2 (Xc x) = DiagonalConstruction.lpNorm 2 x := by
  unfold DiagonalConstruction.lpNorm
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  have h0 : Xc x (i, 0) = (x i).re := by simp [Xc]
  have h1 : Xc x (i, 1) = (x i).im := by simp [Xc, show (1:Fin 2) ≠ 0 by decide]
  rw [h0, h1, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast,
    Real.rpow_natCast, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have hsq : ∀ z : ℂ, ‖z‖^2 = z.re^2 + z.im^2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  exact (hsq (x i)).symm

/-- Hlawka's inequality at `p = 2` for complex coordinate vectors. -/
theorem hlawka_two_complex {n : ℕ} (x y z : Fin n → ℂ) :
    DiagonalConstruction.lpNorm 2 x + DiagonalConstruction.lpNorm 2 y + DiagonalConstruction.lpNorm 2 z + DiagonalConstruction.lpNorm 2 (x + y + z)
      ≥ DiagonalConstruction.lpNorm 2 (x + y) + DiagonalConstruction.lpNorm 2 (y + z) + DiagonalConstruction.lpNorm 2 (z + x) := by
  have h := hlawka_two_real_lpNorm (Xc x) (Xc y) (Xc z)
  rw [← Xc_add x y, ← Xc_add y z, ← Xc_add z x, ← Xc_add (x + y) z] at h
  rw [Xc_norm x, Xc_norm y, Xc_norm z, Xc_norm (x + y + z), Xc_norm (x + y),
    Xc_norm (y + z), Xc_norm (z + x)] at h
  exact h

/-- `DiagonalConstruction.lpNorm 2` of a constant vector on `Fin 1`. -/
theorem lpNorm_two_const {c : ℂ} : DiagonalConstruction.lpNorm 2 (fun _ : Fin 1 => c) = ‖c‖ := by
  unfold DiagonalConstruction.lpNorm
  rw [Fin.sum_univ_one, ← Real.rpow_mul (norm_nonneg c),
    show (2:ℝ) * ((1:ℝ) / 2) = 1 by norm_num, Real.rpow_one]

/-- Sharpness: no constant below `1` works, witnessed by `(1, 1, -2)`. -/
theorem sharpness_key (C : ℝ)
    (hC : HasHlawkaConstant (DiagonalConstruction.lpNorm 2 : (Fin 1 → ℂ) → ℝ) C) : 1 ≤ C := by
  have h := hC (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => (-2:ℂ))
  simp only [tripleGap, pairGapSum, pairGap] at h
  have e1 : (fun _ : Fin 1 => (1:ℂ)) + (fun _ : Fin 1 => (1:ℂ)) + (fun _ : Fin 1 => (-2:ℂ))
      = (fun _ : Fin 1 => (0:ℂ)) := by
    funext i
    simp only [Pi.add_apply]
    norm_num
  have e2 : (fun _ : Fin 1 => (1:ℂ)) + (fun _ : Fin 1 => (1:ℂ))
      = (fun _ : Fin 1 => (2:ℂ)) := by
    funext i
    simp only [Pi.add_apply]
    norm_num
  have e3 : (fun _ : Fin 1 => (1:ℂ)) + (fun _ : Fin 1 => (-2:ℂ))
      = (fun _ : Fin 1 => (-1:ℂ)) := by
    funext i
    simp only [Pi.add_apply]
    norm_num
  rw [e1, e2, e3] at h
  simp only [lpNorm_two_const] at h
  have hn2 : ‖(-2:ℂ)‖ = 2 := by
    rw [norm_neg]
    exact Complex.norm_ofNat (n := 2)
  have h2c : ‖(2:ℂ)‖ = 2 := Complex.norm_ofNat (n := 2)
  have hn1 : ‖(-1:ℂ)‖ = 1 := by
    rw [norm_neg, norm_one]
  simp only [norm_one, norm_zero, hn2, h2c, hn1] at h
  norm_num at h
  have h4 : (1:ℝ) * 4 ≤ C * 4 := by linarith
  exact le_of_mul_le_mul_right h4 (by norm_num)

/-- The sharp diagonal Hlawka constant at `p = 2` is `1`. -/
theorem solution :
    IsLeast {C : ℝ | ∀ n : ℕ, HasHlawkaConstant (DiagonalConstruction.lpNorm 2 : (Fin n → ℂ) → ℝ) C} 1 := by
  refine ⟨?_, ?_⟩
  · -- Membership: `1` is a Hlawka constant (real Gaussian proof + complex transfer).
    intro n x y z
    have h := hlawka_two_complex x y z
    rw [ge_iff_le] at h
    show tripleGap (DiagonalConstruction.lpNorm 2) x y z
      ≤ 1 * pairGapSum (DiagonalConstruction.lpNorm 2) x y z
    rw [tripleGap, pairGapSum, pairGap, pairGap, pairGap, one_mul]
    -- Manual linear arithmetic: the difference equals `(A+B+C+D) - (E+F+G) ≥ 0`.
    rw [← sub_nonneg]
    have hdiff : (DiagonalConstruction.lpNorm 2 x + DiagonalConstruction.lpNorm 2 y
          - DiagonalConstruction.lpNorm 2 (x + y)
          + (DiagonalConstruction.lpNorm 2 x + DiagonalConstruction.lpNorm 2 z
            - DiagonalConstruction.lpNorm 2 (x + z))
          + (DiagonalConstruction.lpNorm 2 y + DiagonalConstruction.lpNorm 2 z
            - DiagonalConstruction.lpNorm 2 (y + z)))
          - (DiagonalConstruction.lpNorm 2 x + DiagonalConstruction.lpNorm 2 y
            + DiagonalConstruction.lpNorm 2 z - DiagonalConstruction.lpNorm 2 (x + y + z))
        = (DiagonalConstruction.lpNorm 2 x + DiagonalConstruction.lpNorm 2 y
            + DiagonalConstruction.lpNorm 2 z + DiagonalConstruction.lpNorm 2 (x + y + z))
          - (DiagonalConstruction.lpNorm 2 (x + y) + DiagonalConstruction.lpNorm 2 (y + z)
            + DiagonalConstruction.lpNorm 2 (z + x)) := by ring
    rw [hdiff]
    exact sub_nonneg.mpr h
  · -- Minimality: the `(1, 1, -2)` witness shows no smaller constant works.
    intro C hC
    exact sharpness_key C (hC 1)
