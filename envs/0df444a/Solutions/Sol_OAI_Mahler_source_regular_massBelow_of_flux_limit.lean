-- Prove2me | solution 1 for OAI.Mahler.source_regular_massBelow_of_flux_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:49:21.605806+00:00
-- url     : https://prove2.me/submissions/826d504f-501c-412b-b2a2-91a26d540af3

import Mathlib
import Definitions.Def_OAISMh000
import Theorems.Thm_OAI_Mahler_source_punctured_scaled_extDeriv

section
-- module Solutions.OAIS_Mahler.Mahler_ShellRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma continuous_radiusSq (n : ℕ) : Continuous (radiusSq (n := n)) := by
  unfold radiusSq; fun_prop

lemma isCompact_coordClosedBall (n : ℕ) (R : ℝ) : IsCompact (coordClosedBall n R) := by
  have hs : coordClosedBall n R ⊆ Icc (fun _ => -|R|) (fun _ => |R|) := by
    intro x hx
    have hi (i : Fin n) : |x i| ≤ |R| := by
      have hsum : x i ^ 2 ≤ radiusSq x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have hx' : radiusSq x ≤ R^2 := hx
      nlinarith [sq_abs (x i), sq_abs R, abs_nonneg (x i), abs_nonneg R]
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_le (continuous_radiusSq n) continuous_const) hs

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ComplexCoordinates
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory WithLp
open scoped ENNReal
namespace MahlerStokes

lemma complexCoordinates_apply (n : ℕ) (x : Fin (n*2) → ℝ) (i : Fin n) :
    complexCoordinates n x i = ⟨x (finProdFinEquiv (i,0)), x (finProdFinEquiv (i,1))⟩ := rfl

/-- Euclidean volume is transported with factor exactly one. -/
theorem measurePreserving_complexCoordinates (n : ℕ) :
    MeasurePreserving (complexCoordinates n) := by
  exact (interleavedEuclidean n).measurePreserving.comp
    (PiLp.volume_preserving_toLp (Fin (n*2)))

/-- The coordinate squared radius is exactly the complex Euclidean squared norm. -/
theorem norm_complexCoordinates_sq (n : ℕ) (x : Fin (n*2) → ℝ) :
    ‖complexCoordinates n x‖^2 = radiusSq x := by
  rw [radiusSq_eq_euclidean_norm_sq]
  exact congrArg (fun t : ℝ => t^2) ((interleavedEuclidean n).norm_map _)

/-- The coordinate map sends the ordered real basis to x_i,y_i without a
sign or scale change. -/
theorem complexCoordinates_basis (n : ℕ) (i : Fin n) (b : Fin 2) :
    complexCoordinates n (Pi.single (finProdFinEquiv (i,b)) 1) =
      EuclideanSpace.single i (if b = 0 then 1 else Complex.I) := by
  ext j : 1
  rw [complexCoordinates_apply]
  by_cases hij : i = j
  · subst j
    fin_cases b <;> simp <;> rfl
  · have hji : j ≠ i := Ne.symm hij
    fin_cases b <;> simp [hji] <;> rfl

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeAlgebra
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedgePower_smul (c : ℂ) (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePower (c • a) k = c ^ k • wedgePower a k := by
  induction k with
  | zero =>
    ext v
    change (1 : ℂ) = c ^ 0 * 1
    simp
  | succ k ih =>
    change wedge (c • a) (wedgePower (c • a) k) = c ^ (k + 1) • wedge a (wedgePower a k)
    simp only [ih, wedge_smul_left, wedge_smul_right, smul_smul]
    rw [pow_succ]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ContinuousWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma contDiffAt_continuousWedge [FiniteDimensional ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : WithTop ℕ∞}
    {a : X → E [⋀^ι]→L[ℝ] ℂ} {b : X → E [⋀^κ]→L[ℝ] ℂ} {x : X}
    (ha : ContDiffAt ℝ r a x) (hb : ContDiffAt ℝ r b x) :
    ContDiffAt ℝ r (fun y => continuousWedge (a y) (b y)) x := by
  let W := continuousWedgeCLM (E := E) (ι := ι) (κ := κ)
  have hw := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r)
    (E := E [⋀^ι]→L[ℝ] ℂ)
    (F := (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ) W
  have hw' := hw.contDiffAt.comp x ha
  exact hw'.clm_apply hb

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CovectorVolume
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct BigOperators

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Exterior multiplication of simple forms concatenates their covectors,
with the exact shuffle normalization and slot order. -/
theorem wedge_covectorVolume (l : ι → T →ₗ[ℝ] ℂ) (r : κ → T →ₗ[ℝ] ℂ) :
    wedge (covectorVolume l) (covectorVolume r) = covectorVolume (Sum.elim l r) := by
  unfold covectorVolume wedge
  rw [← MultilinearMap.domCoprod_alternization,
    ← LinearMap.compMultilinearMap_alternatization]
  congr 1
  ext v
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    LinearMap.mul'_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

lemma wedge_sum_left {J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : T [⋀^κ]→ₗ[ℝ] ℂ) : wedge (∑ j ∈ s, a j) b = ∑ j ∈ s, wedge (a j) b := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.sum_tmul, map_sum]

lemma wedge_sum_right {J : Type*} (s : Finset J) (a : T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : J → T [⋀^κ]→ₗ[ℝ] ℂ) : wedge a (∑ j ∈ s, b j) = ∑ j ∈ s, wedge a (b j) := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.tmul_sum, map_sum]

/-- A change of covectors multiplies the associated volume by its determinant. -/
theorem covectorVolume_linearCombination (C : Matrix ι ι ℂ) (l : ι → T →ₗ[ℝ] ℂ) :
    covectorVolume (fun j => ∑ k, C j k • l k) = C.det • covectorVolume l := by
  ext v
  rw [covectorVolume_apply]
  change Matrix.det (fun i j => (∑ k, C j k • l k) (v i)) = C.det * covectorVolume l v
  rw [covectorVolume_apply]
  let M : Matrix ι ι ℂ := fun i j => l j (v i)
  have hm : ((fun i j => (∑ k, C j k • l k) (v i)) : Matrix ι ι ℂ) =
      M * C.transpose := by
    ext i j
    change (∑ k, C j k • l k) (v i) = ∑ index, l index (v i) * C j index
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hm, Matrix.det_mul, Matrix.det_transpose, mul_comm]
  rfl

lemma covectorVolume_reindex_apply (l : ι → T →ₗ[ℝ] ℂ) (e : κ ≃ ι) (v : κ → T) :
    covectorVolume (l ∘ e) v = covectorVolume l (v ∘ e.symm) := by
  rw [covectorVolume_apply, covectorVolume_apply]
  convert (Matrix.det_submatrix_equiv_self e (fun i j => l j (v (e.symm i)))) using 1 <;>
    first | rfl | (congr 1; ext i j; change _ = l (e j) (v (e.symm (e i))); simp)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorAlternatization
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Equiv Fin
namespace Mahler
noncomputable section

lemma orderedInsertPermutation_sign {n : ℕ} (p : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (orderedInsertPermutation p σ) = (-1)^p.val * Equiv.Perm.sign σ := by
  simp [orderedInsertPermutation, Equiv.Perm.sign_trans, Equiv.Perm.decomposeFin.symm_sign,
    Fin.sign_cycleRange]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Full alternatization of a distinguished derivative slot contains each
term of the usual exterior derivative exactly n! times. -/
theorem alternatization_rawUncurry {n : ℕ} (D : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    (rawUncurry D).alternatization = n.factorial • AlternatingMap.alternatizeUncurryFin D := by
  ext v
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, rawUncurry_apply]
  rw [← Equiv.sum_comp (orderedPermutationEquiv n), Fintype.sum_prod_type]
  simp only [orderedPermutationEquiv_apply, orderedInsertPermutation_zero,
    orderedInsertPermutation_succ, orderedInsertPermutation_sign]
  have hp (p : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
      ((-1 : ℤˣ)^p.val * Equiv.Perm.sign σ) •
        D (v p) (fun i => v (p.succAbove (σ i))) =
      (-1 : ℤ)^p.val • D (v p) (p.removeNth v) := by
    have he := (D (v p)).map_perm (p.removeNth v) σ
    change D (v p) (fun i => v (p.succAbove (σ i))) =
      Equiv.Perm.sign σ • D (v p) (p.removeNth v) at he
    rw [he, smul_smul, mul_assoc, Int.units_mul_self, mul_one]
    simp [Units.smul_def]
  simp_rw [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    AlternatingMap.smul_apply, AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum]

/-- General expansion: alternating all slots of an uncurried multilinear
map is the signed sum of the alternatizations in its trailing slots. -/
theorem alternatization_uncurryLeft_apply {n : ℕ}
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => E) ℂ) (v : Fin (n+1) → E) :
    D.uncurryLeft.alternatization v =
      ∑ p : Fin (n+1), (-1 : ℤ)^p.val • (D (v p)).alternatization (p.removeNth v) := by
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, LinearMap.uncurryLeft_apply]
  rw [← Equiv.sum_comp (orderedPermutationEquiv n), Fintype.sum_prod_type]
  simp only [orderedPermutationEquiv_apply, orderedInsertPermutation_zero,
    orderedInsertPermutation_sign, MultilinearMap.alternatization_apply, Finset.smul_sum,
    MultilinearMap.domDomCongr_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro σ _
  change ((-1 : ℤˣ)^p.val * Equiv.Perm.sign σ) •
    D (v p) (fun i => v (orderedInsertPermutation p σ i.succ)) =
      (-1 : ℤ)^p.val • Equiv.Perm.sign σ • D (v p) (fun i => v (p.succAbove (σ i)))
  simp [Units.smul_def, mul_assoc]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HolomorphicRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Set Metric Filter MeasureTheory
open scoped Topology Interval

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex Schwarz estimate gives a local bound on the full derivative,
from first-order holomorphicity alone. -/
lemma locally_bounded_fderiv {f : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    ∃ r > 0, ∃ C ≥ 0, ball x r ⊆ U ∧
      ∀ y ∈ ball x r, ‖fderiv ℂ f y‖ ≤ C := by
  have hc := (hf x hx).differentiableAt (hU.mem_nhds hx) |>.continuousAt
  have hn : U ∩ f ⁻¹' ball (f x) 1 ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) (hc.preimage_mem_nhds (ball_mem_nhds _ zero_lt_one))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, 2 / (r / 2), by positivity, ?_, ?_⟩
  · intro y hy
    exact (hsub (ball_subset_ball (by linarith) hy)).1
  · intro y hy
    have hball : ball y (r / 2) ⊆ ball x r := by
      intro z hz
      have := dist_triangle z y x
      rw [mem_ball] at hy hz ⊢
      linarith
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      (hf.mono (hball.trans (fun z hz => (hsub hz).1))) ?_ (by positivity)
    intro z hz
    have hzy := (hsub (hball hz)).2
    have hyx := (hsub (ball_subset_ball (by linarith) hy)).2
    rw [mem_closedBall]
    have := dist_triangle (f z) (f x) (f y)
    change dist (f z) (f x) < 1 at hzy
    change dist (f y) (f x) < 1 at hyx
    rw [dist_comm (f x) (f y)] at this
    linarith

variable [FiniteDimensional ℂ E]

/-- Differentiability of a Cauchy integral in an ambient finite-dimensional
complex parameter. The derivative bound is obtained locally by Schwarz. -/
lemma differentiable_cauchy_parameter {f : E → ℂ} {U : Set E} {x v : E}
    {R C r : ℝ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : 0 < R) (hr : 0 < r) (hv : r * ‖v‖ < R / 2)
    (hsub : ball x R ⊆ U)
    (hb : ∀ y ∈ ball x R, ‖fderiv ℂ f y‖ ≤ C) :
    DifferentiableAt ℂ
      (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) x := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let c : ℝ → ℂ := circleMap 0 r
  let k : ℝ → ℂ := fun t => (c t * I) * (1 / c t ^ 2)
  have hc : Continuous c := continuous_circleMap _ _
  have hcn (t : ℝ) : ‖c t‖ = r := by simp [c, abs_of_pos hr]
  have hcz (t : ℝ) : c t ≠ 0 := by
    intro h
    have := hcn t
    rw [h, norm_zero] at this
    linarith
  have hk : Continuous k := (hc.mul continuous_const).mul
    (continuous_const.div (hc.pow 2) (fun t => pow_ne_zero _ (hcz t)))
  have hkn (t : ℝ) : ‖k t‖ = 1 / r := by
    simp [k, norm_pow, hcn, norm_I]
    field_simp
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      y + c t • v ∈ ball x R := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have htri := norm_add_le (y - x) (c t • v)
    have he : y + c t • v - x = (y - x) + c t • v := by abel
    rw [he]
    rw [norm_smul, hcn] at htri
    linarith
  have hcont {y : E} (hy : y ∈ ball x (R / 2)) :
      Continuous (fun t => k t * f (y + c t • v)) := by
    apply hk.mul
    exact hf.continuousOn.comp_continuous (by fun_prop) (fun t => hsub (hshift hy t))
  let F' : E → ℝ → E →L[ℂ] ℂ := fun y t => k t • fderiv ℂ f (y + c t • v)
  have hd {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      HasFDerivAt (fun y => k t * f (y + c t • v)) (F' y t) y := by
    have hf' := ((hf _ (hsub (hshift hy t))).differentiableAt
      (hU.mem_nhds (hsub (hshift hy t)))).hasFDerivAt
    simpa only [F', Function.comp_apply, id_eq, ContinuousLinearMap.comp_id] using
      (hf'.comp y ((hasFDerivAt_id y).add_const (c t • v))).const_mul (k t)
  have hm : AEStronglyMeasurable (F' x) := by
    apply Measurable.aestronglyMeasurable
    exact hk.measurable.smul ((measurable_fderiv ℂ f).comp
      (show Continuous (fun t => x + c t • v) by fun_prop).measurable)
  have hint := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := fun y t => k t * f (y + c t • v)) (F' := F')
    (bound := fun _ => (1 / r) * C) (ball_mem_nhds x (by positivity : 0 < R / 2))
    (by filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
        exact (hcont hy).aestronglyMeasurable)
    ((hcont (mem_ball_self (by positivity))).intervalIntegrable _ _)
    hm.restrict
    (by filter_upwards [] with t ht y hy
        simp only [F', norm_smul, hkn]
        exact mul_le_mul_of_nonneg_left (hb _ (hshift hy t)) (by positivity))
    (intervalIntegrable_const)
    (by filter_upwards [] with t ht y hy; exact hd hy t)
  have he : (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) =
      (fun y => ∫ t in (0 : ℝ)..2 * Real.pi, k t * f (y + c t • v)) := by
    funext y
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul, c, k, mul_assoc]
  rw [he]
  exact hint.differentiableAt

/-- A directional component of the ambient first derivative is holomorphic.
Only first-order holomorphicity on the open domain is assumed. -/
theorem differentiableAt_fderiv_apply_of_open {f : E → ℂ} {U : Set E} {x v : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  obtain ⟨R, hR, C, hC, hsub, hb⟩ := locally_bounded_fderiv hU hx hf
  let r := (R / 2) / (‖v‖ + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hv : r * ‖v‖ < R / 2 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < ‖v‖ + 1)]
    nlinarith
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) {z : ℂ}
      (hz : z ∈ closedBall 0 r) : y + z • v ∈ U := by
    apply hsub
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have hzn : ‖z‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
    have htri := norm_add_le (y - x) (z • v)
    have he : y + z • v - x = (y - x) + z • v := by abel
    rw [he]
    rw [norm_smul] at htri
    have hmul := mul_le_mul_of_nonneg_right hzn (norm_nonneg v)
    linarith
  have he : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x]
      (fun y => (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) := by
    filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
    have hl : Differentiable ℂ (fun z : ℂ => y + z • v) := by fun_prop
    have hline : DifferentiableOn ℂ (fun z : ℂ => f (y + z • v)) (closedBall 0 r) :=
      hf.comp hl.differentiableOn (fun z hz => hshift hy hz)
    have hcauchy := hline.deriv_eq_smul_circleIntegral hr
    have hfy : DifferentiableAt ℂ f y :=
      (hf y (by simpa using hshift hy (mem_closedBall_self hr.le))).differentiableAt
        (hU.mem_nhds (by simpa using hshift hy (mem_closedBall_self hr.le)))
    have hl' : HasDerivAt (fun z : ℂ => y + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have hfy' : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using hfy.hasFDerivAt
    have hder := hfy'.comp_hasDerivAt 0 hl'
    change HasDerivAt (fun z : ℂ => f (y + z • v)) (fderiv ℂ f y v) 0 at hder
    rw [hder.deriv] at hcauchy
    simp only [sub_zero, smul_eq_mul] at hcauchy ⊢
    rw [hcauchy, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  exact ((differentiable_cauchy_parameter hU hf hR hr hv hsub hb).const_mul
    (2 * Real.pi * I : ℂ)⁻¹).congr_of_eventuallyEq he

/-- Holomorphic functions on open finite-dimensional complex domains are C^k
for every finite k. Smoothness is derived, not added to the hypotheses. -/
theorem contDiffOn_nat_of_differentiableOn_open {U : Set E} (hU : IsOpen U)
    (k : ℕ) {f : E → ℂ} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ k f U := by
  induction k generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiffOn_succ_of_fderiv_apply hf (by simp)
    intro v
    have hd : DifferentiableOn ℂ (fun y => fderiv ℂ f y v) U :=
      fun y hy => (differentiableAt_fderiv_apply_of_open hU hy hf).differentiableWithinAt
    apply (ih hd).congr
    intro y hy
    rw [fderivWithin_of_isOpen hU hy]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_Hessian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {E : Type*} [normedAddCommGroupE : NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

lemma dz_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dz f x v = fderiv ℂ f x v := by
  rw [dz, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v - I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  have hi := I_mul_I
  calc
    _ = (fderiv ℂ f x v - (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [hi]; ring

lemma dbar_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dbar f x v = 0 := by
  rw [dbar, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v + I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  calc
    _ = (fderiv ℂ f x v + (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [I_mul_I]; ring

omit isScalarTowerRealComplexE in
lemma dz_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dz (fun y => conj (f y)) x v = conj (dbar f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dz, h.fderiv]
  simp [dbar, map_add, map_mul, conj_I, map_ofNat, sub_eq_add_neg]

omit isScalarTowerRealComplexE in
lemma dbar_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dbar (fun y => conj (f y)) x v = conj (dz f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dbar, h.fderiv]
  simp [dz, map_sub, map_mul, conj_I, map_ofNat]

omit isScalarTowerRealComplexE in
lemma dz_mul [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dz (fun y => f y * g y) x v = dz f x v * g x + f x * dz g x v := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dz, h.fderiv]
  simp [dz]
  ; ring

omit isScalarTowerRealComplexE in
lemma dbar_mul [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbar (fun y => f y * g y) x v = dbar f x v * g x + f x * dbar g x v := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dbar, h.fderiv]
  simp [dbar]
  ; ring

omit isScalarTowerRealComplexE in
lemma dz_sum [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    dz (fun y => ∑ j, f j y) x v = ∑ j, dz (f j) x v := by
  have h : HasFDerivAt (fun y => ∑ j, f j y) (∑ j, fderiv ℝ (f j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hf j).hasFDerivAt)
  rw [dz, h.fderiv]
  simp only [dz, sum_apply, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

omit isScalarTowerRealComplexE in
lemma dbar_sum [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    dbar (fun y => ∑ j, f j y) x v = ∑ j, dbar (f j) x v := by
  have h : HasFDerivAt (fun y => ∑ j, f j y) (∑ j, fderiv ℝ (f j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hf j).hasFDerivAt)
  rw [dbar, h.fderiv]
  simp only [dbar, sum_apply, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

omit isScalarTowerRealComplexE in
lemma dz_clog [IsScalarTower ℝ ℂ E] {u : E → ℂ} {x v : E} (hu : DifferentiableAt ℝ u x)
    (hp : u x ∈ slitPlane) :
    dz (fun y => Complex.log (u y)) x v = dz u x v / u x := by
  have h := ((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x hu.hasFDerivAt
  change HasFDerivAt (fun y => Complex.log (u y)) _ x at h
  rw [dz, h.fderiv]
  simp [dz, ContinuousLinearMap.comp_apply, div_eq_mul_inv]
  ; ring

omit isScalarTowerRealComplexE in
lemma dbar_div [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hn : g x ≠ 0) :
    dbar (fun y => f y / g y) x v =
      (dbar f x v * g x - f x * dbar g x v) / g x ^ 2 := by
  have hi := ((hasDerivAt_inv hn).hasFDerivAt.restrictScalars ℝ).comp x hg.hasFDerivAt
  change HasFDerivAt (fun y => (g y)⁻¹) _ x at hi
  have h := hf.hasFDerivAt.mul hi
  simp only [Pi.mul_def] at h
  simp only [div_eq_mul_inv]
  rw [dbar, h.fderiv]
  simp [dbar]
  ; field_simp [hn]
  ; ring

variable {ι : Type*} [Fintype ι]

omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma tau_nonneg [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : 0 ≤ tau f x :=
  Finset.sum_nonneg (fun j _ => normSq_nonneg (f j x))
omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma energy_eq_tau [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : energy f x = (tau f x : ℂ) := by
  simp [energy, tau, Complex.normSq_eq_conj_mul_self]
lemma logTau_eq (f : ι → E → ℂ) : logTau f = fun x => Complex.log (energy f x) := by
  funext x
  rw [logTau, energy_eq_tau, Complex.ofReal_log (tau_nonneg f x)]

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma diff_conj [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x :=
  Complex.conjCLE.differentiableAt.comp x hf

lemma differentiable_energy {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) : DifferentiableAt ℝ (energy f) x := by
  exact DifferentiableAt.fun_sum (fun j _ =>
    (diff_conj ((hf j).restrictScalars ℝ)).mul ((hf j).restrictScalars ℝ))

lemma dz_energy {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) :
    dz (energy f) x v = ∑ j, conj (f j x) * fderiv ℂ (f j) x v := by
  change dz (fun y => ∑ j, conj (f j y) * f j y) x v = _
  rw [dz_sum (f := fun j y => conj (f j y) * f j y) (fun j => (diff_conj ((hf j).restrictScalars ℝ)).mul
    ((hf j).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dz_mul (diff_conj ((hf j).restrictScalars ℝ)) ((hf j).restrictScalars ℝ),
    dz_conj ((hf j).restrictScalars ℝ), dbar_holomorphic (hf j), dz_holomorphic (hf j)]
  simp

lemma dbar_energy {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) :
    dbar (energy f) x v = ∑ j, conj (fderiv ℂ (f j) x v) * f j x := by
  change dbar (fun y => ∑ j, conj (f j y) * f j y) x v = _
  rw [dbar_sum (f := fun j y => conj (f j y) * f j y) (fun j => (diff_conj ((hf j).restrictScalars ℝ)).mul
    ((hf j).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dbar_mul (diff_conj ((hf j).restrictScalars ℝ)) ((hf j).restrictScalars ℝ),
    dbar_conj ((hf j).restrictScalars ℝ), dz_holomorphic (hf j), dbar_holomorphic (hf j)]
  simp

lemma dz_logTau {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    dz (logTau f) x v = (∑ j, conj (f j x) * fderiv ℂ (f j) x v) / (tau f x : ℂ) := by
  rw [logTau_eq, dz_clog (differentiable_energy hf) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht), dz_energy hf,
    energy_eq_tau]

omit isScalarTowerRealComplexE in
lemma dbar_congr_nhds [IsScalarTower ℝ ℂ E] {u q : E → ℂ} {x v : E} (h : u =ᶠ[𝓝 x] q) :
    dbar u x v = dbar q x v := by
  simp only [dbar, h.fderiv_eq]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_Positivity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators ComplexOrder
local notation "conj" => starRingEnd ℂ
namespace Mahler
variable {ι : Type*} [Fintype ι]

lemma finite_cauchy_schwarz (a b : ι → ℂ) :
    normSq (∑ j, conj (a j) * b j) ≤
      (∑ j, normSq (a j)) * (∑ j, normSq (b j)) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.norm_sq_eq,
    mul_pow, Complex.normSq_eq_norm_sq, mul_comm] using hs

lemma pairing_conj (a b : ι → ℂ) : conj (pairing a b) = pairing b a := by
  simp [pairing, map_sum, map_mul, mul_comm]
lemma pairing_self (a : ι → ℂ) : pairing a a = (sizeSq a : ℂ) := by
  simp [pairing, sizeSq, Complex.normSq_eq_conj_mul_self]
lemma logKernel_conj (a b c : ι → ℂ) : conj (logKernel a b c) = logKernel a c b := by
  simp only [logKernel, map_div₀, map_sub, map_mul, map_pow, pairing_conj, conj_ofReal]
  ring

lemma logKernel_diagonal (a b : ι → ℂ) :
    logKernel a b b = (((sizeSq a * sizeSq b - normSq (pairing a b)) /
      sizeSq a ^ 2 : ℝ) : ℂ) := by
  rw [logKernel, pairing_self]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, pairing_conj]
  ring

lemma logKernel_nonneg (a b : ι → ℂ) : 0 ≤ logKernel a b b := by
  rw [logKernel_diagonal, Complex.nonneg_iff]
  simp only [ofReal_re, ofReal_im, and_true]
  exact div_nonneg (sub_nonneg.mpr (finite_cauchy_schwarz a b)) (sq_nonneg _)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_MatrixHessian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Complex Matrix
open scoped BigOperators ComplexOrder
local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {ι κ : Type*} [Fintype ι] [fintypeKappa : Fintype κ]

lemma pairing_sum_right (a : ι → ℂ) (B : κ → ι → ℂ) :
    pairing a (fun j => ∑ k, B k j) = ∑ k, pairing a (B k) := by
  simp only [pairing, Finset.mul_sum]
  rw [Finset.sum_comm]
lemma pairing_sum_left (a : ι → ℂ) (B : κ → ι → ℂ) :
    pairing (fun j => ∑ k, B k j) a = ∑ k, pairing (B k) a := by
  simp only [pairing, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
lemma pairing_mul_right (a b : ι → ℂ) (r : ℂ) :
    pairing a (fun j => r * b j) = r * pairing a b := by
  simp [pairing, Finset.mul_sum, mul_left_comm]
lemma pairing_mul_left (a b : ι → ℂ) (r : ℂ) :
    pairing (fun j => r * b j) a = conj r * pairing b a := by
  simp [pairing, map_mul, Finset.mul_sum, mul_assoc]

lemma logKernel_sum_right (a b : ι → ℂ) (B : κ → ι → ℂ) :
    logKernel a b (fun j => ∑ k, B k j) = ∑ k, logKernel a b (B k) := by
  simp only [logKernel, pairing_sum_right, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
lemma logKernel_sum_left (a b : ι → ℂ) (B : κ → ι → ℂ) :
    logKernel a (fun j => ∑ k, B k j) b = ∑ k, logKernel a (B k) b := by
  simp only [logKernel, pairing_sum_left, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
lemma logKernel_mul_right (a b c : ι → ℂ) (r : ℂ) :
    logKernel a b (fun j => r * c j) = r * logKernel a b c := by
  simp only [logKernel, pairing_mul_right]
  ring
lemma logKernel_mul_left (a b c : ι → ℂ) (r : ℂ) :
    logKernel a (fun j => r * b j) c = conj r * logKernel a b c := by
  simp only [logKernel, pairing_mul_left]
  ring

omit fintypeKappa in
lemma kernelMatrix_hermitian [Fintype κ] (a : ι → ℂ) (B : κ → ι → ℂ) :
    (kernelMatrix a B).IsHermitian := by
  ext i j
  exact logKernel_conj a (B j) (B i)

lemma kernelMatrix_quadratic (a : ι → ℂ) (B : κ → ι → ℂ) (c : κ → ℂ) :
    star c ⬝ᵥ (kernelMatrix a B *ᵥ c) =
      logKernel a (fun k => ∑ i, c i * B i k) (fun k => ∑ i, c i * B i k) := by
  rw [logKernel_sum_left]
  simp_rw [logKernel_mul_left, logKernel_sum_right, logKernel_mul_right]
  simp [dotProduct, mulVec, kernelMatrix, mul_comm]

lemma kernelMatrix_posSemidef (a : ι → ℂ) (B : κ → ι → ℂ) :
    (kernelMatrix a B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (kernelMatrix_hermitian a B)
  intro c
  rw [kernelMatrix_quadratic]
  exact logKernel_nonneg _ _

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma differentiableAt_oneForm [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) : DifferentiableAt ℝ (oneForm a) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x ha

/-- Exterior differentiation uses the usual unnormalized alternating sum. -/
lemma extDeriv_oneForm {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (v w : E) :
    extDeriv (oneForm a) x ![v, w] =
      fderiv ℝ (fun y => a y w) x v - fderiv ℝ (fun y => a y v) x w := by
  rw [extDeriv_apply (differentiableAt_oneForm ha)]
  simp [Fin.sum_univ_two, Fin.removeNth, oneForm_apply, sub_eq_add_neg]

/-- C^2 regularity of log tau follows from first-order holomorphicity. -/
lemma contDiffAt_logTau_of_open [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) : ContDiffAt ℝ 2 (logTau f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  have he : ContDiffAt ℝ 2 (energy f) x := by
    apply ContDiffAt.sum
    intro j hj
    exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := 2) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht)).restrict_scalars ℝ).comp x he

lemma differentiableAt_dcLinear {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact ((hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)).differentiableAt (by norm_num)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_OpenHessian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Complex Matrix
open scoped BigOperators Topology ComplexOrder
local notation "conj" => starRingEnd ℂ
namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [fintypeKappa : Fintype κ]

lemma diff_numerator_of_open {f : ι → E → ℂ} {U : Set E} {x v : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) : DifferentiableAt ℝ (numerator f v) x := by
  exact DifferentiableAt.fun_sum (fun j _ =>
    (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ)).mul
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ))

lemma dbar_numerator_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    dbar (numerator f v) x w = ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  change dbar (fun y => ∑ j, conj (f j y) * fderiv ℂ (f j) y v) x w = _
  rw [dbar_sum (f := fun j y => conj (f j y) * fderiv ℂ (f j) y v) (fun j => (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ)).mul
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dbar_mul (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ))
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ),
    dbar_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ),
    dz_holomorphic ((hf j x hx).differentiableAt (hU.mem_nhds hx)), dbar_holomorphic (differentiableAt_fderiv_apply_of_open hU hx (hf j))]
  simp

/-- Actual mixed Wirtinger derivative of the squared norm. -/
theorem mixed_energy_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    dbar (fun y => dz (energy f) y v) x w =
      ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j, DifferentiableAt ℂ (f j) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)
  have he : (fun y => dz (energy f) y v) =ᶠ[𝓝 x] numerator f v := by
    filter_upwards [hh] with y hy
    exact dz_energy (fun j => hy j)
  rw [dbar_congr_nhds he, dbar_numerator_of_open hU hx hf]

/-- Actual mixed derivative of the real logarithm, on the positive tau domain. -/
theorem mixed_logTau_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    dbar (fun y => dz (logTau f) y v) x w =
      ((tau f x : ℂ) * (∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v)
        - (∑ j, conj (f j x) * fderiv ℂ (f j) x v) *
          (∑ j, conj (fderiv ℂ (f j) x w) * f j x)) / (tau f x : ℂ)^2 := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j, DifferentiableAt ℂ (f j) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)
  have hc : ContinuousAt (tau f) x := by
    have h := Complex.continuous_re.continuousAt.comp
      (differentiable_energy (fun j => ((hf j x hx).differentiableAt (hU.mem_nhds hx)))).continuousAt
    simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using h
  have hp : ∀ᶠ y in 𝓝 x, 0 < tau f y := hc.eventually (lt_mem_nhds ht)
  have he : (fun y => dz (logTau f) y v) =ᶠ[𝓝 x]
      (fun y => numerator f v y / energy f y) := by
    filter_upwards [hh, hp] with y hy hty
    simpa only [numerator, energy_eq_tau] using dz_logTau
      (v := v) (fun j => hy j) hty
  rw [dbar_congr_nhds he, dbar_div (diff_numerator_of_open hU hx hf)
    (differentiable_energy (fun j => ((hf j x hx).differentiableAt (hU.mem_nhds hx)))) (by
      rw [energy_eq_tau]; exact_mod_cast ne_of_gt ht),
    dbar_numerator_of_open hU hx hf, dbar_energy (fun j => ((hf j x hx).differentiableAt (hU.mem_nhds hx))), energy_eq_tau]
  simp only [numerator]
  ring

omit fintypeKappa in
lemma complexHessian_logTau_eq_of_open [Fintype κ] {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    complexHessian (logTau f) x e =
      kernelMatrix (fun j => f j x) (fun i j => fderiv ℂ (f j) x (e i)) := by
  ext i j
  exact mixed_logTau_of_open hU hx hf ht

theorem complexHessian_logTau_posSemidef_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    (complexHessian (logTau f) x e).PosSemidef := by
  rw [complexHessian_logTau_eq_of_open e hU hx hf ht]
  exact kernelMatrix_posSemidef _ _

omit fintypeKappa in
lemma complexHessian_energy_eq_gram_of_open [Fintype κ] {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    complexHessian (energy f) x e = (jacobian f x e)ᴴ * jacobian f x e := by
  ext i j
  exact mixed_energy_of_open hU hx hf

theorem complexHessian_energy_posSemidef_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    (complexHessian (energy f) x e).PosSemidef := by
  rw [complexHessian_energy_eq_gram_of_open e hU hx hf]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sourceHessian_logTau_det_nonneg_of_open [DecidableEq κ]
    {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    0 ≤ (sourceHessian (logTau f) x e).det := by
  rw [sourceHessian, Matrix.det_transpose]
  exact (complexHessian_logTau_posSemidef_of_open e hU hx hf ht).det_nonneg

theorem sourceHessian_energy_det_nonneg_of_open [DecidableEq κ]
    {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    0 ≤ (sourceHessian (energy f) x e).det := by
  rw [sourceHessian, Matrix.det_transpose]
  exact (complexHessian_energy_posSemidef_of_open e hU hx hf).det_nonneg

/-- The mass density is nonnegative under the mass hypotheses. -/
theorem MassHypotheses.massDensity_nonneg {n N m : ℕ} {U : Set (ComplexEuclidean n)}
    {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : MassHypotheses n N m U f G) {z : ComplexEuclidean n} (hz : z ∈ U) :
    0 ≤ massDensity f z := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact (Complex.nonneg_iff.mp (sourceHessian_energy_det_nonneg_of_open _
    h.open_domain hz h.holomorphic)).1

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorHessian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
/-- Actual mixed derivatives expanded in the real second Fréchet derivative. -/
lemma mixed_second_real [IsScalarTower ℝ ℂ E] {u : E → ℂ} {x v w : E} (hu : ContDiffAt ℝ 2 u x) :
    dbar (fun y => dz u y v) x w =
      (fderiv ℝ (fderiv ℝ u) x w v - I * fderiv ℝ (fderiv ℝ u) x w (I • v) +
        I * fderiv ℝ (fderiv ℝ u) x (I • w) v +
        fderiv ℝ (fderiv ℝ u) x (I • w) (I • v)) / 4 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hv := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hiv := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (I • v) x)
  have hdz := (hv.sub (hiv.const_mul I)).mul_const (2 : ℂ)⁻¹
  change HasFDerivAt (fun y => dz u y v) _ x at hdz
  rw [dbar, hdz.fderiv]
  simp
  linear_combination -(fderiv ℝ (fderiv ℝ u) x (I • w) (I • v) / 4) * I_mul_I

/-- The exterior derivative of the d^c one-form is exactly the
antisymmetrized mixed Hessian, with coefficient i/2. -/
theorem extDeriv_dc_mixed {u : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    extDeriv (oneForm (dcLinear u)) x ![v, w] =
      (I / 2) * (dbar (fun y => dz u y v) x w - dbar (fun y => dz u y w) x v) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hdc (a b : E) : fderiv ℝ (fun y => dcLinear u y a) x b =
      (-1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ u) x b (I • a) := by
    have he : (fun y => dcLinear u y a) =
        (fun y => (-1 / 4 : ℂ) * fderiv ℝ u y (I • a)) := by
      funext y
      simp [dcLinear]
    rw [he]
    have hh := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (I • a) x)).const_mul (-1 / 4 : ℂ)
    rw [hh.fderiv]
    simp
  rw [extDeriv_oneForm (differentiableAt_dcLinear hu), hdc, hdc,
    mixed_second_real hu, mixed_second_real hu]
  have hs := hu.isSymmSndFDerivAt (by simp)
  rw [hs.eq w v, hs.eq (I • w) v, hs.eq (I • v) w, hs.eq (I • w) (I • v)]
  linear_combination -((fderiv ℝ (fderiv ℝ u) x v (I • w) -
    fderiv ℝ (fderiv ℝ u) x w (I • v)) / 4) * I_mul_I

/-- The exterior two-form identity, with no added regularity. -/
theorem extDeriv_dc_logTau_of_open [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (v w : E) :
    extDeriv (oneForm (dcLinear (logTau f))) x ![v, w] =
      (I / 2) *
        (logKernel (fun j => f j x) (fun j => fderiv ℂ (f j) x w)
          (fun j => fderiv ℂ (f j) x v) -
         logKernel (fun j => f j x) (fun j => fderiv ℂ (f j) x v)
          (fun j => fderiv ℂ (f j) x w)) := by
  rw [extDeriv_dc_mixed (contDiffAt_logTau_of_open hU hx hf ht)]
  rw [mixed_logTau_of_open hU hx hf ht, mixed_logTau_of_open hU hx hf ht]
  rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

lemma pairedCovectors_succ {k : ℕ} (p : Fin (k+1) → Fin 2 → T →ₗ[ℝ] ℂ) :
    pairedCovectors p = Sum.elim (p 0) (pairedCovectors (fun i => p i.succ)) := by
  funext s
  cases s <;> rfl

/-- Expand the actual shuffle power as a sum of determinants of selected
covector pairs. This identity includes every term, also repeated selections. -/
theorem wedgePower_sum_pairs {J : Type*} [Fintype J]
    (p : J → Fin 2 → T →ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePower (∑ j, covectorVolume (p j)) k =
      ∑ q : Fin k → J, covectorVolume (pairedCovectors (fun i => p (q i))) := by
  classical
  induction k with
  | zero =>
    ext v
    change (1 : ℂ) = (∑ q : Fin 0 → J, covectorVolume
      (pairedCovectors (fun index => p (q index)))) v
    simp only [Fintype.sum_unique]
    rw [covectorVolume_apply]
    let : IsEmpty (WedgePowerSlots 0) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty.symm
  | succ k ih =>
    change wedge (∑ j, covectorVolume (p j)) (wedgePower (∑ j, covectorVolume (p j)) k) = _
    rw [ih, wedge_sum_left]
    simp_rw [wedge_sum_right, wedge_covectorVolume]
    simp_rw [pairedCovectors_succ]
    trans ∑ q : J × (Fin k → J), covectorVolume (Sum.elim (p q.1) (pairedCovectors (fun i => p (q.2 i))))
    · exact (Fintype.sum_prod_type (fun q : J × (Fin k → J) => covectorVolume (Sum.elim (p q.1) (pairedCovectors (fun i => p (q.2 i)))))).symm
    · apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => J))
      intro q
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      rw [show wedgePowerSlotsDecidableEq (k+1) =
        (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) from Subsingleton.elim _ _]
      rfl

lemma pairPermutation_sign {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (pairPermutation σ) = 1 := by
  simp [pairPermutation, Equiv.Perm.sign_prodCongrLeft]

lemma pairedCovectors_perm {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (Fin k)) :
    pairedCovectors (fun i => p (σ i)) = pairedCovectors p ∘ pairPermutation σ := by
  funext s
  simp [pairedCovectors, pairPermutation, Equiv.prodCongrLeft]

lemma covectorVolume_pairs_perm {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (Fin k)) :
    covectorVolume (pairedCovectors (fun i => p (σ i))) = covectorVolume (pairedCovectors p) := by
  ext v
  rw [pairedCovectors_perm, covectorVolume_apply, covectorVolume_apply]
  change Matrix.det ((Matrix.of (fun row column => pairedCovectors p column (v row))).submatrix
    id (pairPermutation σ)) = _
  rw [Matrix.det_permute', pairPermutation_sign]
  simp only [Units.val_one, Int.cast_one, one_mul]

lemma covectorVolume_pairs_noninjective {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (q : Fin k → Fin k) (hq : ¬Function.Injective q) :
    covectorVolume (pairedCovectors (fun i => p (q i))) = 0 := by
  classical
  obtain ⟨i,j,hij,hne⟩ : ∃ i j, q i = q j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, exists_prop] using hq
  ext v
  rw [covectorVolume_apply]
  apply Matrix.det_zero_of_column_eq
    (i := (pairSlotEquiv k).symm (i,0)) (j := (pairSlotEquiv k).symm (j,0))
  · intro h
    have h' := congrArg (fun s => (pairSlotEquiv k s).1) h
    exact hne (by simpa using h')
  · intro s
    simp [pairedCovectors, hij]

/-- The n-fold shuffle power of n simple two-forms is n! times their
interleaved covector volume. Repeated choices vanish; pair permutations have
positive sign. This yields the factorial in the normalization. -/
theorem wedgePower_sum_pairs_top (k : ℕ) (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ) :
    wedgePower (∑ j, covectorVolume (p j)) k =
      (k.factorial : ℂ) • covectorVolume (pairedCovectors p) := by
  classical
  rw [wedgePower_sum_pairs]
  calc
    (∑ q : Fin k → Fin k, covectorVolume (pairedCovectors (fun i => p (q i)))) =
        ∑ q : Fin k → Fin k with Function.Bijective q,
          covectorVolume (pairedCovectors (fun i => p (q i))) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun q _ hq => ?_)).symm
      apply covectorVolume_pairs_noninjective p q
      intro hi
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, Finite.surjective_of_injective hi⟩)
    _ = ∑ σ : Equiv.Perm (Fin k), covectorVolume (pairedCovectors (fun i => p (σ i))) :=
      Finset.sum_bij (fun q h => Equiv.ofBijective q (Finset.mem_filter.1 h).2)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => by injection h)
        (fun b _ => ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, b.bijective⟩,
          Equiv.coe_fn_injective rfl⟩) (fun _ _ => rfl)
    _ = (k.factorial : ℂ) • covectorVolume (pairedCovectors p) := by
      simp only [covectorVolume_pairs_perm, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
      exact (Nat.cast_smul_eq_nsmul ℂ k.factorial _).symm

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LevelForms
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

lemma contDiffAt_energy_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    ContDiffAt ℝ 2 (energy f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  apply ContDiffAt.sum
  intro j hj
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_NormExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma alternatingMap_sum_apply {T : Type*} [AddCommGroup T] [Module ℝ T]
    {ι J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ) (v : ι → T) :
    (∑ j ∈ s, a j) v = ∑ j ∈ s, a j v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    change a j v + (∑ i ∈ s, a i) v = _
    rw [ih]

/-- The normalization is positive on dx_1,dy_1,..., not just determined up
to an unspecified orientation sign. -/
theorem interleavedVolume_basis (n : ℕ) : interleavedVolume n interleavedBasis = 1 := by
  rw [interleavedVolume, covectorVolume_apply]
  have hm : Matrix.of (fun a b : WedgePowerSlots n =>
      pairedCovectors (coordinatePair (n := n)) b (interleavedBasis a)) =
      (1 : Matrix (WedgePowerSlots n) (WedgePowerSlots n) ℂ) := by
    ext a b
    obtain ⟨i,α,ha⟩ : ∃ i α, pairSlotEquiv n a = (i,α) := ⟨_,_,rfl⟩
    obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv n b = (j,β) := ⟨_,_,rfl⟩
    have hab : a = b ↔ i = j ∧ α = β := by
      rw [← (pairSlotEquiv n).injective.eq_iff, ha, hb, Prod.mk.injEq]
    fin_cases α <;> fin_cases β <;>
      simp [pairedCovectors, interleavedBasis, ha, hb, coordinatePair,
        Matrix.of_apply, Matrix.one_apply, hab, eq_comm] <;> split_ifs <;> simp_all
  rw [hm, Matrix.det_one]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_MatrixExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma hessianCovectorMatrix_det {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    (hessianCovectorMatrix H).det = (-2 * I) ^ n * H.det := by
  rw [hessianCovectorMatrix, Matrix.det_fromBlocks_one₁₁]
  have hm : (-I) • H - H * (I • (1 : Matrix (Fin n) (Fin n) ℂ)) = (-2 * I) • H := by
    simp only [Matrix.mul_smul, Matrix.mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hm, Matrix.det_smul, Fintype.card_fin]

lemma pairedCoordinates_split (n : ℕ) : pairedCovectors (coordinatePair (n := n)) =
    splitCoordinates n ∘ pairSplitEquiv n := by
  funext s
  obtain ⟨i,j,h⟩ : ∃ i j, pairSlotEquiv n s = (i,j) := ⟨_,_,rfl⟩
  fin_cases j <;> simp [pairedCovectors, coordinatePair, pairSplitEquiv, splitCoordinates, h]

lemma hessianPair_split {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    pairedCovectors (hessianPair H) =
      (fun i => ∑ j, hessianCovectorMatrix H i j • splitCoordinates n j) ∘ pairSplitEquiv n := by
  funext s
  obtain ⟨i,j,h⟩ : ∃ i j, pairSlotEquiv n s = (i,j) := ⟨_,_,rfl⟩
  fin_cases j <;>
    simp [pairedCovectors, hessianPair, pairSplitEquiv, hessianCovectorMatrix,
      splitCoordinates, h, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg,
      Finset.sum_add_distrib, smul_smul, mul_comm]

lemma hessianPair_volume {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    covectorVolume (pairedCovectors (hessianPair H)) =
      ((-2 * I)^n * H.det) • interleavedVolume n := by
  ext v
  rw [hessianPair_split, covectorVolume_reindex_apply, covectorVolume_linearCombination]
  change (hessianCovectorMatrix H).det *
    covectorVolume (splitCoordinates n) (v ∘ (pairSplitEquiv n).symm) = _
  rw [← covectorVolume_reindex_apply, ← pairedCoordinates_split, hessianCovectorMatrix_det]
  rfl

/-- The full n! det(H) normalization, with the i/2 convention and the
positively oriented interleaved real volume form. -/
theorem matrixTwoForm_top {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    wedgePower (matrixTwoForm H) n =
      ((n.factorial : ℂ) * H.det) • interleavedVolume n := by
  rw [matrixTwoForm, wedgePower_smul, wedgePower_sum_pairs_top, hessianPair_volume,
    smul_smul, smul_smul]
  have hc : (I/2) * (-2*I) = 1 := by linear_combination -I_mul_I
  congr 1
  calc
    (I/2)^n * (n.factorial : ℂ) * ((-2*I)^n * H.det) =
        (n.factorial : ℂ) * H.det * ((I/2)*(-2*I))^n := by rw [mul_pow (I/2) (-2*I)]; ac_rfl
    _ = (n.factorial : ℂ) * H.det := by rw [hc, one_pow, mul_one]

lemma hessianPair_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (v : ComplexEuclidean n) : hessianPair H i 0 v = v i := by
  change ((v i).re : ℂ) + I * ((v i).im : ℂ) = v i
  apply Complex.ext <;> simp

lemma hessianPair_one {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (v : ComplexEuclidean n) : hessianPair H i 1 v = ∑ j, H i j * star (v j) := by
  change (∑ j, H i j • (realCoordinate j - I • imagCoordinate j)) v = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    realCoordinate_apply, imagCoordinate_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Complex.ext <;> simp

lemma matrixTwoForm_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : ComplexEuclidean n) :
    matrixTwoForm H ![v,w] = (I/2) * (matrixPairing H w v - matrixPairing H v w) := by
  simp only [matrixTwoForm, AlternatingMap.smul_apply, smul_eq_mul, alternatingMap_sum_apply,
    covectorVolume_apply, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    hessianPair_zero, hessianPair_one, matrixPairing]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_OpenExteriorNormalization
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma linearMap_coordinate_expansion {n : ℕ} (A : ComplexEuclidean n →L[ℂ] ℂ)
    (v : ComplexEuclidean n) : A v = ∑ i, v i * A (coordinateDirection i) := by
  have hv : v = ∑ i, v i • coordinateDirection i := by
    ext j
    simp [coordinateDirection, Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  simp [map_smul, smul_eq_mul]

lemma pairing_coordinate_expansion {n : ℕ} {J : Type*} [Fintype J]
    (A : J → ComplexEuclidean n →L[ℂ] ℂ) (w v : ComplexEuclidean n) :
    pairing (fun j => A j w) (fun j => A j v) =
      matrixPairing (fun i j => pairing (fun a => A a (coordinateDirection j))
        (fun a => A a (coordinateDirection i))) w v := by
  have he (z : ComplexEuclidean n) : (fun j => A j z) =
      (fun j => ∑ i, z i * A j (coordinateDirection i)) :=
    funext (fun j => linearMap_coordinate_expansion (A j) z)
  rw [he w, he v, pairing_sum_left]
  simp_rw [pairing_mul_left, pairing_sum_right, pairing_mul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (starRingEnd ℂ) (w j) = star (w j) from rfl]
  ring

lemma logKernel_coordinate_expansion {n : ℕ} {J : Type*} [Fintype J]
    (a : J → ℂ) (A : J → ComplexEuclidean n →L[ℂ] ℂ) (w v : ComplexEuclidean n) :
    logKernel a (fun j => A j w) (fun j => A j v) =
      matrixPairing (fun i j => logKernel a (fun b => A b (coordinateDirection j))
        (fun b => A b (coordinateDirection i))) w v := by
  have he (z : ComplexEuclidean n) : (fun j => A j z) =
      (fun j => ∑ i, z i * A j (coordinateDirection i)) :=
    funext (fun j => linearMap_coordinate_expansion (A j) z)
  rw [he w, he v, logKernel_sum_left]
  simp_rw [logKernel_mul_left, logKernel_sum_right, logKernel_mul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (starRingEnd ℂ) (w j) = star (w j) from rfl]
  ring

variable {n : ℕ} {J : Type*} [Fintype J] {f : J → ComplexEuclidean n → ℂ}
  {U : Set (ComplexEuclidean n)} {x : ComplexEuclidean n}

lemma extDeriv_energy_matrix_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap =
      matrixTwoForm (sourceHessian (energy f) x coordinateDirection) := by
  have hmat : sourceHessian (energy f) x coordinateDirection =
      (fun i j => pairing (fun a => fderiv ℂ (f a) x (coordinateDirection j))
        (fun a => fderiv ℂ (f a) x (coordinateDirection i))) := by
    ext i j
    exact mixed_energy_of_open hU hx hf
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  change extDeriv (oneForm (dcLinear (energy f))) x v = _
  rw [hv, extDeriv_dc_mixed (contDiffAt_energy_of_open hU hx hf), matrixTwoForm_apply, hmat,
    mixed_energy_of_open hU hx hf, mixed_energy_of_open hU hx hf]
  change (I/2) * (pairing (fun j => fderiv ℂ (f j) x (v 1)) (fun j => fderiv ℂ (f j) x (v 0)) -
    pairing (fun j => fderiv ℂ (f j) x (v 0)) (fun j => fderiv ℂ (f j) x (v 1))) = _
  rw [pairing_coordinate_expansion, pairing_coordinate_expansion]

lemma extDeriv_logTau_matrix_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap =
      matrixTwoForm (sourceHessian (logTau f) x coordinateDirection) := by
  have hmat : sourceHessian (logTau f) x coordinateDirection =
      (fun i j => logKernel (fun a => f a x)
        (fun a => fderiv ℂ (f a) x (coordinateDirection j))
        (fun a => fderiv ℂ (f a) x (coordinateDirection i))) := by
    ext i j
    exact mixed_logTau_of_open hU hx hf ht
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  change extDeriv (oneForm (dcLinear (logTau f))) x v = _
  rw [hv, extDeriv_dc_logTau_of_open hU hx hf ht, matrixTwoForm_apply, hmat,
    logKernel_coordinate_expansion, logKernel_coordinate_expansion]

/-- The top exterior normalization, under
open-domain first-order holomorphicity, with no additional smoothness premise. -/
theorem extDeriv_energy_top_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    wedgePower (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap n =
      ((n.factorial : ℂ) * (sourceHessian (energy f) x coordinateDirection).det) • interleavedVolume n := by
  rw [extDeriv_energy_matrix_of_open hU hx hf, matrixTwoForm_top]

theorem extDeriv_logTau_top_of_open (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    wedgePower (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap n =
      ((n.factorial : ℂ) * (sourceHessian (logTau f) x coordinateDirection).det) • interleavedVolume n := by
  rw [extDeriv_logTau_matrix_of_open hU hx hf ht, matrixTwoForm_top]

/-- The density already used by the exact mass target is the real coefficient
of the actual top exterior form in the positive Euclidean coordinate frame. -/
theorem MassHypotheses.massDensity_eq_topForm {N m : ℕ}
    {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : MassHypotheses n N m U f G) (hx : x ∈ U) :
    massDensity f x =
      (wedgePower (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap n
        interleavedBasis).re := by
  rw [extDeriv_energy_top_of_open h.open_domain hx h.holomorphic]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, interleavedVolume_basis, mul_one]
  simp only [massDensity, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The actual shuffle normalization is exactly full alternatization of a
raw tensor product; no factorial is silently inserted. -/
theorem rawProduct_alternatization (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    (rawProduct a b).alternatization = wedge a.alternatization b.alternatization := by
  unfold rawProduct wedge
  rw [← MultilinearMap.domCoprod_alternization,
    ← LinearMap.compMultilinearMap_alternatization]

theorem rawPower_alternatization (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) (k : ℕ) :
    (rawPower B k).alternatization = wedgePower B.alternatization k := by
  induction k with
  | zero =>
    change ((AlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℂ)).toMultilinearMap).alternatization =
      AlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℂ)
    rw [AlternatingMap.coe_alternatization]
    exact one_nsmul _
  | succ k ih =>
    rw [show wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) from Subsingleton.elim _ _]
    change (rawProduct B (rawPower B k)).alternatization = _
    rw [rawProduct_alternatization, ih]
    rfl

lemma rawCovector_alternatization (a : E →ₗ[ℝ] ℂ) :
    (rawCovector a).alternatization = AlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) a := by
  ext v
  simp [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

theorem rawBoundary_alternatization (a : E →ₗ[ℝ] ℂ)
    (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) (k : ℕ) :
    (rawBoundary a B k).alternatization =
      wedge (AlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) a)
        (wedgePower B.alternatization k) := by
  rw [rawBoundary, rawProduct_alternatization, rawCovector_alternatization, rawPower_alternatization]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawAlternatingCalculus
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Equiv
namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Full alternatization commutes with any explicit slot identification. -/
theorem raw_alternatization_reindex
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ) (e : ι ≃ κ) :
    (a.domDomCongr e).alternatization = a.alternatization.domDomCongr e := by
  ext v
  rw [MultilinearMap.alternatization_apply]
  rw [← Equiv.sum_comp e.permCongr]
  simp only [AlternatingMap.domDomCongr_apply, MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro σ _
  simp [Equiv.Perm.sign_permCongr, MultilinearMap.domDomCongr_apply,
    Equiv.permCongr_apply, Function.comp_def]

/-- A symmetric pair of raw slots contributes zero to an exterior form. -/
theorem raw_alternatization_zero_of_swap
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ) {i j : ι} (hij : i ≠ j)
    (h : a.domDomCongr (Equiv.swap i j) = a) : a.alternatization = 0 := by
  have he := raw_alternatization_reindex a (Equiv.swap i j)
  rw [h, AlternatingMap.domDomCongr_perm, Equiv.Perm.sign_swap hij] at he
  ext v
  have hv := congrArg (fun b => b v) he
  simp only [Units.smul_def, Units.val_neg, Units.val_one,
    neg_smul, one_smul, AlternatingMap.neg_apply] at hv
  change a.alternatization v = 0
  linear_combination (1/2 : ℂ) * hv

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawClosedProduct
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Every product-rule term, with its explicit slot placement. -/
theorem rawPrefix_productVariation [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    rawPrefix (rawProductVariation a Da b Db) =
      (rawProduct (rawPrefix Da) b).domDomCongr (Equiv.sumAssoc (Fin 1) ι κ) +
      (rawProduct a (rawPrefix Db)).domDomCongr (rawMoveDerivative ι κ) := by
  ext v
  rfl

/-- If both factors are closed after alternation, their full product-rule
variation is closed. This retains both placement terms before cancelling. -/
theorem rawPrefix_productVariation_closed
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (ha : (rawPrefix Da).alternatization = 0)
    (hb : (rawPrefix Db).alternatization = 0) :
    (rawPrefix (rawProductVariation a Da b Db)).alternatization = 0 := by
  rw [rawPrefix_productVariation, map_add, raw_alternatization_reindex,
    raw_alternatization_reindex, rawProduct_alternatization, rawProduct_alternatization,
    ha, hb]
  simp

/-- If only the right factor is closed, the entire derivative is exactly
the left-factor term, with its reassociation shown. -/
theorem rawPrefix_productVariation_right_closed
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (hb : (rawPrefix Db).alternatization = 0) :
    (rawPrefix (rawProductVariation a Da b Db)).alternatization =
      (wedge (rawPrefix Da).alternatization b.alternatization).domDomCongr
        (Equiv.sumAssoc (Fin 1) ι κ) := by
  rw [rawPrefix_productVariation, map_add, raw_alternatization_reindex,
    raw_alternatization_reindex, rawProduct_alternatization, rawProduct_alternatization, hb]
  simp

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawClosedPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- All derivative placements in the k-fold product vanish after
alternation when the actual two-form derivative is closed. -/
theorem rawPowerVariation_closed (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (hB : (rawPrefix DB).alternatization = 0) (k : ℕ) :
    (rawPrefix (rawPowerVariation B DB k)).alternatization = 0 := by
  induction k with
  | zero =>
    have hz : rawPrefix (rawPowerVariation B DB 0) = 0 := by ext v; rfl
    rw [hz, map_zero]
  | succ k ih =>
    rw [show wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) from Subsingleton.elim _ _]
    exact rawPrefix_productVariation_closed B DB (rawPower B k)
      (rawPowerVariation B DB k) hB ih

/-- Full raw product-rule identity underlying d(alpha wedge B^k), with
all right-factor contributions proved zero and the surviving order explicit. -/
theorem rawBoundaryVariation_closed (a : E →ₗ[ℝ] ℂ)
    (Da : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (hB : (rawPrefix DB).alternatization = 0) (k : ℕ) :
    (rawPrefix (rawProductVariation (rawCovector a) (rawCovectorVariation Da)
      (rawPower B k) (rawPowerVariation B DB k))).alternatization =
      (wedge (rawPrefix (rawCovectorVariation Da)).alternatization
        (wedgePower B.alternatization k)).domDomCongr
          (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k)) := by
  rw [rawPrefix_productVariation_right_closed _ _ _ _ (rawPowerVariation_closed B DB hB k),
    rawPower_alternatization]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawCoefficientDerivative
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem HasRawFDerivAt.product [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {b : E → MultilinearMap ℝ (fun _ : κ => E) ℂ}
    {Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ} {x : E}
    (ha : HasRawFDerivAt a Da x) (hb : HasRawFDerivAt b Db x) :
    HasRawFDerivAt (fun y => rawProduct (a y) (b y))
      (rawProductVariation (a x) Da (b x) Db) x := by
  intro v
  have hd := (ha (fun i => v (Sum.inl i))).mul (hb (fun i => v (Sum.inr i)))
  apply hd.congr_fderiv
  ext w
  simp [rawCoefficientDerivative_apply, rawProductVariation, rawProduct_apply,
    smul_eq_mul]
  ring

theorem HasRawFDerivAt.power {B : E → MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ}
    {DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ} {x : E}
    (hB : HasRawFDerivAt B DB x) (k : ℕ) :
    HasRawFDerivAt (fun y => rawPower (B y) k) (rawPowerVariation (B x) DB k) x := by
  induction k with
  | zero =>
    intro v
    have hz : rawCoefficientDerivative (rawPowerVariation (B x) DB 0) v = 0 := by ext w; rfl
    rw [hz]
    exact hasFDerivAt_const (1 : ℂ) x
  | succ k ih => exact hB.product ih

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawAlternationDerivative
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rawAlternatedCoefficientDerivative_apply
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (v : ι → E) (w : E) :
    rawAlternatedCoefficientDerivative D v w = (D w).alternatization v := by
  simp [rawAlternatedCoefficientDerivative, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, Function.comp_def]

theorem HasRawFDerivAt.alternatization
    {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ} {x : E}
    (ha : HasRawFDerivAt a D x) (v : ι → E) :
    HasFDerivAt (fun y => (a y).alternatization v)
      (rawAlternatedCoefficientDerivative D v) x := by
  simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  have hd : HasFDerivAt
      (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • (fun y => a y (v ∘ σ)))
      (rawAlternatedCoefficientDerivative D v) x :=
    HasFDerivAt.sum (u := Finset.univ)
      (fun (σ : Equiv.Perm ι) _ => (ha (v ∘ σ)).const_smul (Equiv.Perm.sign σ))
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => by simp [Finset.sum_apply, Function.comp_def])

/-- Differentiating an actual continuous form presented as a full
alternatization is full alternatization of its raw coefficient derivative.
The normalization is exactly the exterior derivative, with no factor. -/
theorem extDeriv_of_raw_alternatization {n : ℕ}
    {a : E → MultilinearMap ℝ (fun _ : Fin n => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => E) ℂ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hω : DifferentiableAt ℝ ω x)
    (heq : ∀ᶠ y in 𝓝 x, (ω y).toAlternatingMap = (a y).alternatization)
    (ha : HasRawFDerivAt a D x) :
    (extDeriv ω x).toAlternatingMap = D.uncurryLeft.alternatization := by
  ext v
  change extDeriv ω x v = _
  rw [extDeriv_apply hω, alternatization_uncurryLeft_apply]
  apply Finset.sum_congr rfl
  intro p _
  have he : (fun y => ω y (p.removeNth v)) =ᶠ[𝓝 x]
      (fun y => (a y).alternatization (p.removeNth v)) :=
    heq.mono (fun y hy => congrArg (fun b => b (p.removeNth v)) hy)
  rw [he.fderiv_eq, (ha.alternatization (p.removeNth v)).fderiv,
    rawAlternatedCoefficientDerivative_apply]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawReindexedDerivative
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma HasRawFDerivAt.reindex [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ} {x : E}
    (ha : HasRawFDerivAt a D x) :
    HasRawFDerivAt (fun y => (a y).domDomCongr e) (rawReindexDerivative e D) x := by
  intro v
  exact ha (v ∘ e)

omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] in
lemma rawPrefix_uncurry_reindex [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) :
    (rawPrefix D).domDomCongr ((Equiv.sumCongr (Equiv.refl (Fin 1)) e).trans (rawFrontFin n)) =
      (rawReindexDerivative e D).uncurryLeft := by
  ext v
  change D (v (rawFrontFin n (Sum.inl 0)))
      (fun i => v (rawFrontFin n (Sum.inr (e i)))) = D (v 0) (fun i => v (e i).succ)
  have h0 : rawFrontFin n (Sum.inl (0 : Fin 1)) = 0 := rawFrontFin_inl n 0
  have htail : (fun i => v (rawFrontFin n (Sum.inr (e i)))) = (fun i => v (e i).succ) :=
    funext (fun i => congrArg v (rawFrontFin_inr (e i)))
  rw [h0, htail]

/-- Exterior differentiation with an arbitrary explicit ordering of raw
slots, retaining the order of the distinguished derivative slot. -/
theorem extDeriv_of_reindexed_raw {n : ℕ} (e : ι ≃ Fin n)
    {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hω : DifferentiableAt ℝ ω x)
    (heq : ∀ᶠ y in 𝓝 x, (ω y).toAlternatingMap = (a y).alternatization.domDomCongr e)
    (ha : HasRawFDerivAt a D x) :
    (extDeriv ω x).toAlternatingMap = (rawPrefix D).alternatization.domDomCongr
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) e).trans (rawFrontFin n)) := by
  rw [← raw_alternatization_reindex, rawPrefix_uncurry_reindex]
  apply extDeriv_of_raw_alternatization hω _ (ha.reindex e)
  exact heq.mono (fun y hy => hy.trans (raw_alternatization_reindex (a y) e).symm)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularSublevel
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

lemma isOpen_regularSublevel {d : ℕ} {U : Set (Fin d → ℝ)} {g : (Fin d → ℝ) → ℝ}
    {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U) : IsOpen (regularSublevel U g R) := by
  exact hg.isOpen_inter_preimage hU isOpen_Iio

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceLevelFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- Smoothness of the literal energy, at any finite order, is derived from
first-order holomorphicity on the open source domain. -/
theorem MassHypotheses.contDiffAt_energy (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (r : ℕ) :
    ContDiffAt ℝ r (energy f) x := by
  apply ContDiffAt.sum
  intro j _
  have hj : ContDiffAt ℝ r (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open h.open_domain r (h.holomorphic j)).contDiffAt
      (h.open_domain.mem_nhds hx)).restrict_scalars ℝ
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x hj).mul hj

theorem MassHypotheses.tau_pos (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) : 0 < tau f x := by
  have hnot : ¬∀ j, f j x = 0 := fun hz => hne ((h.isolated_zero x hx).mp hz)
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩

theorem MassHypotheses.contDiffAt_logTau (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) (r : ℕ) :
    ContDiffAt ℝ r (logTau f) x := by
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := r) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr (h.tau_pos hx hne))).restrict_scalars ℝ).comp x
    (h.contDiffAt_energy hx r)

/-- The existing Stokes coordinates carry the wedge slots to the exact
positive interleaved frame used by the Hessian normalization. -/
theorem complexCoordinates_wedge_basis (s : WedgePowerSlots n) :
    MahlerStokes.complexCoordinates n
      (MahlerStokes.coordinateBasis (n*2) (finProdFinEquiv (pairSlotEquiv n s))) =
      interleavedBasis s := by
  exact MahlerStokes.complexCoordinates_basis n (pairSlotEquiv n s).1 (pairSlotEquiv n s).2

/-- Actual logarithmic top-form density is nonnegative in the positive
Stokes coordinate frame, with no positivity assumption. -/
theorem source_log_top_coefficient_nonneg (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) :
    0 ≤ (wedgePower (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap n
      (fun s => MahlerStokes.complexCoordinates n
        (MahlerStokes.coordinateBasis (n*2) (finProdFinEquiv (pairSlotEquiv n s))))).re := by
  simp only [complexCoordinates_wedge_basis]
  rw [extDeriv_logTau_top_of_open h.open_domain hx h.holomorphic (h.tau_pos hx hne)]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, interleavedVolume_basis, mul_one,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.nonneg_iff.mp
    (sourceHessian_logTau_det_nonneg_of_open coordinateDirection h.open_domain hx h.holomorphic
      (h.tau_pos hx hne))).1

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceFluxRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_sourceDC [FiniteDimensional ℝ E] {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+1) u x) : ContDiffAt ℝ r (oneForm (dcLinear u)) x := by
  have hd : ContDiffAt ℝ r (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact sourceDCOperator.contDiff.contDiffAt.comp x hd

lemma contDiffAt_sourceDDC {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+2) u x) :
    ContDiffAt ℝ r (extDeriv (oneForm (dcLinear u))) x := by
  have hd : ContDiffAt ℝ (r+1) (oneForm (dcLinear u)) x :=
    contDiffAt_sourceDC (by convert hu using 1 ; norm_num [add_assoc])
  have hdd : ContDiffAt ℝ r (fderiv ℝ (oneForm (dcLinear u))) x :=
    hd.fderiv_right (by norm_num)
  exact (alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x hdd

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma continuousWedgePower_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] (a : E [⋀^Fin 2]→L[ℝ] ℂ) (k : ℕ) :
    (continuousWedgePower a k).toAlternatingMap = wedgePower a.toAlternatingMap k := by
  induction k with
  | zero => rfl
  | succ k ih => change wedge _ _ = _; rw [ih]; rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_continuousWedgePower [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → E [⋀^Fin 2]→L[ℝ] ℂ} {x : X} {r : WithTop ℕ∞}
    (ha : ContDiffAt ℝ r a x) (k : ℕ) :
    ContDiffAt ℝ r (fun y => continuousWedgePower (a y) k) x := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih => exact contDiffAt_continuousWedge ha ih

/-- C1 regularity of the whole actual flux form uses C3 of its potential. -/
theorem contDiffAt_sourceBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    ContDiffAt ℝ 1 (continuousSourceBoundaryForm u k) x := by
  exact contDiffAt_continuousWedge
    (contDiffAt_sourceDC (hu.of_le (by norm_num) : ContDiffAt ℝ (1+1) u x))
    (contDiffAt_continuousWedgePower
      (contDiffAt_sourceDDC (hu : ContDiffAt ℝ (1+2) u x)) k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceCoordinateForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Set Filter MeasureTheory
open scoped Topology Manifold

namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

lemma contDiffAt_sourceRealBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    ContDiffAt ℝ 1 (sourceRealBoundaryForm u k) x := by
  exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℝ (Fin (2*k+1))
      Complex.reCLM).contDiff.contDiffAt.comp x
    ((sourceReindexCLM (E := E) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
      (contDiffAt_sourceBoundaryForm hu k)))

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRawJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual symmetry of the second Frechet derivative kills its full
alternatization, including the covector-evaluation slot. -/
theorem rawSecondJet_closed {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) :
    (rawPrefix (rawSecondJet (E := E) (fderiv ℝ (fderiv ℝ a) x))).alternatization = 0 := by
  apply raw_alternatization_zero_of_swap _ (i := Sum.inl (0 : Fin 1))
    (j := Sum.inr (0 : Fin 2)) (by simp)
  ext v
  simp only [MultilinearMap.domDomCongr_apply, rawPrefix_apply, rawSecondJet_apply]
  exact congrArg (fun L : E →L[ℝ] ℂ => L (v (Sum.inr 1)))
    (ha.isSymmSndFDerivAt (by norm_num) (v (Sum.inr 0)) (v (Sum.inl 0)))

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The raw first jet alternates to the exterior derivative. -/
theorem rawFirstJet_alternatization {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) :
    (rawFirstJet (fderiv ℝ a x)).alternatization = (extDeriv (oneForm a) x).toAlternatingMap := by
  rw [rawFirstJet, alternatization_rawUncurry]
  simp only [Nat.factorial_one, one_nsmul]
  ext v
  have hev (z w : E) : fderiv ℝ (fun y => a y z) x w = fderiv ℝ a x w z := by
    simpa using congrArg (fun L : E →L[ℝ] ℂ => L w)
      (ha.hasFDerivAt.clm_apply (hasFDerivAt_const z x)).fderiv
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  change _ = extDeriv (oneForm a) x ![v 0, v 1]
  rw [extDeriv_oneForm ha, hev, hev]
  simp [AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two,
    rawCovectorJet, Fin.removeNth, sub_eq_add_neg]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRawCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma rawCovector_hasRawFDerivAt {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) :
    HasRawFDerivAt (fun y => rawCovector (a y).toLinearMap)
      (rawCovectorVariation (rawLinearJet (fderiv ℝ a x))) x := by
  intro v
  have hd := ha.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)
  apply hd.congr_fderiv
  ext w
  simp [rawCoefficientDerivative_apply, rawCovectorVariation, rawLinearJet]

lemma rawFirstJet_hasRawFDerivAt {A : E → E →L[ℝ] E →L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) :
    HasRawFDerivAt (fun y => rawFirstJet (A y)) (rawSecondJet (fderiv ℝ A x)) x := by
  intro v
  have hd := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)).clm_apply
    (hasFDerivAt_const (v 1) x)
  apply hd.congr_fderiv
  ext w
  simp [rawCoefficientDerivative_apply]

/-- The coefficientwise derivative of the full raw
form, including every derivative of every first-jet factor. -/
theorem rawBoundary_hasRawFDerivAt {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (k : ℕ) :
    HasRawFDerivAt
      (fun y => rawBoundary (a y).toLinearMap (rawFirstJet (fderiv ℝ a y)) k)
      (rawProductVariation (rawCovector (a x).toLinearMap)
        (rawCovectorVariation (rawLinearJet (fderiv ℝ a x)))
        (rawPower (rawFirstJet (fderiv ℝ a x)) k)
        (rawPowerVariation (rawFirstJet (fderiv ℝ a x))
          (rawSecondJet (fderiv ℝ (fderiv ℝ a) x)) k)) x := by
  have hda : ContDiffAt ℝ 1 (fderiv ℝ a) x := ha.fderiv_right (by norm_num)
  exact (rawCovector_hasRawFDerivAt (ha.differentiableAt (by norm_num))).product
    ((rawFirstJet_hasRawFDerivAt (hda.differentiableAt one_ne_zero)).power k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRawOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma rawPrefix_firstJet [FiniteDimensional ℝ E] (A : E →L[ℝ] E →L[ℝ] ℂ) :
    (rawPrefix (rawCovectorVariation (rawLinearJet A))).domDomCongr
      (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) = rawFirstJet A := by
  ext v
  rfl

omit [FiniteDimensional ℝ E] in
lemma rawProduct_reindex_left [FiniteDimensional ℝ E] {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ι']
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) (e : ι ≃ ι') :
    (rawProduct a b).domDomCongr (Equiv.sumCongr e (Equiv.refl κ)) =
      rawProduct (a.domDomCongr e) b := by
  ext v
  rfl

lemma rawMain_firstJet (A : E →L[ℝ] E →L[ℝ] ℂ) (k : ℕ) :
    (wedge (rawPrefix (rawCovectorVariation (rawLinearJet A))).alternatization
      (wedgePower (rawFirstJet A).alternatization k)).domDomCongr
      (Equiv.sumCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)
        (Equiv.refl (WedgePowerSlots k))) =
    wedgePower (rawFirstJet A).alternatization (k+1) := by
  rw [← rawPower_alternatization, ← rawProduct_alternatization,
    ← raw_alternatization_reindex, rawProduct_reindex_left, rawPrefix_firstJet,
    rawProduct_alternatization, rawPower_alternatization]
  rfl

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceTopCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section

/-- The calculated top-slot order is the positive
interleaved real/imaginary order. -/
theorem sourceTopSlots_interleaved (k : ℕ) (s : WedgePowerSlots (k+1)) :
    (sourceTopSlots k s).val = (finProdFinEquiv (pairSlotEquiv (k+1) s)).val := by
  cases s with
  | inl b => fin_cases b <;> rfl
  | inr s =>
    change 1 + (1 + ((pairSlotEquiv k s).2.val + 2 * (pairSlotEquiv k s).1.val)) =
      (pairSlotEquiv k s).2.val + 2 * ((pairSlotEquiv k s).1.val + 1)
    omega

lemma coordinateCast_basis {a b : ℕ} (h : a = b) (i : Fin a) :
    coordinateCast h (MahlerStokes.coordinateBasis a i) =
      MahlerStokes.coordinateBasis b (finCongr h i) := by
  subst b
  rfl

/-- No unproved orientation factor remains in the coordinate frame. -/
theorem sourceCoordinates_top_basis (k : ℕ) (s : WedgePowerSlots (k+1)) :
    sourceCoordinates k (MahlerStokes.coordinateBasis ((2*k+1)+1) (sourceTopSlots k s)) =
      interleavedBasis s := by
  change MahlerStokes.complexCoordinates (k+1)
    (coordinateCast _ (MahlerStokes.coordinateBasis _ (sourceTopSlots k s))) = _
  rw [coordinateCast_basis]
  have hi : finCongr (show (2*k+1)+1 = (k+1)*2 by omega) (sourceTopSlots k s) =
      finProdFinEquiv (pairSlotEquiv (k+1) s) :=
    Fin.ext (sourceTopSlots_interleaved k s)
  rw [hi]
  exact complexCoordinates_wedge_basis s

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceCanonicalMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
namespace Mahler
noncomputable section

lemma measurePreserving_coordinateCast {a b : ℕ} (h : a = b) :
    MeasurePreserving (coordinateCast h) volume volume := by
  subst b
  exact MeasurePreserving.id _

lemma measurePreserving_sourceCoordinates (k : ℕ) :
    MeasurePreserving (sourceCoordinates k) volume volume :=
  (MahlerStokes.measurePreserving_complexCoordinates (k+1)).comp
    (measurePreserving_coordinateCast _)

theorem setIntegral_sourceCoordinates (k : ℕ) (S : Set (ComplexEuclidean (k+1)))
    (f : ComplexEuclidean (k+1) → ℝ) :
    (∫ x in (sourceCoordinates k) ⁻¹' S, f (sourceCoordinates k x)) = ∫ z in S, f z :=
  (measurePreserving_sourceCoordinates k).setIntegral_preimage_emb
    (sourceCoordinates k).toHomeomorph.toMeasurableEquiv.measurableEmbedding f S

lemma radiusSq_coordinateCast {a b : ℕ} (h : a = b) (x : Fin a → ℝ) :
    MahlerStokes.radiusSq (coordinateCast h x) = MahlerStokes.radiusSq x := by
  subst b
  rfl

lemma norm_sourceCoordinates_sq (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    ‖sourceCoordinates k x‖^2 = MahlerStokes.radiusSq x := by
  change ‖MahlerStokes.complexCoordinates (k+1) (coordinateCast _ x)‖^2 = _
  rw [MahlerStokes.norm_complexCoordinates_sq, radiusSq_coordinateCast]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceFullExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_dcLinear_source [FiniteDimensional ℝ E] {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) : ContDiffAt ℝ 2 (dcLinear u) x := by
  have hd : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact (((-1/4 : ℂ) • (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure).contDiff.contDiffAt.comp x hd)

lemma sourceComplexBoundaryForm_raw {u : E → ℂ} {y : E}
    (ha : DifferentiableAt ℝ (dcLinear u) y) (k : ℕ) :
    (sourceComplexBoundaryForm u k y).toAlternatingMap =
      (rawBoundary (dcLinear u y).toLinearMap (rawFirstJet (fderiv ℝ (dcLinear u) y)) k).alternatization.domDomCongr
        (sourceBoundarySlots k) := by
  rw [rawBoundary_alternatization, rawFirstJet_alternatization ha]
  change (wedge _ _).domDomCongr _ = _
  rw [continuousWedgePower_toAlternatingMap]
  rfl

/-- The exterior derivative identity in every degree.
C3 of the potential supplies all product rules and the symmetric second
jet of dc; neither closedness nor a Stokes identity is assumed. -/
theorem extDeriv_sourceComplexBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    (extDeriv (sourceComplexBoundaryForm u k) x).toAlternatingMap =
      (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap (k+1)).domDomCongr
        (sourceTopSlots k) := by
  have ha := contDiffAt_dcLinear_source hu
  have hω : DifferentiableAt ℝ (sourceComplexBoundaryForm u k) x :=
    ((sourceReindexCLM (E := E) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
      (contDiffAt_sourceBoundaryForm hu k)).differentiableAt one_ne_zero
  have heq : ∀ᶠ y in 𝓝 x, (sourceComplexBoundaryForm u k y).toAlternatingMap =
      (rawBoundary (dcLinear u y).toLinearMap (rawFirstJet (fderiv ℝ (dcLinear u) y)) k).alternatization.domDomCongr
        (sourceBoundarySlots k) :=
    (ha.eventually (by norm_num)).mono (fun y hy => sourceComplexBoundaryForm_raw
      (hy.differentiableAt (by norm_num)) k)
  have hd := extDeriv_of_reindexed_raw (sourceBoundarySlots k) hω heq
    (rawBoundary_hasRawFDerivAt ha k)
  rw [rawBoundaryVariation_closed _ _ _ _ (rawSecondJet_closed ha) k] at hd
  calc
    (extDeriv (sourceComplexBoundaryForm u k) x).toAlternatingMap = _ := hd
    _ = (wedgePower (rawFirstJet (fderiv ℝ (dcLinear u) x)).alternatization (k+1)).domDomCongr
        (sourceTopSlots k) := by
      let reindexPair := Equiv.sumCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)
        (Equiv.refl (WedgePowerSlots k))
      have slots : reindexPair.trans (sourceTopSlots k) =
          (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k)).trans
            ((Equiv.sumCongr (Equiv.refl (Fin 1)) (sourceBoundarySlots k)).trans
              (rawFrontFin (2*k+1))) := by
        ext index
        simp only [sourceTopSlots, Equiv.trans_apply, reindexPair,
          Equiv.symm_apply_apply]
      let baseForm := wedge
        (rawPrefix (rawCovectorVariation (rawLinearJet (fderiv ℝ (dcLinear u) x)))).alternatization
        (wedgePower (rawFirstJet (fderiv ℝ (dcLinear u) x)).alternatization k)
      exact (congrArg (fun equivalence => baseForm.domDomCongr equivalence) slots.symm).trans
        (congrArg (fun form : E [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
          form.domDomCongr (sourceTopSlots k))
          (rawMain_firstJet (fderiv ℝ (dcLinear u) x) k))
    _ = _ := by rw [rawFirstJet_alternatization (ha.differentiableAt (by norm_num))]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRealExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taking the real part commutes with the actual exterior derivative. -/
theorem extDeriv_realPart {n : ℕ} {ω : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hω : DifferentiableAt ℝ ω x) :
    extDeriv (fun y => Complex.reCLM.compContinuousAlternatingMap (ω y)) x =
      Complex.reCLM.compContinuousAlternatingMap (extDeriv ω x) := by
  have hr : DifferentiableAt ℝ (fun y => Complex.reCLM.compContinuousAlternatingMap (ω y)) x :=
    (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℝ (Fin n)
      Complex.reCLM).differentiableAt.comp x hω
  ext v
  rw [extDeriv_apply hr]
  change _ = Complex.reCLM (extDeriv ω x v)
  rw [extDeriv_apply hω, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_zsmul]
  congr 1
  have hd := Complex.reCLM.hasFDerivAt.comp x
    (hω.hasFDerivAt.continuousAlternatingMap_apply_const (p.removeNth v))
  rw [fderiv_continuousAlternatingMap_apply_const hω]
  exact congrArg (fun L : E →L[ℝ] ℝ => L (v p)) hd.fderiv

variable [FiniteDimensional ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem extDeriv_sourceRealBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) (v : Fin ((2*k+1)+1) → E) :
    extDeriv (sourceRealBoundaryForm u k) x v =
      (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap (k+1)
        (fun s => v (sourceTopSlots k s))).re := by
  have hω : DifferentiableAt ℝ (sourceComplexBoundaryForm u k) x :=
    ((sourceReindexCLM (E := E) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
      (contDiffAt_sourceBoundaryForm hu k)).differentiableAt one_ne_zero
  change extDeriv (fun y => Complex.reCLM.compContinuousAlternatingMap
    (sourceComplexBoundaryForm u k y)) x v = _
  rw [extDeriv_realPart hω]
  exact congrArg (fun a => (a v).re) (extDeriv_sourceComplexBoundaryForm hu k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceCoordinateExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem extDeriv_sourceCoordinateForm {d : ℕ}
    (Ψ : (Fin d → ℝ) ≃L[ℝ] E) {u : E → ℂ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ 3 u (Ψ x)) (k : ℕ) (v : Fin ((2*k+1)+1) → (Fin d → ℝ)) :
    extDeriv (sourceCoordinateForm Ψ u k) x v =
      (wedgePower (extDeriv (oneForm (dcLinear u)) (Ψ x)).toAlternatingMap (k+1)
        (fun s => Ψ (v (sourceTopSlots k s)))).re := by
  have hω := (contDiffAt_sourceRealBoundaryForm hu k).differentiableAt one_ne_zero
  have hp := extDeriv_pullback hω (Ψ.contDiff.contDiffAt : ContDiffAt ℝ 2 Ψ x) (by norm_num)
  have hd (y : Fin d → ℝ) : fderiv ℝ Ψ y = Ψ.toContinuousLinearMap := Ψ.hasFDerivAt.fderiv
  simp only [hd] at hp
  change extDeriv (fun y => (sourceRealBoundaryForm u k (Ψ y)).compContinuousLinearMap
    Ψ.toContinuousLinearMap) x v = _
  rw [hp]
  exact extDeriv_sourceRealBoundaryForm hu k (fun i => Ψ (v i))

variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

theorem MassHypotheses.coordinate_energy_extDeriv (h : MassHypotheses (k+1) N m U f G)
    {x : Fin ((2*k+1)+1) → ℝ} (hx : sourceCoordinates k x ∈ U) :
    extDeriv (sourceCoordinateForm (sourceCoordinates k) (energy f) k) x
      (MahlerStokes.coordinateBasis ((2*k+1)+1)) = massDensity f (sourceCoordinates k x) := by
  rw [extDeriv_sourceCoordinateForm _ (h.contDiffAt_energy hx 3)]
  simp only [sourceCoordinates_top_basis]
  exact (h.massDensity_eq_topForm hx).symm

/-- The punctured Stokes integrand is nonnegative, using
the nonnegative logarithmic complex Hessian in the positive frame. -/
theorem MassHypotheses.coordinate_log_extDeriv_nonneg (h : MassHypotheses (k+1) N m U f G)
    {x : Fin ((2*k+1)+1) → ℝ} (hx : sourceCoordinates k x ∈ U) (hne : x ≠ 0) :
    0 ≤ extDeriv (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) x
      (MahlerStokes.coordinateBasis ((2*k+1)+1)) := by
  have hz : sourceCoordinates k x ≠ 0 := by
    intro he
    apply hne
    exact (sourceCoordinates k).injective (by simpa using he)
  rw [extDeriv_sourceCoordinateForm _ (h.contDiffAt_logTau hx hz 3)]
  simp only [sourceCoordinates_top_basis]
  simpa only [complexCoordinates_wedge_basis] using source_log_top_coefficient_nonneg h hx hz

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceStokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory ContinuousAlternatingMap MahlerStokes
open scoped Topology Manifold

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem MassHypotheses.contDiffAt_tau (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (r : ℕ) : ContDiffAt ℝ r (tau f) x := by
  have he : (fun z => (energy f z).re) = tau f := by
    funext z; simp only [energy_eq_tau, Complex.ofReal_re]
  rw [← he]
  exact Complex.reCLM.contDiff.contDiffAt.comp x (h.contDiffAt_energy hx r)

theorem MassHypotheses.contDiffOn_coordinateTau (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (r : ℕ) :
    ContDiffOn ℝ r (fun x => tau f (Ψ x)) (Ψ ⁻¹' U) := by
  intro x hx
  exact ((h.contDiffAt_tau hx r).comp x Ψ.contDiff.contDiffAt).contDiffWithinAt

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRegularFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap MahlerStokes Set MeasureTheory
open scoped Topology
namespace Mahler
noncomputable section
variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

/-- The punctured Stokes inequality for the coordinate forms,
Hessian mass density, outward inner sphere, and ordinary complex volume.
Only the geometric inclusion of the small closed ball is a premise. -/
theorem source_regular_flux_le_mass (h : MassHypotheses (k+1) N m U f G)
    {R r : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hr : 0 < r)
    (hB : coordClosedBall ((2*k+1)+1) r ⊆
      regularSublevel ((sourceCoordinates k) ⁻¹' U) (fun x => tau f (sourceCoordinates k x)) R) :
    _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) ≤
      (R⁻¹)^(k+1) * (∫ z in U ∩ {z | tau f z < R}, massDensity f z) := by
  let D := regularSublevel ((sourceCoordinates k) ⁻¹' U)
    (fun x => tau f (sourceCoordinates k x)) R
  have hD : IsOpen D := isOpen_regularSublevel
    (h.open_domain.preimage (sourceCoordinates k).continuous)
    (h.contDiffOn_coordinateTau (sourceCoordinates k) 1).continuousOn
  have hs := source_punctured_scaled_extDeriv h k (sourceCoordinates k) hR hR1 hreg hr hB
  have hi : (∫ x in D,
      extDeriv (sourceCoordinateForm (sourceCoordinates k) (energy f) k) x
        (coordinateBasis ((2*k+1)+1))) =
      ∫ z in U ∩ {z | tau f z < R}, massDensity f z := by
    calc
      _ = ∫ x in D, massDensity f (sourceCoordinates k x) :=
        setIntegral_congr_fun hD.measurableSet (fun x hx => h.coordinate_energy_extDeriv hx.1)
      _ = _ := setIntegral_sourceCoordinates k (U ∩ {z | tau f z < R}) (massDensity f)
  have hp : 0 ≤ ∫ x in D \ coordClosedBall ((2*k+1)+1) r,
      extDeriv (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) x
        (coordinateBasis ((2*k+1)+1)) := by
    apply integral_nonneg_of_ae
    apply ae_restrict_of_forall_mem (hD.measurableSet.diff (isCompact_coordClosedBall _ _).measurableSet)
    intro x hx
    apply h.coordinate_log_extDeriv_nonneg hx.1.1
    intro hz
    apply hx.2
    subst x
    change radiusSq (0 : Fin ((2*k+1)+1) → ℝ) ≤ r^2
    simpa [radiusSq] using sq_nonneg r
  change (R⁻¹)^(k+1) * (∫ x in D, _) - _ = _ at hs
  rw [hi] at hs
  exact sub_nonneg.mp (hs ▸ hp)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRegularLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter MahlerStokes
open scoped Topology
namespace Mahler
noncomputable section
variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

/-- Small balls really lie in the source sublevel eventually; this is
derived from the isolated zero and local continuity, not assumed. -/
theorem source_eventually_ball_subset_sublevel (h : MassHypotheses (k+1) N m U f G)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), coordClosedBall ((2*k+1)+1) r ⊆
      regularSublevel ((sourceCoordinates k) ⁻¹' U) (fun x => tau f (sourceCoordinates k x)) R := by
  have hc : ContinuousOn (tau f) U := fun z hz => (h.contDiffAt_tau hz 0).continuousAt.continuousWithinAt
  have hD : IsOpen (U ∩ {z | tau f z < R}) := hc.isOpen_inter_preimage h.open_domain isOpen_Iio
  have hf0 : ∀ j, f j 0 = 0 := (h.isolated_zero 0 h.zero_mem).2 rfl
  have ht0 : tau f 0 = 0 := by simp [tau, hf0]
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hD 0 ⟨h.zero_mem, by simpa [ht0] using hR⟩
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  intro x hx
  have hs : ‖sourceCoordinates k x‖^2 ≤ r^2 := by
    rw [norm_sourceCoordinates_sq]
    exact hx
  have hn : ‖sourceCoordinates k x‖ < δ :=
    ((sq_le_sq₀ (norm_nonneg _) hr.1.le).mp hs).trans_lt hr.2
  exact hsub (by simpa using hn)

/-- A limit L of outward Stokes sphere flux
gives a regular-level mass bound R^n L.
No Stokes identity, positivity, or ball-inclusion premise remains. -/
theorem source_regular_mass_lower_of_flux_limit (h : MassHypotheses (k+1) N m U f G)
    {R L : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hlimit : Tendsto
      (fun r => _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    R^(k+1) * L ≤ ∫ z in U ∩ {z | tau f z < R}, massDensity f z := by
  have hle : L ≤ (R⁻¹)^(k+1) * (∫ z in U ∩ {z | tau f z < R}, massDensity f z) := by
    apply le_of_tendsto hlimit
    filter_upwards [source_eventually_ball_subset_sublevel h hR, self_mem_nhdsWithin] with r hB hr
    exact source_regular_flux_le_mass h hR hR1 hreg hr hB
  have hmul := mul_le_mul_of_nonneg_left hle (pow_nonneg hR.le (k+1))
  simpa only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_pow, one_mul] using hmul

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRegularMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter MahlerStokes
open scoped Topology ENNReal
namespace Mahler
noncomputable section
variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

theorem source_integral_le_massBelow (h : MassHypotheses (k+1) N m U f G) (R : ℝ) :
    ENNReal.ofReal (∫ z in U ∩ {z | tau f z < R}, massDensity f z) ≤ massBelow U f R := by
  let D := U ∩ {z | tau f z < R}
  have hc : ContinuousOn (tau f) U := fun z hz => (h.contDiffAt_tau hz 0).continuousAt.continuousWithinAt
  have hD : IsOpen D := hc.isOpen_inter_preimage h.open_domain isOpen_Iio
  by_cases hi : IntegrableOn (massDensity f) D
  · have hp : 0 ≤ᵐ[volume.restrict D] massDensity f :=
      ae_restrict_of_forall_mem hD.measurableSet (fun z hz => h.massDensity_nonneg hz.1)
    exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hi hp)
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

theorem source_regular_massBelow_of_flux_limit_oai (h : MassHypotheses (k+1) N m U f G)
    {R L : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hlimit : Tendsto
      (fun r => _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ENNReal.ofReal (R^(k+1) * L) ≤ massBelow U f R :=
  (ENNReal.ofReal_le_ofReal (source_regular_mass_lower_of_flux_limit h hR hR1 hreg hlimit)).trans
    (source_integral_le_massBelow h R)

end
end Mahler

end OAI
end

theorem solution : type_of% @OAI.Mahler.source_regular_massBelow_of_flux_limit_oai := @OAI.Mahler.source_regular_massBelow_of_flux_limit_oai
