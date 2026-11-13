-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:15.023471+00:00
-- url     : https://prove2.me/submissions/527dabe1-d5c6-4503-b20f-8bf9582377c9

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_increment_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_nonlinear_profiles
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_polynomial_free_correction_fixed_phase
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_freeDisplacement_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_freeDisplacement_residual_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q + G q) p = coordDeriv v F p + coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_add hF hG, add_apply]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma smooth_compact_weighted_bound {U : Set E} {V K : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : E → F) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ f U → MapsTo f U K → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  obtain ⟨D, hD, hbD⟩ := compact_coefficient_bound hV hK hKV hg m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hC hf hfk hbf
  exact hbf.comp hU hV hs hC (le_trans zero_le_one hD) hf hg
    (fun x hx => hKV (hfk hx)) (fun j hj x hx => hbD j hj (f x) (hfk hx))




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma WeightedBound.real_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RootMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


lemma positivePair_isOpen : IsOpen positivePair :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt continuous_const (continuous_apply 1))

lemma contDiffOn_rootDifferenceCoefficient :
    ContDiffOn ℝ ∞ rootDifferenceCoefficient positivePair := by
  have h0 : ContDiffOn ℝ ∞ (fun p : Fin 2 → ℝ => p 0) positivePair :=
    (contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffOn
  have h1 : ContDiffOn ℝ ∞ (fun p : Fin 2 → ℝ => p 1) positivePair :=
    (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffOn
  have hs0 := h0.sqrt (fun p (hp : p ∈ positivePair) => ne_of_gt hp.1)
  have hs1 := h1.sqrt (fun p (hp : p ∈ positivePair) => ne_of_gt hp.2)
  exact (hs0.add hs1).inv (fun p hp => ne_of_gt
    (add_pos (Real.sqrt_pos.2 hp.1) (Real.sqrt_pos.2 hp.2)))

lemma sqrt_difference {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt u - Real.sqrt v = (u - v) * rootDifferenceCoefficient ![u, v] := by
  have hh : Real.sqrt u + Real.sqrt v ≠ 0 := ne_of_gt
    (add_pos (Real.sqrt_pos.2 hu) (Real.sqrt_pos.2 hv))
  dsimp [rootDifferenceCoefficient]
  rw [← div_eq_mul_inv]
  apply (eq_div_iff hh).2
  nlinarith [Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]

lemma compact_root_bound {U : Set E} (hU : UniqueDiffOn ℝ U)
    {r R : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (u : E → ℝ) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ u U → MapsTo u U (Icc r R) → WeightedBound U s m C u →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (fun p => Real.sqrt (u p)) := by
  have hroot : ContDiffOn ℝ ∞ Real.sqrt (Ioi (0 : ℝ)) :=
    contDiffOn_id.sqrt (fun p hp => ne_of_gt hp)
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU isOpen_Ioi.uniqueDiffOn
    (isCompact_Icc : IsCompact (Icc r R)) (fun p hp => hr.trans_le hp.1) hroot m
  exact ⟨D, hD, hbD⟩

lemma compact_root_difference_bound {U : Set E} (hU : UniqueDiffOn ℝ U)
    {r R : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (u v : E → ℝ) (s C A : ℝ), 0 < s → 1 ≤ C → 0 ≤ A →
      ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
      MapsTo u U (Icc r R) → MapsTo v U (Icc r R) →
      WeightedBound U s m C u → WeightedBound U s m C v →
      WeightedBound U s m A (fun p => u p - v p) →
      WeightedBound U s m (2 ^ m * A * ((m.factorial : ℝ) * D * C ^ m))
        (fun p => Real.sqrt (u p) - Real.sqrt (v p)) := by
  let K : Set (Fin 2 → ℝ) := Icc (fun _ => r) (fun _ => R)
  have hKV : K ⊆ positivePair := by
    intro p hp
    exact ⟨hr.trans_le (hp.1 0), hr.trans_le (hp.1 1)⟩
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU positivePair_isOpen.uniqueDiffOn
    (isCompact_Icc : IsCompact K) hKV contDiffOn_rootDifferenceCoefficient m
  refine ⟨D, hD, ?_⟩
  intro u v s C A hs hC hA hu hv hru hrv hbu hbv hbuv
  let f : E → Fin 2 → ℝ := fun p => ![u p, v p]
  have hf : ContDiffOn ℝ ∞ f U := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i <;> simpa [f] using (by assumption : ContDiffOn ℝ ∞ _ U)
  have hfk : MapsTo f U K := by
    intro p hp
    constructor <;> intro i <;> fin_cases i <;>
      simp only [f]
    · exact (hru hp).1
    · exact (hrv hp).1
    · exact (hru hp).2
    · exact (hrv hp).2
  have hbf : WeightedBound U s m C f := by
    apply WeightedBound.pi hU hs (le_trans zero_le_one hC)
    · intro i; exact contDiffOn_pi.mp hf i
    · intro i; fin_cases i
      · exact hbu
      · exact hbv
  have hbCoef := hbD f s C hs hC hf hfk hbf
  have hc : ContDiffOn ℝ ∞ (rootDifferenceCoefficient ∘ f) U :=
    contDiffOn_rootDifferenceCoefficient.comp hf (fun p hp => hKV (hfk hp))
  apply (hbuv.real_mul hU hs.le hA (by positivity) (hu.sub hv) hc hbCoef).congr
  intro p hp
  exact sqrt_difference (hr.trans_le (hru hp).1) (hr.trans_le (hrv hp).1)

end ClosedSurfaceR4.RootMean

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



lemma compact_amplitude_bounds {U : Set E} (hU : UniqueDiffOn ℝ U)
    {r R C P : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (hP : 0 ≤ P) (m : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (s A : ℝ) (ψ u v : E → ℝ), 0 < s → 0 ≤ A →
      ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
      MapsTo u U (Icc r R) → MapsTo v U (Icc r R) →
      WeightedBound U s m P ψ → WeightedBound U s m C u → WeightedBound U s m C v →
      WeightedBound U s m A (fun p => u p - v p) →
      WeightedBound U s m K (phaseAmplitude ψ u) ∧
      WeightedBound U s m K (phaseAmplitude ψ v) ∧
      WeightedBound U s m (K * A) (fun p => phaseAmplitude ψ u p - phaseAmplitude ψ v p) := by
  obtain ⟨D0, hD0, hb0⟩ := compact_root_bound (R := R) hU hr m
  obtain ⟨D1, hD1, hb1⟩ := compact_root_difference_bound (R := R) hU hr m
  let B0 := (m.factorial : ℝ) * D0 * C ^ m
  let B1 := (m.factorial : ℝ) * D1 * C ^ m
  let K := max 1 (max (2 ^ m * P * B0) (2 ^ m * P * (2 ^ m * B1)))
  have hK0 : 2 ^ m * P * B0 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK1 : 2 ^ m * P * (2 ^ m * B1) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro s A ψ u v hs hA hψ hu hv hru hrv hbψ hbu hbv hbuv
  have hpu : ∀ p ∈ U, u p ≠ 0 := fun p hp => ne_of_gt (hr.trans_le (hru hp).1)
  have hpv : ∀ p ∈ U, v p ≠ 0 := fun p hp => ne_of_gt (hr.trans_le (hrv hp).1)
  have hrootu := hb0 u s C hs hC hu hru hbu
  have hrootv := hb0 v s C hs hC hv hrv hbv
  have hrootd := hb1 u v s C A hs hC hA hu hv hru hrv hbu hbv hbuv
  have hba := hbψ.real_mul hU hs.le hP (by positivity) hψ (hu.sqrt hpu) hrootu
  have hbb := hbψ.real_mul hU hs.le hP (by positivity) hψ (hv.sqrt hpv) hrootv
  refine ⟨hba.mono_const hK0, hbb.mono_const hK0, ?_⟩
  have hbd := hbψ.real_mul hU hs.le hP (by positivity) hψ
    ((hu.sqrt hpu).sub (hv.sqrt hpv)) hrootd
  have hbound : 2 ^ m * P * (2 ^ m * A * B1) ≤ K * A := by
    calc
      _ = (2 ^ m * P * (2 ^ m * B1)) * A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hA
  apply (hbd.mono_const hbound).congr
  intro p hp
  dsimp [phaseAmplitude]
  ring

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set

lemma weighted_coefficient {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A : Base → Tensor}
    {s J P C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m C A) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * C)
      (coefficient Q e A) := by
  have hAe := hAB.comp_coordinates hV hU hs hs1 hJ hC he hA heU heB
  have hh := hQB.clm_apply hV hs.le hP (by positivity) hQ (hA.comp he heU) hAe
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  ring

lemma weighted_coefficient_difference {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A B : Base → Tensor}
    {s J P D : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hD : 0 ≤ D) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m D (A - B)) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * D)
      (fun p => coefficient Q e A p - coefficient Q e B p) := by
  apply (weighted_coefficient hU hV hs hs1 hJ hP hD hQ he heU (hA.sub hB) heB hQB hAB).congr
  intro p hp
  exact (map_sub (Q p) (A (e p)) (B (e p))).symm




end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DoubleModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearized_add_right {n : ℕ} {F X Y : RField n} {p : Base}
    (hX : DifferentiableAt ℝ X p) (hY : DifferentiableAt ℝ Y p) (v w : Base) :
    realLinearized F (fun q => X q + Y q) v w p =
      realLinearized F X v w p + realLinearized F Y v w p := by
  simp only [realLinearized, partial_add hX hY, dotProduct_add]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SupportedCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open Set ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)

lemma realLinearizedTensor_congr_right {n : ℕ} {F X Y : RField n} {p : Base}
    (h : X =ᶠ[nhds p] Y) : realLinearizedTensor F X p = realLinearizedTensor F Y p := by
  ext i
  simp only [realLinearizedTensor_apply, realLinearized, coordDeriv, h.fderiv_eq]

lemma realLinearizedTensor_zero_right {n : ℕ} (F : RField n) (p : Base) :
    realLinearizedTensor F (fun _ => 0) p = 0 := by
  ext i
  simp [realLinearizedTensor_apply, realLinearized, coordDeriv]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ExtendedCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter



lemma displacement_zero_value {n : ℕ} (τ : ℝ) (φ : Base → ℝ) {A : Field n}
    {p : Base} (hA : A p = 0) : displacement τ φ A p = 0 := by
  ext i
  simp [displacement, QuadraticMean.realMode, QuadraticMean.realPart, hA]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_realLinearizedTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (realLinearizedTensor X Y) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realLinearizedTensor_apply, realLinearized]
  exact (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hY _)).add
    (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
      (contDiffOn_coordDeriv_vector hU hY _))

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedSolve
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma contDiffOn_displacement {n : ℕ} {U : Set Base} {φ : Base → ℝ} {Z : Field n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (displacement τ φ Z) U := by
  have he : ContDiffOn ℝ ∞ (fun p => QuadraticMean.phase (φ p / τ)) U := by
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.div_const τ)).mul contDiffOn_const).cexp
  exact (QuadraticMean.realPartCLM n).contDiff.comp_contDiffOn (he.smul hZ)



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

/-- Restoring finitely many coordinate functions is bounded in every fixed
weighted atlas norm, uniformly in the input and the scale. -/
theorem restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedEstimates.WeightedBound Set.univ s m C (h i)) →
      A.WeightedBound s m (D * C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.pair_weighted_bound (V := V) i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j) (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [localize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasLinearMapBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed linear coordinate changes preserve the actual atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V W : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma localize_clm (p : M) (χ : M → ℝ) (L : V →L[ℝ] W) (F : M → V) :
    localize p χ (L ∘ F) = L ∘ localize p χ F := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize,hx,map_smul]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma weightedBound_clm (L : V →L[ℝ] W) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) {s C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hb : A.WeightedBound s m C F) :
    A.WeightedBound s m (‖L‖*C) (L ∘ F) := by
  intro i
  rw [localize_clm]
  exact (hb i).linear uniqueDiffOn_univ hs
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn L

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedSeminorm_le_of_weightedBound {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K)
    (hb : WeightedBound Set.univ s m C f) : supportedWeightedSeminorm K s m f ≤ C := by
  apply Seminorm.finset_sup_apply_le hC
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C
  have hn : ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C / (s : ℝ) ^ j := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (div_nonneg hC (pow_nonneg s.coe_nonneg _)) j f).2
    intro x _
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le hs hjm (Set.mem_univ x)
  calc
    _ ≤ (s : ℝ) ^ j * (C / (s : ℝ) ^ j) := mul_le_mul_of_nonneg_left hn (pow_nonneg s.coe_nonneg _)
    _ = C := by field_simp [ne_of_gt hs]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the real polynomial linearization from the complex conjugated
operator. This is the realization identity needed by forced cancellation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

namespace Perturbation

lemma linearized_add {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (t : ℝ) (p : Base) :
    linearized P ε G (fun x => H x + K x) t p =
      linearized P ε G H t p + linearized P ε G K t p := by
  simp only [linearized, Expression.variation_add _ G hH hK, mul_add, Finset.sum_add_distrib]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartDisplacement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real displacements and tensor targets transported through a permitted
phase chart, with their actual support and size estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    (φ : SmallModes.Base → ℝ) (hphase : ∀ x ∈ e.source, (e x).1 = φ x)

lemma chart_displacement_smooth_support (hφ : ContDiff ℝ ∞ φ) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    ContDiff ℝ ∞ (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ∧
      tsupport (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ⊆ K := by
  refine ⟨contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn
    (chartPull e he K hK Z).contDiff.contDiffOn τ), ?_⟩
  apply closure_minimal _ K.isCompact.isClosed
  intro x hx
  by_contra hn
  exact hx (RealModes.displacement_zero_value τ φ ((chartPull e he K hK Z).zero_on_compl hn))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full linearized metric perturbation preserves the support of its
varying field, including every higher-jet polynomial term. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero_of_notMem {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X : RealModes.RField 4} {p : SmallModes.Base} (hp : p ∉ tsupport X) :
    coordinateFullLinearized P ε G X p = 0 := by
  have hx : X =ᶠ[nhds p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hp
  have hc : (X ∘ planeCoordinateIsometry) =ᶠ[nhds (planeCoordinateIsometry.symm p)] (fun _ => 0) := by
    apply hx.comp_tendsto
    simpa only [planeCoordinateIsometry.apply_symm_apply] using
      (planeCoordinateIsometry.continuous.continuousAt (x := planeCoordinateIsometry.symm p)).tendsto
  have hn : planeCoordinateIsometry.symm p ∉ tsupport (X ∘ planeCoordinateIsometry) :=
    notMem_tsupport_iff_eventuallyEq.mpr hc
  have hm : RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X p = 0 := by
    rw [RealModes.realLinearizedTensor_congr_right hx, RealModes.realLinearizedTensor_zero_right]
  funext k
  simp only [coordinateFullLinearized, Pi.add_apply, hm, Pi.zero_apply, zero_add,
    coordinateRealLinearized, linearized]
  apply Finset.sum_eq_zero
  intro l _
  rw [(P k l).variation_zero_of_notMem G hn 0, mul_zero]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

lemma trialAmplitude_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A c.e.source) (hball : InTrialBall c.e.source reference r A)
    (y : SmallModes.Base) :
    c.trialAmplitude ψ Q h hρ A y = phaseAmplitude ψ (coefficient Q c.e.symm A) y := by
  classical
  simp only [trialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A c.e.source ∧
    InTrialBall c.e.source reference r A from ⟨hA,hball⟩)]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform square-root amplitude constants from numerical coordinate,
cutoff and form bounds. In particular they precede the scale and map. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

theorem uniform_local_amplitude_bounds {V : Set Base} (hV : IsOpen V)
    {ρ R : ℝ} (hρ : 0 < ρ) (m : ℕ) (C I Q Ψ : ℝ)
    (hI : 1 ≤ I) (hQ : 1 ≤ Q) (hΨ : 1 ≤ Ψ) :
    let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (U : Set Base) (s r : ℝ)
      (reference : Base → Tensor) (F : RField 4) (ψ : Base → ℝ)
      (forms : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base)
      (_h : LocalBounds U V s r ρ R reference F ψ forms χ e)
      (d : Budgets U V s F ψ forms χ e),
      d.inv m = I → d.forms m = Q → d.psi m = Ψ → 0 < s → s ≤ 1 →
      ∀ (A B : Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      InTrialBall U reference r A → InTrialBall U reference r B →
      WeightedBound U s m C A → WeightedBound U s m C B →
      WeightedBound U s m D (A - B) →
      WeightedBound V s m A₀ (phaseAmplitude ψ (coefficient forms e A)) ∧
      WeightedBound V s m A₀ (phaseAmplitude ψ (coefficient forms e B)) ∧
      WeightedBound V s m (A₀ * J * D)
        (fun x => phaseAmplitude ψ (coefficient forms e A) x -
          phaseAmplitude ψ (coefficient forms e B) x) := by
  dsimp only
  let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
  let C' := max 1 (J * C)
  obtain ⟨A₀,hA₀,ha⟩ := compact_amplitude_bounds (R := R) hV.uniqueDiffOn hρ
    (show 1 ≤ C' from le_max_left _ _) (zero_le_one.trans hΨ) m
  refine ⟨A₀,hA₀,?_⟩
  intro U s r reference F ψ forms χ e h d hi hq hψ hs hs1 A B D hC hD hA hB hballA hballB hbA hbB hbD
  have heq : inputFactor d m = J := by simp only [inputFactor, hi, hq, J]
  have hcoeff (X : Base → Tensor) (hX : ContDiffOn ℝ ∞ X U)
      (hbX : WeightedBound U s m C X) : WeightedBound V s m C' (coefficient forms e X) := by
    have hh := weighted_coefficient h.openU.uniqueDiffOn hV.uniqueDiffOn hs hs1
      (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hC h.smoothQ h.smoothInv
      h.invInto hX (d.inv_bound m) (d.forms_bound m) hbX
    change WeightedBound V s m (inputFactor d m * C) _ at hh
    rw [heq] at hh
    exact hh.mono_const (le_max_right _ _)
  have hdiff := weighted_coefficient_difference h.openU.uniqueDiffOn hV.uniqueDiffOn
    hs hs1 (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hD h.smoothQ h.smoothInv
    h.invInto hA hB (d.inv_bound m) (d.forms_bound m) hbD
  change WeightedBound V s m (inputFactor d m * D) _ at hdiff
  rw [heq] at hdiff
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hcut : WeightedBound V s m Ψ ψ := by simpa only [hψ] using d.psi_bound m
  have hh := ha s (J * D) ψ (coefficient forms e A) (coefficient forms e B) hs
    (mul_nonneg hJ hD) h.smoothPsi
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hB)
    (coefficient_trial_range h.invInto h.margin hballA)
    (coefficient_trial_range h.invInto h.margin hballB) hcut (hcoeff A hA hbA)
    (hcoeff B hB hbB) hdiff
  exact ⟨hh.1,hh.2.1,by simpa only [J, mul_assoc] using hh.2.2⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedUniformAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds on the actual supported trial amplitudes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_trial_amplitude {V : Set SmallModes.Base} (hV : IsOpen V)
    {ρ R : ℝ} (hρ : 0 < ρ) (m : ℕ) (A I Q Ψ : ℝ)
    (hI : 1 ≤ I) (hQ : 1 ≤ Q) (hΨ : 1 ≤ Ψ) :
    let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ {n : ℕ} {P : Fin 3 → Fin n → Expression}
      {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (ψ : SupportedField (F := ℝ) c.chartCompact)
      (Qf : SmallModes.Base → Tensor →L[ℝ] ℝ)
      (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Qf c.e c.e.symm)
      (d : Budgets c.e.source c.e.target s c.realMap ψ Qf c.e c.e.symm),
      c.e.target = V → d.inv m = I → d.forms m = Q → d.psi m = Ψ →
      0 < (s : ℝ) → s ≤ 1 →
      ∀ (B C : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ A → 0 ≤ D →
      ContDiffOn ℝ ∞ B c.e.source → ContDiffOn ℝ ∞ C c.e.source →
      InTrialBall c.e.source reference r B → InTrialBall c.e.source reference r C →
      WeightedBound c.e.source s m A B → WeightedBound c.e.source s m A C →
      WeightedBound c.e.source s m D (B - C) →
      supportedWeightedSeminorm c.chartCompact s m (c.trialAmplitude ψ Qf h hρ B) ≤ A₀ ∧
      supportedWeightedSeminorm c.chartCompact s m (c.trialAmplitude ψ Qf h hρ C) ≤ A₀ ∧
      supportedWeightedSeminorm c.chartCompact s m
        (c.trialAmplitude ψ Qf h hρ B - c.trialAmplitude ψ Qf h hρ C) ≤ A₀ * J * D := by
  obtain ⟨A₀,hA₀,ha⟩ := uniform_local_amplitude_bounds (R := R) hV hρ m A I Q Ψ hI hQ hΨ
  refine ⟨A₀,hA₀,?_⟩
  intro n P ε τ G hG φ K s c r reference ψ Qf h d hv hi hq hψ hs hs1 B C D hA hD hB hC
    hballB hballC hbB hbC hbD
  rw [← hv] at ha
  obtain ⟨hu,hv',hd⟩ := ha c.e.source s r reference c.realMap ψ Qf c.e c.e.symm h d
    hi hq hψ hs hs1 B C D hA hD hB hC hballB hballC hbB hbC hbD
  let b := c.trialAmplitude ψ Qf h hρ B
  let e := c.trialAmplitude ψ Qf h hρ C
  have heb : (b : SmallModes.Base → ℝ) = RootMean.phaseAmplitude ψ (coefficient Qf c.e.symm B) :=
    funext (c.trialAmplitude_apply ψ Qf h hρ hB hballB)
  have hec : (e : SmallModes.Base → ℝ) = RootMean.phaseAmplitude ψ (coefficient Qf c.e.symm C) :=
    funext (c.trialAmplitude_apply ψ Qf h hρ hC hballC)
  let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hA0 : 0 ≤ A₀ := zero_le_one.trans hA₀
  have hD0 : 0 ≤ A₀ * J * D := mul_nonneg (mul_nonneg hA0 hJ) hD
  have hb : WeightedBound c.e.target s m A₀ b := by simpa only [heb] using hu
  have he : WeightedBound c.e.target s m A₀ e := by simpa only [hec] using hv'
  have hdiff : WeightedBound c.e.target s m (A₀ * J * D) (b - e) := by
    change WeightedBound c.e.target s m _ (fun x => b x - e x)
    simpa only [heb,hec] using hd
  have hsp := chartSupport_subset c.e (modeSupport K) c.supportChart
  exact ⟨supportedSeminorm_le_of_weightedBound hs hA0 b
      (hb.extend_support c.e.open_target (b.tsupport_subset.trans hsp) hA0),
    supportedSeminorm_le_of_weightedBound hs hA0 e
      (he.extend_support c.e.open_target (e.tsupport_subset.trans hsp) hA0),
    supportedSeminorm_le_of_weightedBound hs hD0 (b - e)
      (hdiff.extend_support c.e.open_target ((b - e).tsupport_subset.trans hsp) hD0)⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_rb8e9ed_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

lemma tensorPlaneRestore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D * ‖fiberFromThree‖, mul_nonneg hD (norm_nonneg _), ?_⟩
  intro f s C hs hs1 hC hf hb
  have hh := hd (fun i y => fiberFromThree (f i (planeCoordinateIsometry y))) s
    (‖fiberFromThree‖ * C) hs hs1 (mul_nonneg (norm_nonneg _) hC)
    (fun i => fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))
    (fun i => (weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i)).linear
      uniqueDiffOn_univ hs.le ((hf i).comp planeCoordinateIsometry.contDiff).contDiffOn fiberFromThree)
  have hout : A.TensorWeightedBound s m (D * (‖fiberFromThree‖ * C))
      (A.tensorPlaneRestore f) := hh
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeDisplacement
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real displacement of the actual charted free amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

lemma coordinate_originalFreeSeed (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    coordinateAmplitude (c.originalFreeSeed δ q b) =
      (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b) :
        SmallModes.Field 4) := by
  funext x
  change (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b))
    (planeCoordinateIsometry (planeCoordinateIsometry.symm x)) = _
  rw [planeCoordinateIsometry.apply_symm_apply]

lemma freeDisplacement_smooth_support (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    ContDiff ℝ ∞ (c.freeDisplacement δ q b) ∧
      tsupport (c.freeDisplacement δ q b) ⊆ (modeSupport K : Set SmallModes.Base) := by
  unfold freeDisplacement
  rw [c.coordinate_originalFreeSeed]
  exact chart_displacement_smooth_support c.e c.smoothForward (modeSupport K) c.supportChart
    (coordinatePhase φ) (c.smoothPhase.comp planeCoordinateIsometry.symm.contDiff) τ (c.freeSeed δ q b)

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedUniformFree
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform size and full-linearization residuals for the actual free
oscillation used by the charted mean construction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma displacement_smooth_support (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (d.displacement hρ δ q A) ∧
      tsupport (d.displacement hρ δ q A) ⊆ (modeSupport K : Set SmallModes.Base) :=
  c.freeDisplacement_smooth_support δ q (d.amplitude hρ A)

end ChartedMeanData

theorem uniform_charted_free_bounds {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B E : ℝ, 1 ≤ B ∧ 1 ≤ E ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ τ m (B * (δ * τ)) (d.displacement hρ δ q A) ∧
      WeightedBound Set.univ τ m (E * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
        (coordinateFullLinearized P ε G (d.displacement hρ δ q A)) := by
  let j := PolynomialSolveData.inputOrder (P := P) q m
  obtain ⟨A₀,hA₀,ha⟩ := uniform_charted_trial_amplitude (R := R) p.openV hρ j C
    (p.inv j) (p.forms j) (p.psi j) (p.oneLEInv j) (p.oneLEForms j) (p.oneLEPsi j)
  let B₀ := (m.factorial : ℝ) * 2 ^ m * correctedSeedBudget (tensorOrder P) p.C p.D q m (p.normal j) *
    p.J m ^ m
  let κ := fun k => max (SmallModes.errorConstant k (p.C k))
    (p.D k * SmallModes.initialConstant 4 (k + tensorOrder P) (p.C (k + tensorOrder P)))
  let γ := fun k => max (SmallModes.fullErrorConstant 4 k (p.C k))
    (p.D k * SmallModes.initialConstant 4 (k + tensorOrder P) (p.C (k + tensorOrder P)))
  let E₀ := tensorChartBudget m (p.J m) (p.J (m + 1)) * 2 ^ m *
    (FiniteParametrix.boundProfile (tensorOrder P + 1) κ γ q m * (Real.sqrt 2 * 2 ^ j * p.normal j))
  refine ⟨max 1 (B₀ * A₀),max 1 (E₀ * A₀),le_max_left _ _,le_max_left _ _,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  have hi : d.budgets.inv j = p.inv j := congrFun hd.inverse j
  have hq : d.budgets.forms j = p.forms j := congrFun hd.forms j
  have hp : d.budgets.psi j = p.psi j := congrFun hd.cutoff j
  have hz : WeightedBound c.e.source s j 0 (A - A) := by
    apply (weightedBound_zero c.e.source s j (F := Tensor)).congr
    intro x _
    exact sub_self (A x)
  obtain ⟨hu,_,_⟩ := ha c d.cutoff d.form d.localBounds d.budgets hd.target hi hq hp hs hs1
    A A 0 hC le_rfl hA.contDiffOn hA.contDiffOn
    (fun x _ => hball x (Set.mem_univ x)) (fun x _ => hball x (Set.mem_univ x))
    (hbA.restrict_open c.e.open_source) (hbA.restrict_open c.e.open_source) hz
  have hn : WeightedBound c.e.target s j (p.normal j) (freeNormal c.realMap) := by
    simpa only [hd.normal] using d.budgets.normal_bound j
  have hsize := c.freeDisplacement_bound hδ hτ hs hτs hs1 hε hsmall q m
    (zero_le_one.trans hA₀) (zero_le_one.trans (p.oneLENormal j)) hn (d.amplitude hρ A) hu
  have hres := c.freeDisplacement_residual_bound hδ hτ hs hτs hs1 hε q m
    (zero_le_one.trans hA₀) (zero_le_one.trans (p.oneLENormal j)) hn (d.amplitude hρ A) hu
  have heqB : c.freeSizeFactor q m (p.normal j) = B₀ := by
    simp only [PolynomialSolveData.freeSizeFactor,hd.coefficients,hd.perturbation,hd.coordinates,B₀]
  have heqE : c.freeResidualFactor q m (p.normal j) = E₀ := by
    have hk : c.κ = κ := by
      funext k
      simp only [PolynomialSolveData.κ,hd.coefficients,hd.perturbation,κ]
    have hg : c.freeInitialFactor = γ := by
      funext k
      simp only [PolynomialSolveData.freeInitialFactor,hd.coefficients,hd.perturbation,γ]
    simp only [PolynomialSolveData.freeResidualFactor,PolynomialSolveData.freeChartResidualFactor,
      hk,hg,hd.coordinates,E₀,j]
  rw [heqB] at hsize
  rw [heqE] at hres
  constructor
  · apply hsize.mono_const
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_max_right 1 (B₀ * A₀))
      (mul_nonneg hδ hτ.le)
  · apply hres.mono_const
    have hη : 0 ≤ (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) :=
      pow_nonneg (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))) _
    calc
      _ = (E₀ * A₀) * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le)) hη

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticInteraction
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the mixed and pure terms introduced by the second, forced
correction from the quadratic tensor of the first, free correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_add {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateFullLinearized P ε G (X + Y) =
      coordinateFullLinearized P ε G X + coordinateFullLinearized P ε G Y := by
  have ha : X + Y = (fun x => X x + Y x) := rfl
  have hc : (X + Y) ∘ planeCoordinateIsometry =
      (fun x => (X ∘ planeCoordinateIsometry) x + (Y ∘ planeCoordinateIsometry) x) := rfl
  funext p k
  simp only [coordinateFullLinearized, Pi.add_apply, coordinateRealLinearized,
    RealModes.realLinearizedTensor_apply]
  rw [hc, linearized_add _ ε G (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff), ha,
    RealModes.realLinearized_add_right (hX.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) (hY.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite additivity and smoothness of the actual full linearized operator.
Coefficient smoothness is required only near the support of the variation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) :
    coordinateFullLinearized P ε G 0 = 0 := by
  funext p
  exact coordinateFullLinearized_zero_of_notMem P ε G (by simp)

lemma coordinateFullLinearized_sum {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (a : Finset ι) (X : ι → RealModes.RField 4) (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    coordinateFullLinearized P ε G (fun p => ∑ i ∈ a, X i p) =
      fun p => ∑ i ∈ a, coordinateFullLinearized P ε G (X i) p := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change coordinateFullLinearized P ε G 0 = 0
    exact coordinateFullLinearized_zero P ε G
  | @insert i a hi ih =>
    have hs : ContDiff ℝ ∞ (fun p => ∑ j ∈ a, X j p) := ContDiff.sum fun j _ => hX j
    simp only [Finset.sum_insert hi]
    change coordinateFullLinearized P ε G (X i + fun p => ∑ j ∈ a, X j p) = _
    rw [coordinateFullLinearized_add P ε G (hX i) hs, ih]
    rfl

lemma coordinateFullLinearized_smooth {n : ℕ} {O : Set LowJet} {U : Set Base}
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {X : RealModes.RField 4} (hX : ContDiff ℝ ∞ X)
    (hXs : tsupport X ⊆ (modeSupport K : Set SmallModes.Base)) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinateFullLinearized P ε G X) := by
  let Xs : SupportedField (F := Fin 4 → ℝ) (modeSupport K) :=
    ContDiffMapSupportedIn.of_support_subset hX (subset_closure.trans hXs)
  let Xp := pullSupported planeCoordinateIsometry K Xs
  have hp : ContDiff ℝ ∞ (coordinateRealLinearized P ε G X 0) := by
    apply contDiff_pi.mpr
    intro k
    have hs : ContDiff ℝ ∞ (fun x => ∑ l, ε ^ (l.val + 1) * (P k l).variation G Xp (x, 0)) :=
      ContDiff.sum (s := Finset.univ) (fun l _ =>
      contDiff_const.mul ((P k l).variation_smooth_global hO hU K.isCompact.isClosed hKU
        (hP k l) hG Xp.contDiff hQ Xp.tsupport_subset 0))
    exact hs.comp planeCoordinateIsometry.symm.contDiff
  exact (contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
    (hG.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hX.contDiffOn)).add hp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite free oscillation and its original-coordinate linear
residual. The constants precede the immersion and scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma chartedFreeSum_eq (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    chartedFreeSum d hρ δ q A = fun x => ∑ i, (d i).displacement hρ δ q A x := rfl

lemma chartedFreeSum_smooth_support (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (chartedFreeSum d hρ δ q A) ∧
      tsupport (chartedFreeSum d hρ δ q A) ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) := by
  rw [chartedFreeSum_eq]
  refine ⟨ContDiff.sum (fun i _ => ((d i).displacement_smooth_support hρ δ q A).1),?_⟩
  apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (modeSupport (K i)).isCompact.isClosed)
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun hz => hn (Set.mem_iUnion.mpr
    ⟨i,((d i).displacement_smooth_support hρ δ q A).2 hz⟩))

theorem uniform_charted_free_family (p : ι → ChartedMeanProfile P)
    (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B E : ℝ, 1 ≤ B ∧ 1 ≤ E ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : ι → Base → ℝ} {K : ι → Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference), (∀ i, (p i).Fits (d i)) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ τ m (B * (δ * τ)) (chartedFreeSum d hρ δ q A) ∧
      WeightedBound Set.univ τ m (E * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
        (coordinateFullLinearized P ε G (chartedFreeSum d hρ δ q A)) := by
  classical
  choose B E hB hE he using fun i => uniform_charted_free_bounds (R := R) (p i) hρ q m C
  refine ⟨1 + ∑ i, B i,1 + ∑ i, E i,?_,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hB i))
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hE i))
  intro G hG φ K ε τ s c d hd hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  have hm (i : ι) := he i (d i) (hd i) hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  rw [chartedFreeSum_eq]
  constructor
  · have hh := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ
      (fun i => B i * (δ * τ)) (fun i => (d i).displacement hρ δ q A)
      (fun i _ => ((d i).displacement_smooth_support hρ δ q A).1.contDiffOn)
      (fun i _ => (hm i).1)
    apply hh.mono_const
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ hτ.le)
  · rw [coordinateFullLinearized_sum P ε G Finset.univ _
      (fun i => ((d i).displacement_smooth_support hρ δ q A).1)]
    have hh := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ
      (fun i => E i * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
      (fun i => coordinateFullLinearized P ε G ((d i).displacement hρ δ q A))
      (fun i _ => (coordinateFullLinearized_smooth (c i).openO (c i).openU P (c i).smoothP hG
        (c i).mapsG (K i) (c i).supportU ((d i).displacement_smooth_support hρ δ q A).1
        ((d i).displacement_smooth_support hρ δ q A).2 ε).contDiffOn)
      (fun i _ => (hm i).2)
    apply hh.mono_const
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ hτ.le))
      (pow_nonneg (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))) _)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorPlaneRestore
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore coordinate-plane vector fields to a smooth global displacement,
with a fixed-atlas weighted estimate and no derivative loss. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorPlaneRestore_smooth (f : A.centers → SmallModes.Base → V)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) : ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.vectorPlaneRestore f) := by
  have hh : ContMDiff planeModel 𝓘(ℝ, V) ∞
      (fun x => ∑ i : A.centers, restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry) x) :=
    ContMDiff.sum (fun i _ => restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      ((hf i).comp planeCoordinateIsometry.contDiff))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [vectorPlaneRestore, Finset.sum_apply]

variable [CompactSpace M]

theorem vectorPlaneRestore_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (f : A.centers → SmallModes.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.WeightedBound s m (D*C) (A.vectorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := V) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  exact hd (fun i => f i ∘ planeCoordinateIsometry) s C hs hs1 hC
    (fun i => (hf i).comp planeCoordinateIsometry.contDiff)
    (fun i => weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasFreeOscillation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global free oscillation and its weighted displacement bound. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasFreeFiberSpace
local instance atlasFreeDualAdd_rb8e9ed_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasFreeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasFreeFiberNormed
local instance atlasFreeSectionNormed_rb8e9ed_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasFreeSectionSpace_rb8e9ed_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma atlasFreeOscillation_smooth
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ (A.atlasFreeOscillation d hρ δ q u) :=
  A.vectorPlaneRestore_smooth _ (fun i => (chartedFreeSum_smooth_support
    (d i).data hρ δ q (A.tensorPlaneRead i u)).1)

theorem uniform_atlas_free_size
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (q m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → τ/s + ε/τ^loss ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      A.TensorWeightedBound s N C u →
      A.WeightedBound τ m (B*(δ*τ)) (A.atlasFreeOscillation d hρ δ q u) := by
  classical
  dsimp only
  let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i
    (PolynomialSolveData.inputOrder (P := P i) q m)
  let C' := fun i => max 1 (D i*C)
  choose B E hB hE hfree using fun i : A.centers =>
    uniform_charted_free_family (R := R) (r := r i) (reference := reference i) (p i) hρ q m (C' i)
  let S := 1 + ∑ i : A.centers, B i
  have hS (i : A.centers) : B i ≤ S := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := B) (fun i _ => zero_le_one.trans (hB i)) (Finset.mem_univ i)
    change B i ≤ 1 + ∑ i : A.centers, B i
    linarith
  have hS0 : 0 ≤ S := by
    have hh : 0 ≤ ∑ i : A.centers, B i := Finset.sum_nonneg (fun i _ => zero_le_one.trans (hB i))
    change 0 ≤ 1 + ∑ i : A.centers, B i
    linarith
  obtain ⟨D₀,hD₀,hrestore⟩ := A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  refine ⟨max 1 (D₀*S),le_max_left _ _,?_⟩
  intro ε τ s d hd hτ hs hτs hs1 hε hsmall δ hδ u hu hball hbu
  have hη (i : A.centers) : τ/s + ε/τ^tensorLoss (P i) ≤ 1 := by
    apply le_trans _ hsmall
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    apply pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
    exact Finset.le_sup (f := fun i : A.centers => tensorLoss (P i)) (Finset.mem_univ i)
  have hlocal (i : A.centers) : WeightedEstimates.WeightedBound univ s
      (PolynomialSolveData.inputOrder (P := P i) q m) (C' i) (A.tensorPlaneRead i u) := by
    have horder : PolynomialSolveData.inputOrder (P := P i) q m ≤ N := Finset.le_sup
      (f := fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
      (Finset.mem_univ i)
    have hbu' : A.TensorWeightedBound s (PolynomialSolveData.inputOrder (P := P i) q m) C u :=
      fun k => (hbu k).mono_order horder
    exact (hread i u s C hs hs1 hC hu hbu').mono_const (le_max_right _ _)
  have hsize (i : A.centers) : WeightedEstimates.WeightedBound univ τ m (S*(δ*τ))
      (chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u)) := by
    have hh := (hfree i (d i).data (hd i) hτ hs hτs hs1 hε (hη i) δ hδ
      (A.tensorPlaneRead i u) (zero_le_one.trans (le_max_left _ _))
      (A.tensorPlaneRead_smooth i hu) (hball i) (hlocal i)).1
    exact hh.mono_const (mul_le_mul_of_nonneg_right (hS i) (mul_nonneg hδ hτ.le))
  have hh := hrestore _ τ (S*(δ*τ)) hτ (hτs.trans hs1)
    (mul_nonneg hS0 (mul_nonneg hδ hτ.le))
    (fun i => (chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).1) hsize
  intro i
  apply (hh i).mono_const
  calc
    D₀*(S*(δ*τ)) = (D₀*S)*(δ*τ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PerturbedIncrementEstimate
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combine the actual polynomial metric expansion and its finite free and
forced cancellations. The polynomial loss is fixed before the accuracy order. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes

lemma coordinateFullLinearized_smooth_global {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    {G : Base → Space} {X : RField 4} (hG : ContDiff ℝ ∞ G)
    (hX : ContDiff ℝ ∞ X) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinateFullLinearized P ε G X) := by
  apply (contDiffOn_univ.mp (contDiffOn_realLinearizedTensor isOpen_univ
    (hG.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hX.contDiffOn)).add
  apply contDiff_pi.mpr
  intro k
  change ContDiff ℝ ∞ (fun p => ∑ l, ε^(l.val+1) *
    (P k l).variation G (X ∘ planeCoordinateIsometry) (planeCoordinateIsometry.symm p,0))
  apply ContDiff.sum
  intro l _
  apply contDiff_const.mul
  have hs := (P k l).variation_smooth (U := univ) isOpen_univ hG
    (hX.comp planeCoordinateIsometry.contDiff) (fun _ _ => mem_univ _) (hP k l)
  have hs' : ContDiff ℝ ∞ ((P k l).variation G (X ∘ planeCoordinateIsometry)) := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using hs
  exact hs'.comp (planeCoordinateIsometry.symm.contDiff.prodMk contDiff_const)

lemma combinedQuadraticMean_smooth_global {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    {G : Base → Space} {φ : ι → Base → ℝ} {H : ι → Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (ε τ : ℝ) :
    ContDiff ℝ ∞ (combinedQuadraticMean P ε G φ H τ 0) := by
  have hs : ContDiff ℝ ∞ (RealModes.zeroPhaseSum τ
      (fun i => coordinatePhase (φ i)) (fun i => coordinateAmplitude (H i))) := by
    apply contDiffOn_univ.mp
    apply ContDiffOn.sum
    intro i _
    apply contDiffOn_pi.mpr
    intro k
    exact QuadraticMean.contDiffOn_zeroPair
      (QuadraticMean.contDiffOn_derivativeAmplitude isOpen_univ
        ((hφ i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
        ((hH i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn τ _)
      (QuadraticMean.contDiffOn_derivativeAmplitude isOpen_univ
        ((hφ i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
        ((hH i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn τ _)
  apply hs.add
  apply contDiff_pi.mpr
  intro k
  apply ContDiff.sum
  intro i _
  exact (contDiffOn_univ.mp (quadraticMeanCoefficient_smooth isOpen_univ (hP k)
    hG (hφ i) (hH i) (fun _ _ => mem_univ _) ε τ 0)).comp
      planeCoordinateIsometry.symm.contDiff

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialFreeResidual
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform global metric-linear residual of the actual free oscillation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFreeResidualDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFreeResidualDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFreeResidualFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFreeResidualFiberSpace
local instance polynomialFreeResidualSectionNormed_rb8e9ed_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFreeResidualSectionSpace_rb8e9ed_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_atlas_polynomial_free_residual
    {n : A.centers → ℕ} {mQ : ℕ}
    (Pglobal : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (P : A.centers → Fin 3 → Fin mQ → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (hrep : A.PolynomialLinearRepresentation Pglobal P)
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (q m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
      {ε τ η : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).G = A.jetChartMap i F) →
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → 0 ≤ η → η ≤ 1 →
      (∀ i, τ/s + ε/τ^tensorLoss (P i) ≤ η) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      A.TensorWeightedBound s N C u →
      A.TensorWeightedBound τ m (B*(δ*τ)*η^(q+1))
        (linearMetricTensor F (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u)+
          A.atlasPolynomialVariation Pglobal ε F
            (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u)) := by
  classical
  dsimp only
  let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i
    (PolynomialSolveData.inputOrder (P := P i) q m)
  let C' := fun i => max 1 (D i*C)
  choose B E hB hE hfree using fun i : A.centers =>
    uniform_charted_free_family (R := R) (r := r i) (reference := reference i) (p i) hρ q m (C' i)
  let S := 1 + ∑ i : A.centers, E i
  have hS (i : A.centers) : E i ≤ S := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := E) (fun i _ => zero_le_one.trans (hE i)) (Finset.mem_univ i)
    change E i ≤ 1 + ∑ i : A.centers, E i
    linarith
  have hS0 : 0 ≤ S := by
    have hh : 0 ≤ ∑ i : A.centers, E i := Finset.sum_nonneg (fun i _ => zero_le_one.trans (hE i))
    change 0 ≤ 1 + ∑ i : A.centers, E i
    linarith
  obtain ⟨D₀,hD₀,hrestore⟩ := A.tensorPlaneRestore_bound m
  refine ⟨max 1 (D₀*S),le_max_left _ _,?_⟩
  intro F hF ε τ η s d hG hd hτ hs hτs hs1 hε hη hη1 hηle hK δ hδ u hu hball hbu
  have hlocal (i : A.centers) : WeightedEstimates.WeightedBound univ s
      (PolynomialSolveData.inputOrder (P := P i) q m) (C' i) (A.tensorPlaneRead i u) := by
    have horder : PolynomialSolveData.inputOrder (P := P i) q m ≤ N := Finset.le_sup
      (f := fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
      (Finset.mem_univ i)
    have hbu' : A.TensorWeightedBound s (PolynomialSolveData.inputOrder (P := P i) q m) C u :=
      fun k => (hbu k).mono_order horder
    exact (hread i u s C hs hs1 hC hu hbu').mono_const (le_max_right _ _)
  let f := fun i => chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u)
  have hf (i : A.centers) : ContDiff ℝ ∞ (f i) :=
    (chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).1
  have hsp (i : A.centers) : tsupport (f i) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp
      ((chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).2 hx)
    exact hK i j hj
  have hres (i : A.centers) : WeightedEstimates.WeightedBound univ τ m
      (S*(δ*τ)*η^(q+1))
      (coordinateFullLinearized (P i) ε (A.jetChartMap i F) (f i)) := by
    have hh := (hfree i (d i).data (hd i) hτ hs hτs hs1 hε
      ((hηle i).trans hη1) δ hδ
      (A.tensorPlaneRead i u) (zero_le_one.trans (le_max_left _ _))
      (A.tensorPlaneRead_smooth i hu) (hball i) (hlocal i)).2
    change WeightedEstimates.WeightedBound univ τ m
      (E i*(δ*τ)*(τ/s+ε/τ^tensorLoss (P i))^(q+1))
      (coordinateFullLinearized (P i) ε (d i).G (f i)) at hh
    rw [hG i] at hh
    apply hh.mono_const
    have hlocalη : 0 ≤ τ/s+ε/τ^tensorLoss (P i) :=
      add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hS i) (mul_nonneg hδ hτ.le))
      (pow_le_pow_left₀ hlocalη (hηle i) _) (pow_nonneg hlocalη _)
      (mul_nonneg hS0 (mul_nonneg hδ hτ.le))
  change A.TensorWeightedBound τ m _
    (linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f)+
      A.atlasPolynomialVariation Pglobal ε F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f))
  rw [hrep F hF f hf hsp ε]
  have hh := hrestore _ τ (S*(δ*τ)*η^(q+1)) hτ (hτs.trans hs1)
    (by positivity) (fun i => coordinateFullLinearized_smooth_global (hP i)
      (A.jetChartMap_smooth i hF) (hf i) ε) hres
  intro i
  apply (hh i).mono_const
  calc
    D₀*(S*(δ*τ)*η^(q+1)) = (D₀*S)*(δ*τ)*η^(q+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le))
      (pow_nonneg hη _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InputPolynomialSmallIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble a uniform nearby-map increment from fixed profiles and an adjusted mean. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasFiberSpace
local instance polynomialSmallAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasFiberSpace
local instance polynomialSmallAtlasSectionNormed_rb8e9ed_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSmallAtlasSectionSpace_rb8e9ed_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem input_polynomial_small_increment_fixed_phase_oai
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Q)
    (hlin : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : A.centers × Fin 3 → M → ℝ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          φ k l)) x))
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ∀ i, Fin 3 → ChartedMeanProfile (Q i)) {ρ R : ℝ} (hρ : 0 < ρ),
      ∀ (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
      (D : ℕ → ℝ) (_hD : ∀ m, 0 ≤ D m)
    (C E : ℕ → ℝ) (_hC : ∀ m, 0 ≤ C m) (_hE : ∀ m, 0 ≤ E m) (q : ℕ),
    ∃ B T : ℕ → ℝ,
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ a : A.centers × Fin 3, A.freeGlobalPhase d a.1 a.2 = φ a) →
      (∀ i, (d i).G = A.jetChartMap i G) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Q i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η →
      (∀ m, A.ShiftedBound 2 m s (D m) G) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      (∀ m, A.TensorWeightedBound τ m (E m*δ^2*η^(q+1))
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*η^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  classical
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_polynomial_free_correction_fixed_phase Pol Q hQ hquad hlin
    F hF φ hφ hImm hgood Ω hΩ KΩ hΩK hweight
  refine ⟨ρ₀,hρ₀,?_⟩
  intro p ρ R hρ r reference D hD C E hC hE q
  let N := fun m => Finset.univ.sup
    (fun i : A.centers => PolynomialSolveData.inputOrder (P := Q i) q m)
  choose Af hAf hfree using fun m => A.uniform_atlas_free_size p hρ r reference q m (C (N m)) (hC (N m))
  choose Ef hEf hfreeRes using fun m => A.uniform_atlas_polynomial_free_residual Pol Q hQ hlin
    p hρ r reference q m (C (N m)) (hC (N m))
  obtain ⟨Cv,Ct,hCv,hCt,hcorr⟩ := hall p hρ r reference D hD C hC q
  let L : ℝ := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  let A₀ := fun m => L*Af m
  let B₀ := fun m => L*Cv m
  have hA₀ (m) : 0 ≤ A₀ m := mul_nonneg hL (zero_le_one.trans (hAf m))
  have hB₀ (m) : 0 ≤ B₀ m := mul_nonneg hL (hCv m)
  obtain ⟨E₁,E₂,hE₁,hE₂,hnonlinear⟩ := A.atlas_polynomial_nonlinear_profiles Pol hPol
    Ω hΩ KΩ hΩK houter D A₀ B₀ hD hA₀ hB₀
  choose Dm hDm hincrement using fun m => A.atlas_polynomial_increment_bound m
    (A₀ (m+1)) (B₀ (m+1)) (hA₀ (m+1)) (hB₀ (m+1))
  let B := fun m => A₀ m+B₀ m
  let T := fun m => Ef m+Ct m+E m+Dm m+E₁ m+E₂ m
  have hB (m) : 0 ≤ B m := add_nonneg (hA₀ m) (hB₀ m)
  have hT (m) : 0 ≤ T m := by
    dsimp [T]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (zero_le_one.trans (hEf m)) (hCt m)) (hE m)) (hDm m)) (hE₁ m)) (hE₂ m)
  refine ⟨B,T,hB,hT,?_⟩
  intro G hG b hb hbρ hclose ε τ s d hfit hphase hdG hτ hs hτs hs1 hε hε1
    η hη hη1 hsmall hd hK δ hδ hδτ u H hu hH hball hbu hmean
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  let loss := max (Finset.univ.sup (fun i : A.centers => tensorLoss (Q i)))
    (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))
  have hle (k : ℕ) (hk : k ≤ loss) : τ/s+ε/τ^k ≤ η := by
    apply le_trans _ hsmall
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    exact pow_le_pow_of_le_one hτ.le hτ1 hk
  have hQsmall (i) : τ/s+ε/τ^tensorLoss (Q i) ≤ η := hle _
    ((Finset.le_sup (f := fun i : A.centers => tensorLoss (Q i)) (Finset.mem_univ i)).trans (le_max_left _ _))
  have hPsmall (i) : ε/τ^tensorLoss (Pol i) ≤ 1 := by
    have hh := hle _ ((Finset.le_sup (f := fun i : A.centers => tensorLoss (Pol i))
      (Finset.mem_univ i)).trans (le_max_right _ _))
    linarith [div_nonneg hτ.le hs.le]
  have hfreeSmall : τ/s+ε/τ^(Finset.univ.sup (fun i : A.centers => tensorLoss (Q i))) ≤ 1 :=
    (hle _ (le_max_left _ _)).trans hη1
  obtain ⟨W,hW,hwsize,hwres⟩ := hcorr G hG b hb hbρ hclose d hfit hphase hdG hτ hs hτs hs1
    hε hε1 η hη hη1 hQsmall hd hK δ hδ u hu hball hbu
  let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
  let V := spaceCoordinates.symm ∘ W
  have hUr := A.atlasFreeOscillation_smooth d hρ δ q u
  have hU : ContMDiff planeModel spaceModel ∞ U := spaceCoordinates.symm.contDiff.contMDiff.comp hUr
  have hV : ContMDiff planeModel spaceModel ∞ V := spaceCoordinates.symm.contDiff.contMDiff.comp hW
  have hbU (m) : A.WeightedBound τ m (A₀ m*(δ*τ)) U := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hUr hτ.le
      (hfree m d hfit hτ hs hτs hs1 hε hfreeSmall δ hδ.le u hu hball (hbu (N m)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [U,A₀,L])
    all_goals ring
  have hbV (m) : A.WeightedBound τ m (B₀ m*δ^2) V := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hW hτ.le (hwsize m)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [V,B₀,L])
    all_goals ring
  have hfreeResidual (m) : A.TensorWeightedBound τ m (Ef m*(δ*τ)*η^(q+1))
      (linearMetricTensor G U+A.atlasPolynomialVariation Pol ε G U) :=
    hfreeRes m G hG d hdG hfit hτ hs hτs hs1 hε hη hη1 hQsmall hK δ hδ.le u hu hball (hbu (N m))
  obtain ⟨hinter,hremainder⟩ := hnonlinear G U V hG hU hV s τ ε δ hτ hs hτs hs1
    hε hε1 hδ hδτ hPsmall hd hbU hbV
  let H₀ := A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u))
  have hH₀ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H₀ x)) := by
    apply A.tensorPlaneRestore_smooth
    intro i
    exact combinedQuadraticMean_smooth_global (hQ i) (d i).smoothG
      (fun j => ((d i).solver j).smoothPhase)
      (fun j => ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff) ε τ
  refine ⟨U+V,hU.add hV,?_,?_⟩
  · intro m k
    apply ((A.weightedBound_add hU hV hτ.le (hbU m) (hbV m)) k).mono_const
    have hδ2 : δ^2 ≤ δ*τ := by nlinarith
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hδ2 (hB₀ m)]
  · intro m k
    have hforced : A.TensorWeightedBound τ m (Ct m*δ^2*η^(q+1))
        (linearMetricTensor G V+A.atlasPolynomialVariation Pol ε G V+
          (inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U)-H₀) := by
      have hh := hwres m
      have heq : linearMetricTensor G V+A.atlasPolynomialVariation Pol ε G V+
          (inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U-H₀) =
          linearMetricTensor G V+A.atlasPolynomialVariation Pol ε G V+
          (inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U)-H₀ := by abel
      change A.TensorWeightedBound τ m _ (linearMetricTensor G V+
        A.atlasPolynomialVariation Pol ε G V+(inducedTensor U+A.atlasPolynomialQuadratic Pol ε G U-H₀)) at hh
      rw [heq] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hh := hincrement m Pol hPol G U V hG hU hV (δ^2 • H) H₀
      (hH.const_smul_section (a := δ^2)) hH₀ τ ε δ
      (Ef m*(δ*τ)*η^(q+1)) (Ct m*δ^2*η^(q+1)) (E m*δ^2*η^(q+1)) (E₁ m) (E₂ m)
      hτ hτ1 hδ.le hδτ (hbU (m+1)) (hbV (m+1)) (hfreeResidual m) hforced (hmean m)
      (hinter m) (hremainder m)
    apply (hh k).mono_const
    have hδ1 : δ ≤ 1 := hδτ.trans hτ1
    have hδt : δ*τ ≤ δ := mul_le_of_le_one_right hδ.le hτ1
    have hδ2 : δ^2 ≤ δ := by nlinarith
    have hp : 0 ≤ η^(q+1) := pow_nonneg hη _
    have hx : 0 ≤ δ^3/τ := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδt (zero_le_one.trans (hEf m))) hp
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ2 (hCt m)) hp
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ2 (hE m)) hp
    have h4 : 0 ≤ Ef m+Ct m+E m := add_nonneg (add_nonneg (zero_le_one.trans (hEf m)) (hCt m)) (hE m)
    have h5 : 0 ≤ Dm m+E₁ m+E₂ m := add_nonneg (add_nonneg (hDm m) (hE₁ m)) (hE₂ m)
    dsimp [T]
    nlinarith [mul_nonneg h4 hx,mul_nonneg h5 (mul_nonneg hδ.le hp)]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase_oai.{u_1}
