-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:28.609199+00:00
-- url     : https://prove2.me/submissions/558f23c6-08f1-40f5-9a1f-56e404644524

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_metricMeanField_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_metricMeanField_difference_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_originalFreeSeed_bound

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

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith


lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)



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

lemma WeightedBound.mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
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

lemma WeightedBound.const_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a * f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul]
  calc
    _ = ‖a‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg a)

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
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

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



lemma reducedConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ reducedConstant m K := by
  unfold reducedConstant
  positivity

lemma errorConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ errorConstant m K := by
  unfold errorConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK)) (by positivity)

lemma targetConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ targetConstant n m K := by
  unfold targetConstant
  positivity

lemma fullErrorConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ fullErrorConstant n m K :=
  mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK))
    (targetConstant_nonneg n (m + 1) hK)

lemma amplitudeConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ amplitudeConstant n m K := by
  unfold amplitudeConstant
  exact mul_nonneg (by positivity) (targetConstant_nonneg _ _ hK)

lemma initialConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ initialConstant n m K := by
  unfold initialConstant
  exact add_nonneg (by positivity) (amplitudeConstant_nonneg _ _ hK)

end Quantitative
end ClosedSurfaceR4.SmallModes

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

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma freeSeed_sub (δ τ : ℝ) (b c : Base → ℝ) (F : RField 4) :
    freeSeed δ τ (fun p => b p - c p) F = fun p => freeSeed δ τ b F p - freeSeed δ τ c F p := by
  ext p i
  simp only [freeSeed, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_sub]
  ring

end ClosedSurfaceR4.RealModes

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

namespace ClosedSurfaceR4.FiniteMean
open ClosedSurfaceR4.WeightedEstimates Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem MeanBounds.finset_sum {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference : E → F} {r : ℝ} {L : ℕ}
    (a : Finset ι) (T : ι → ℝ → (E → F) → E → F) (B K : ι → ℕ → ℝ → ℝ)
    (hT : ∀ i ∈ a, MeanBounds U s reference r L (T i) (B i) (K i)) :
    MeanBounds U s reference r L (fun η f x => ∑ i ∈ a, T i η f x)
      (fun m C => 1 + ∑ i ∈ a, B i m C) (fun m C => 1 + ∑ i ∈ a, K i m C) := by
  constructor
  · intro m C hC
    have hh : 0 ≤ ∑ i ∈ a, B i m C := Finset.sum_nonneg
      (fun i hi => le_trans zero_le_one ((hT i hi).B_pos m C hC))
    linarith
  · intro m C hC
    have hh : 0 ≤ ∑ i ∈ a, K i m C := Finset.sum_nonneg
      (fun i hi => le_trans zero_le_one ((hT i hi).K_pos m C hC))
    linarith
  · intro η hη hη1 f hf hball
    exact ContDiffOn.sum (fun i hi => (hT i hi).smooth η hη hη1 f hf hball)
  · intro η hη hη1 m C f hC hf hball hb
    have hh := WeightedBound.finset_sum hU hs a (fun i => η * B i m C)
      (fun i => T i η f) (fun i hi => (hT i hi).smooth η hη hη1 f hf hball)
      (fun i hi => (hT i hi).value η hη hη1 m C f hC hf hball hb)
    apply hh.mono_const
    rw [← Finset.mul_sum, mul_add, mul_one]
    linarith
  · intro η hη hη1 m C D f g hC hD hf hg hballf hballg hbf hbg hbd
    have hh := WeightedBound.finset_sum hU hs a (fun i => K i m C * η * D)
      (fun i => T i η f - T i η g)
      (fun i hi => ((hT i hi).smooth η hη hη1 f hf hballf).sub
        ((hT i hi).smooth η hη hη1 g hg hballg))
      (fun i hi => (hT i hi).difference η hη hη1 m C D f g hC hD hf hg hballf hballg hbf hbg hbd)
    have hbound : (∑ i ∈ a, K i m C * η * D) ≤ (1 + ∑ i ∈ a, K i m C) * η * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, add_mul, one_mul, add_mul]
      have hpos : 0 ≤ η * D := mul_nonneg hη.le hD
      linarith
    apply (hh.mono_const hbound).congr
    intro x hx
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]

end ClosedSurfaceR4.FiniteMean

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetWordDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every ordered coordinate jet is a derivative of a component of the
actual second jet, with precisely the excess derivative count. -/
noncomputable section

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma exists_lowWord (w : List (Fin 2)) (hw : w.length ≤ 2) :
    ∃ i : Fin 7, lowWord i = w := by
  cases w with
  | nil => exact ⟨0, rfl⟩
  | cons a w =>
    cases w with
    | nil =>
      fin_cases a
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    | cons b w =>
      have he : w = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hw
        omega)
      subst w
      fin_cases a <;> fin_cases b
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩

lemma split_lowWord (w : List (Fin 2)) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, w = v ++ lowWord i ∧ v.length = w.length - 2 := by
  obtain ⟨i, hi⟩ := exists_lowWord (w.drop (w.length - 2)) (by
    rw [List.length_drop]
    omega)
  refine ⟨w.take (w.length - 2), i, ?_, ?_⟩
  · rw [hi, List.take_append_drop]
  · rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]

lemma iteratedDirectional_append {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v w : List A) (f : A → E) :
    iteratedDirectional (v ++ w) f = iteratedDirectional v (iteratedDirectional w f) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.cons_append, iteratedDirectional, ih]

/-- The scale loss of an ordered jet factor is its derivative order minus two. -/
lemma jet_as_lowJet_derivative (w : List (Fin 2)) (a : Fin 4) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, v.length = w.length - 2 ∧
      ∀ (G : Base → Space), jet G w a =
        iteratedDirectional (v.map coordinateVector) (fun p => lowJet G p (Sum.inr (i, a))) := by
  obtain ⟨v, i, hw, hv⟩ := split_lowWord w
  refine ⟨v, i, hv, ?_⟩
  intro G
  change iteratedDirectional (w.map coordinateVector) (fun p => G p a) = _
  rw [hw, List.map_append, iteratedDirectional_append]
  rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedActualJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

/-- A weighted bound on the second-jet map controls every actual higher jet. -/
theorem weighted_actual_jet {U : Set Base} (hU : IsOpen U) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + (w.length - 2)) B (lowJet G)) :
    WeightedBound U s m (B / s ^ (w.length - 2)) (jet G w a) := by
  obtain ⟨v, i, hv, he⟩ := jet_as_lowJet_derivative w a
  rw [he G]
  have hQ := (lowJet_smooth hG).contDiffOn (s := U)
  have hcomp := hb.component hU.uniqueDiffOn hs.le hB hQ (Sum.inr (i, a))
  have hf : ContDiffOn ℝ ∞ (fun p => lowJet G p (Sum.inr (i, a))) U :=
    (contDiff_pi.mp (lowJet_smooth hG) (Sum.inr (i, a))).contDiffOn
  have hvnorm : ∀ x ∈ v.map coordinateVector, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact norm_coordinateVector_le j
  have hcomp' : WeightedBound U s (m + (v.map coordinateVector).length) B
      (fun p => lowJet G p (Sum.inr (i, a))) := by
    simpa only [List.length_map, hv] using hcomp
  have hd := hcomp'.iteratedDirectional hU hs hB hf (v.map coordinateVector) hvnorm m
  simpa only [List.length_map, hv] using hd

end ClosedSurfaceR4.JetPolynomial

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

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for tensor transport through phase charts. The
change of chart changes constants but introduces no scale loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma tensorChartBudget_nonneg (m : ℕ) {J D : ℝ} (hJ : 0 ≤ J) (hD : 0 ≤ D) :
    0 ≤ tensorChartBudget m J D := by unfold tensorChartBudget; positivity

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrix
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite parametrix improvement with derivative loss. This is a finite
algebraic iteration; no bounded inverse on one Banach space is assumed. -/
noncomputable section

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma boundProfile_nonneg {L : ℕ} {K C : ℕ → ℝ}
    (hK : ∀ m, 0 ≤ K m) (hC : ∀ m, 0 ≤ C m) (j m : ℕ) :
    0 ≤ boundProfile L K C j m := by
  induction j generalizing m with
  | zero => exact hC m
  | succ j ih => exact mul_nonneg (hK m) (ih (m + L))

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedTupleOperators
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tuples of supported linear operators, with actual weighted
seminorm bounds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A F E ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup E] [Module ℝ E]
  [Fintype ι]

lemma supportedWeightedSeminorm_mono {K : Compacts A} (s : ℝ≥0) {m r : ℕ} (hmr : m ≤ r)
    (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm K s m f ≤ supportedWeightedSeminorm K s r f := by
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact supportedWeightedSeminorm_component s r j (hjm.trans hmr) f

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedLowCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform angular-slice estimates for smooth low-jet coefficients on a
compact admissible set. The angular parameter adds no scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_lowJet_pair {U : Set Base} (hU : IsOpen U) {Q : Base → LowJet}
    (hQ : ContDiffOn ℝ ∞ Q U) {s B : ℝ} (hs : 0 < s) (hB : 1 ≤ B) (m : ℕ)
    (hb : WeightedBound U s m B Q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (2 * B) (fun p => (Q p, t)) := by
  have hleft : WeightedBound U s m B (fun p => (Q p, (0 : ℝ))) := by
    simpa only [ContinuousLinearMap.norm_inl, one_mul, Function.comp_def,
      ContinuousLinearMap.inl_apply] using
      hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hc : ‖((0 : LowJet), t)‖ ≤ 1 := by
    rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg ht.1]
    exact max_le (by norm_num) ht.2
  have hright : WeightedBound U s m 1 (fun _ : Base => ((0 : LowJet), t)) :=
    (weightedBound_const U s m ((0 : LowJet), t)).mono_const hc
  have hsum := hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const) contDiffOn_const hright
  have hp : WeightedBound U s m (B + 1) (fun p => (Q p, t)) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hsum
  exact hp.mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedCoefficientVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A low-jet coefficient variation is linear in the varied map and loses
only the two derivatives in its second jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem compact_low_coefficient_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → E} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : Base → LowJet) (s : ℝ), 0 < s →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s m D (fun p => c (Q p, t)) := by
  have hsub : K ×ˢ Set.Icc (0 : ℝ) 1 ⊆ O ×ˢ Set.univ :=
    fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
  obtain ⟨D, hD, hb⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn
    (hO.prod isOpen_univ).uniqueDiffOn (hK.prod isCompact_Icc) hsub hc m
  refine ⟨(m.factorial : ℝ) * D * (2 * B) ^ m, by positivity, ?_⟩
  intro Q s hs hQ hQK hQB t ht
  exact hb (fun p => (Q p, t)) s (2 * B) hs (by linarith)
    (hQ.prodMk contDiffOn_const) (fun p hp => ⟨hQK hp, ht⟩)
    (weighted_lowJet_pair hU hQ hs hB m hQB ht)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedJetPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

lemma ofExpression_loss (e : Expression) : (ofExpression e).loss = e.loss := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, loss, ↓reduceIte, Expression.loss, ih]
  | add _ _ ihe ihf => simp only [ofExpression, loss, Expression.loss, ihe, ihf]

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (h : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem loss_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).loss ≤ e.loss + 2 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    simpa only [loss, Fin.succ_ne_zero, ↓reduceIte, Nat.add_zero] using hl
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      simp only [differentiate, loss, Fin.succ_ne_zero, ↓reduceIte]
      omega
    · simp only [differentiate, hi, ↓reduceIte, loss]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, loss]
    omega

theorem loss_third_variation (e : Expression) :
    ((((ofExpression e).differentiate 0).differentiate 1).differentiate 2).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  omega

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (hN : 2 ≤ N) (h : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma order_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).order ≤ e.order := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ 2 (le_refl 2)
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    exact max_le hl (le_refl 2)
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, order]
    omega

lemma order_ofExpression (e : Expression) : (ofExpression e).order = e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, order, Expression.order, ih]
  | add _ _ ihe ihf => simp only [ofExpression, order, Expression.order, ihe, ihf]

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

lemma variations_order (e : Expression) (i : Fin 3) : (e.variations i).order ≤ e.order := by
  have h₁ := order_differentiate 0 (ofExpression e)
  have h₂ := order_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := order_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [order_ofExpression] at h₁
  fin_cases i
  · exact h₁
  · exact h₂.trans h₁
  · exact h₃.trans (h₂.trans h₁)

lemma variations_loss (e : Expression) (i : Fin 3) : (e.variations i).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  fin_cases i
  · change ((ofExpression e).differentiate 0).loss ≤ e.loss + 6
    omega
  · change (((ofExpression e).differentiate 0).differentiate 1).loss ≤ e.loss + 6
    omega
  · exact loss_third_variation e

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedComplexMixedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-scale evaluation: the output is measured at the slow scale, while
only the explicit jet excess contributes short-scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

theorem compact_complex_mixed_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : MixedExpression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (J : JetData) (s τ : ℝ),
      0 < s → 0 < τ → τ ≤ 1 → ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) U K →
      WeightedBound U s m B (lowJet G) →
      (∀ i w a, ContDiffOn ℝ ∞ (J i w a) U) →
      (∀ i w a, w.length ≤ e.order →
        WeightedBound U s m (B / τ ^ slotLoss i w) (J i w a)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / τ ^ e.loss) (fun p => e.evalComplex G J (p, t)) := by
  induction e with
  | coeff c =>
    have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn he
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient_vector hU hO hK hKO hc m B hB
    refine ⟨D, hD, ?_⟩
    intro G J s τ hs _ _ hG hGK hb _ _ t ht
    simpa only [loss, pow_zero, div_one, evalComplex, Function.comp_def,
      Complex.ofRealCLM_apply] using hd (lowJet G) s hs (lowJet_smooth hG).contDiffOn hGK hb t ht
  | atom i w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have htBound := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun j v b hv => hJB j v b (hv.trans (le_max_right _ _))) t ht
    have hjBound := hJB i w a (le_max_left _ _)
    have hp := hjBound.mul hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (hJ i w a) (evalComplex_parameter_smooth hG hQ hJ (e := e) he t) htBound
    convert hp using 1 <;> first | rfl | simp only [loss, slotLoss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_left _ _))) t ht
    have hc' := hc G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_right _ _))) t ht
    have hd'' : WeightedBound U s m (D / τ ^ max e.loss f.loss)
        (fun p => e.evalComplex G J (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / τ ^ max e.loss f.loss)
        (fun p => f.evalComplex G J (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_right _ _)))
    simpa only [loss, add_div, evalComplex] using hd''.add hU.uniqueDiffOn hs.le
      (evalComplex_parameter_smooth hG hQ hJ (e := e) he.1 t)
      (evalComplex_parameter_smooth hG hQ hJ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedModulatedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slow-scale bounds on the amplitudes of fast oscillatory jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

lemma weighted_complexify {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)

lemma weighted_amplitudeDerivative {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hb : WeightedBound U s (m + 1) C Z) (v : Base) (hv : ‖v‖ ≤ 1)
    (hp : WeightedBound U s m P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m ((1 + 2 ^ m * P) * C / τ) (amplitudeDerivative τ φ v Z) := by
  have hd := (hb.directional hU hs hZ.contDiffOn v).mono_const
    (mul_le_of_le_one_left (div_nonneg hC hs.le) hv)
  have hd' := hd.mono_const (div_le_div_of_nonneg_left hC hτ hτs)
  have hds : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))
  have hc := weighted_complexify hU.uniqueDiffOn hs.le hP hds.contDiffOn hp
  have hcs := Complex.ofRealCLM.contDiff.comp hds
  have hc' := hc.const_mul hU.uniqueDiffOn hcs.contDiffOn (Complex.I / (τ : ℂ))
  have hn : ‖Complex.I / (τ : ℂ)‖ = 1 / τ := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [hn] at hc'
  have hcm := (contDiff_const (c := Complex.I / (τ : ℂ))).mul hcs
  have hz := hc'.mul hU.uniqueDiffOn hs.le (by positivity) hC hcm.contDiffOn hZ.contDiffOn
    (hb.mono_order (Nat.le_succ m))
  have ha := hd'.add hU.uniqueDiffOn hs.le
    ((hZ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))).contDiffOn
    (hcm.mul hZ).contDiffOn hz
  convert ha using 1 <;> first | rfl | ring

lemma jetConstant_nonneg {P : ℝ} (hP : 0 ≤ P) (m r : ℕ) : 0 ≤ jetConstant P m r := by
  induction r generalizing m with
  | zero => exact zero_le_one
  | succ r ih => exact mul_nonneg (by positivity) (ih (m + 1))

/-- Output derivatives remain at the slow scale. Only the length of the jet
word contributes short-scale powers. -/
theorem weighted_amplitudeJet {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (w : List Base)
    (hw : ∀ v ∈ w, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + w.length) C Z)
    (hp : ∀ v ∈ w, WeightedBound U s (m + w.length) P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m (jetConstant P m w.length * C / τ ^ w.length)
      (amplitudeJet τ φ w Z) := by
  induction w generalizing m with
  | nil => simpa only [amplitudeJet, List.length_nil, Nat.add_zero, jetConstant, one_mul, pow_zero, div_one] using hb
  | cons v w ih =>
    have hlen : m + (v :: w).length = (m + 1) + w.length := by simp; omega
    have hb' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) (m + 1)
      (hlen ▸ hb) (fun x hx => hlen ▸ hp x (List.mem_cons_of_mem _ hx))
    have hd := weighted_amplitudeDerivative hU hτ hs hτs
      (div_nonneg (mul_nonneg (jetConstant_nonneg hP _ _) hC) (pow_nonneg hτ.le _)) hP
      hφ (amplitudeJet_smooth hφ hZ τ w) hb' v (hw v (List.mem_cons_self ..))
      ((hp v (List.mem_cons_self ..)).mono_order (by simp))
    convert hd using 1
    · simp only [List.length_cons, jetConstant, pow_succ]
      ring
    · rfl

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetDataBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite-order budget for all demodulated jet slots. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

lemma amplitudeBudget_ge_one {N m : ℕ} {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) :
    1 ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma le_amplitudeBudget {N m : ℕ} {B P : ℝ} (hP : 0 ≤ P) :
    B ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma jetConstant_le_amplitudeBudget {N m r : ℕ} {B P : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hr : r ≤ N) :
    jetConstant P m r ≤ amplitudeBudget N m B P := by
  have h := Finset.single_le_sum (fun a _ => jetConstant_nonneg hP m a)
    (show r ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
  dsimp only [amplitudeBudget]
  linarith

theorem weighted_amplitudeData {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) {τ s B P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (m N : ℕ) (hGb : WeightedBound U s (m + N) B (lowJet G))
    (hHb : ∀ j, WeightedBound U s (m + N) 1 (H j))
    (hφb : ∀ j v, WeightedBound U s (m + N) P (fun p => fderiv ℝ (φ j) p (coordinateVector v)))
    (i : Fin 4) (w : List (Fin 2)) (a : Fin 4) (hw : w.length ≤ N) :
    WeightedBound U s m (amplitudeBudget N m B P / τ ^ slotLoss i w)
      (amplitudeData G φ H τ i w a) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hj := weighted_actual_jet hU hG hs hB m w a (hGb.mono_order (by omega))
    have hc := weighted_complexify hU.uniqueDiffOn hs.le (by positivity)
      (jet_smooth hG w a).contDiffOn hj
    apply hc.mono_const
    calc
      B / s ^ (w.length - 2) ≤ B / τ ^ (w.length - 2) :=
        div_le_div_of_nonneg_left hB (pow_pos hτ _) (pow_le_pow_left₀ hτ.le hτs _)
      _ ≤ _ := div_le_div_of_nonneg_right (le_amplitudeBudget hP) (pow_nonneg hτ.le _)
  · have hcomp := (hHb j).component hU.uniqueDiffOn hs.le zero_le_one (hH j).contDiffOn a
    have hc := weighted_amplitudeJet hU hτ hs hτs zero_le_one hP
      (hφ j) (contDiff_pi.mp (hH j) a) (w.map coordinateVector)
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact norm_coordinateVector_le v) m
      (hcomp.mono_order (by simp only [List.length_map]; omega))
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact (hφb j v).mono_order (by simp only [List.length_map]; omega))
    simp only [List.length_map, mul_one] at hc
    apply hc.mono_const
    exact div_le_div_of_nonneg_right (jetConstant_le_amplitudeBudget hB hP hw)
      (pow_nonneg hτ.le _)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp slow-scale estimates for the first three conjugated polynomial
variations. The power E+6 is independent of correction accuracy and order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

/-- Unit amplitude bounds give the sharp exponent for every first, second,
and third variation after removing all participating phase factors. -/
theorem compact_conjugated_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) 1 (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m (D / τ ^ (e.loss + 6))
          (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  classical
  let A := amplitudeBudget e.order m B P
  have hA : 1 ≤ A := amplitudeBudget_ge_one (zero_le_one.trans hB) hP
  have hex := fun i : Fin 3 => compact_complex_mixed_bound hU hO hK hKO (e.variations i)
    (e.variations_smoothCoeffs hO he i) m A hA
  choose D hD hb using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G φ H s τ hτ hs hτs hs1 hG hφ hH hGK hGb hHb hφb t ht i
  have hdata := weighted_amplitudeData hU hG hφ hH hτ hs hτs (zero_le_one.trans hB) hP
    m e.order hGb hHb hφb
  have h := hb i G (amplitudeData G φ H τ) s τ hs hτ (hτs.trans hs1) hG hGK
    ((hGb.mono_order (by omega)).mono_const (le_amplitudeBudget hP))
    (fun j w a => (amplitudeData_smooth hG hφ hH τ j w a).contDiffOn)
    (fun j w a hw => hdata j w a (hw.trans (e.variations_order i))) t ht
  have hbound : D i / τ ^ (e.variations i).loss ≤ (∑ j, D j) / τ ^ (e.loss + 6) := by
    calc
      _ ≤ D i / τ ^ (e.loss + 6) := div_le_div_of_nonneg_left (hD i) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (e.variations_loss i))
      _ ≤ _ := div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)) (pow_nonneg hτ.le _)
  apply (h.mono_const hbound).congr
  intro p _
  exact conjugatedVariation_eq e G hφ hH τ i (p, t)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetScaling
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling each oscillatory amplitude independently. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

lemma amplitudeDerivative_real_smul {Z : Base → ℂ} (hZ : ContDiff ℝ ∞ Z)
    (φ : Base → ℝ) (τ c : ℝ) (v : Base) :
    amplitudeDerivative τ φ v (fun p => c • Z p) =
      fun p => c • amplitudeDerivative τ φ v Z p := by
  funext p
  have hd := congrArg (fun L : Base →L[ℝ] ℂ => L v)
    (((hZ.differentiable (by simp) p).hasFDerivAt.const_smul c).fderiv)
  change fderiv ℝ (fun q => c • Z q) p v = c • fderiv ℝ Z p v at hd
  change fderiv ℝ (fun q => c • Z q) p v + _ = _
  rw [hd]
  simp only [amplitudeDerivative, Complex.real_smul]
  ring

lemma amplitudeJet_real_smul {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ c : ℝ) (w : List Base) :
    amplitudeJet τ φ w (fun p => c • Z p) = fun p => c • amplitudeJet τ φ w Z p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [amplitudeJet, ih]
    exact amplitudeDerivative_real_smul (amplitudeJet_smooth hφ hZ τ w) φ τ c v

lemma scaleDirections_smooth {H : DirectionFields} (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (c : Fin 3 → ℝ) : ∀ j, ContDiff ℝ ∞ (scaleDirections H c j) :=
  fun j => ContDiff.const_smul (c j) (hH j)

lemma amplitudeData_scale (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (c : Fin 3 → ℝ) :
    amplitudeData G φ (scaleDirections H c) τ =
      scaleJets (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) := by
  funext i w a p
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (scaleJets_base (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) w a p).symm
  · rw [scaleJets_succ]
    change amplitudeJet τ (φ j) (w.map coordinateVector) (fun q => c j • H j q a) p = _
    rw [amplitudeJet_real_smul (hφ j) (contDiff_pi.mp (hH j) a)]
    rfl

lemma conjugatedVariation_scale (e : Expression) (G : Base → Space)
    {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (τ : ℝ) (c : Fin 3 → ℝ) (i : Fin 3) (z : Base × ℝ) :
    conjugatedVariation e G φ (scaleDirections H c) τ i z =
      (c 0 * (if 1 ≤ i then c 1 else 1) * (if 2 ≤ i then c 2 else 1)) •
        conjugatedVariation e G φ H τ i z := by
  rw [conjugatedVariation_eq e G hφ (scaleDirections_smooth hH c),
    conjugatedVariation_eq e G hφ hH, amplitudeData_scale G hφ hH τ c]
  have h := evalComplex_scaleJets (fun j => e.variations_degree i j) G
    (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) z
  fin_cases i <;> simpa [Complex.real_smul] using h

lemma scaleDirections_inverse (H : DirectionFields) (C : Fin 3 → ℝ) (hC : ∀ j, C j ≠ 0) :
    scaleDirections (scaleDirections H (fun j => (C j)⁻¹)) C = H := by
  funext j p
  simp only [scaleDirections, smul_smul, mul_inv_cancel₀ (hC j), one_smul]

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedMultilinearBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated polynomial estimates retain the product of the input
amplitude bounds. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

/-- Product estimate corresponding to the fixed-power perturbation bound
in the small-modes argument. No output-order or accuracy dependence is
hidden in the short-scale exponent. -/
theorem compact_conjugated_multilinear_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ (e.loss + 6)) (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  obtain ⟨D, hD, hb⟩ := compact_conjugated_variation_bound hU hO hK hKO e he m B P hB hP
  refine ⟨D, hD, ?_⟩
  intro G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let V := scaleDirections H (fun j => (C j)⁻¹)
  have hV := scaleDirections_smooth hH (fun j => (C j)⁻¹)
  have hunit : ∀ j, WeightedBound U s (m + e.order) 1 (V j) := by
    intro j
    have h := (hHb j).const_smul hU.uniqueDiffOn (hH j).contDiffOn (C j)⁻¹
    change WeightedBound U s (m + e.order) 1 (fun p => (C j)⁻¹ • H j p)
    simpa only [abs_of_pos (inv_pos.mpr (hC j)),
      inv_mul_cancel₀ (ne_of_gt (hC j))] using h
  have hbound := hb G φ V s τ hτ hs hτs hs1 hG hφ hV hGK hGb hunit hφb t ht i
  let W : ℝ := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 < W := by
    have h₀ := hC 0
    have h₁ := hC 1
    have h₂ := hC 2
    dsimp only [W]
    split_ifs <;> positivity
  have heq : (fun p => conjugatedVariation e G φ H τ i (p, t)) =
      (fun p => W • conjugatedVariation e G φ V τ i (p, t)) := by
    funext p
    have h := conjugatedVariation_scale e G hφ hV τ C i (p, t)
    rw [scaleDirections_inverse H C (fun j => ne_of_gt (hC j))] at h
    exact h
  rw [heq]
  have hsmooth : ContDiffOn ℝ ∞ (fun p => conjugatedVariation e G φ V τ i (p, t)) U := by
    have h := evalComplex_parameter_smooth hG (fun p hp => hKO (hGK hp))
      (fun j w a => (amplitudeData_smooth hG hφ hV τ j w a).contDiffOn)
      (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact conjugatedVariation_eq e G hφ hV τ i (p, t)
  have h := hbound.const_smul hU.uniqueDiffOn hsmooth W
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos hW]
  ring

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial perturbations have one fixed short-scale exponent. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

variable {n : ℕ}

/-- The perturbation parameter enters linearly in the bound, and the single
short-scale loss works at every requested output order. -/
theorem compact_conjugated_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B Q : ℝ) (hB : 1 ≤ B) (hQ : 0 ≤ Q) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ ε : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ j, WeightedBound U s (m + order P) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + order P) Q
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * ε * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ loss P) (fun p => conjugated P ε G φ H τ i (p, t)) := by
  classical
  have hex := fun l => compact_conjugated_multilinear_bound hU hO hK hKO (P l) (hP l) m B Q hB hQ
  choose D hD hb using hex
  refine ⟨∑ l, D l, Finset.sum_nonneg (fun l _ => hD l), ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let W := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 ≤ W := by
    have h₀ := (hC 0).le
    have h₁ := (hC 1).le
    have h₂ := (hC 2).le
    dsimp only [W]
    split_ifs <;> positivity
  have hval (l : Fin n) : WeightedBound U s m (D l * ε * W / τ ^ loss P)
      (fun p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t)) := by
    have hl : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hh := hb l G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK
      (hGb.mono_order (Nat.add_le_add_left hl m))
      (fun j => (hHb j).mono_order (Nat.add_le_add_left hl m))
      (fun j v => (hφb j v).mono_order (Nat.add_le_add_left hl m)) t ht i
    have hsmooth := conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t
    have hh' : WeightedBound U s m (D l * W / τ ^ loss P)
        (fun p => conjugatedVariation (P l) G φ H τ i (p, t)) :=
      hh.mono_const (div_le_div_of_nonneg_left (mul_nonneg (hD l) hW) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
          (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))))
    have hscaled := hh'.const_smul hU.uniqueDiffOn hsmooth (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have heps : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l * W / τ ^ loss P) :=
        mul_le_mul_of_nonneg_right heps
          (div_nonneg (mul_nonneg (hD l) hW) (pow_nonneg hτ.le _))
      _ = _ := by ring
  have hsum := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l * ε * W / τ ^ loss P)
    (fun l p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t))
    (fun l _ => (conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t).const_smul _) (fun l _ => hval l)
  simpa only [conjugated, ← Finset.sum_div, ← Finset.sum_mul, W] using hsum

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedOperatorBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-loss conjugated estimate for the actual supported linear map. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma supportedField_eq_zero_of_seminorm_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Compacts Base} (s : ℝ≥0) (m : ℕ)
    {f : SupportedField (F := F) K} (hf : supportedWeightedSeminorm K s m f = 0) : f = 0 := by
  apply DFunLike.ext
  intro p
  have h := (weightedBound_of_supportedSeminorm s m f).norm_le (Set.mem_univ p)
  rw [hf] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformFreeModeConstants
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit free-mode constants, independent of both short scales and
of the perturbation size. These constants are used before selecting scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma freeModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (q m : ℕ) :
    0 ≤ freeModeBudget n L B D q m := by
  apply add_nonneg _ (amplitudeConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) _ _

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalizedPerturbedDifference
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized metric mean has the finite-loss difference estimate
needed for repeated substitution of trial amplitudes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

lemma supportedFreeSeed_sub (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (b c : SupportedField (F := ℝ) K) :
    supportedFreeSeed δ τ hF h K hKU (b - c) =
      supportedFreeSeed δ τ hF h K hKU b - supportedFreeSeed δ τ hF h K hKU c := by
  apply DFunLike.ext
  intro p
  exact congrFun (freeSeed_sub δ τ b c F) p

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CorrectedNormalSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit size and difference budgets for the actual corrected normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

lemma correctedSeedBudget_nonneg (L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (q m : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ correctedSeedBudget L B D q m N := by
  have h := freeModeBudget_nonneg 4 L B D hB q m
  dsimp only [correctedSeedBudget]
  positivity

lemma correctedNormalSeed_sub (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b c : SupportedField (F := ℝ) K) :
    correctedNormalSeed δ τ hF h K hKU R q (b - c) =
      correctedNormalSeed δ τ hF h K hKU R q b - correctedNormalSeed δ τ hF h K hKU R q c := by
  simp only [correctedNormalSeed, supportedFreeSeed_sub, map_sub]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanCoefficient
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial contribution to the quadratic zero-phase coefficient. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma weighted_starField {U : Set Base} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {H : Base → Fin 4 → ℂ} (hs : 0 < s) (hC : 0 ≤ C) (hH : ContDiff ℝ ∞ H)
    (hb : WeightedBound U s m C H) : WeightedBound U s m C (starField H) := by
  apply WeightedBound.pi hU hs hC
  · intro a
    exact (Complex.conjCLE.contDiff.comp (contDiff_pi.mp hH a)).contDiffOn
  · intro a
    have hh := (hb.component hU hs.le hC hH.contDiffOn a).linear hU hs.le
      (contDiff_pi.mp hH a).contDiffOn Complex.conjCLE.toContinuousLinearMap
    apply hh.mono_const
    apply mul_le_of_le_one_left hC
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteQuadraticVariation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums in the actual complexified Hessian. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma complexJet_add {H K : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    complexJet (fun p => H p + K p) = complexJet H + complexJet K := by
  funext w a p
  exact congrFun (directional_add (contDiff_pi.mp hH a) (contDiff_pi.mp hK a)
    (w.map coordinateVector)) p

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanPair
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear form underlying the polynomial zero-phase correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma starDirectionJets_add (J K : DirectionJets) :
    starDirectionJets (J + K) = starDirectionJets J + starDirectionJets K := by
  funext w a p
  exact star_add _ _

namespace Perturbation

lemma quadraticMeanPair_add_left {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ (fun x => H x + K x) L τ t p =
      quadraticMeanPair P ε G φ H L τ t p + quadraticMeanPair P ε G φ K L τ t p := by
  have he : (fun x => phase τ φ x • (H x + K x)) =
      fun x => phase τ φ x • H x + phase τ φ x • K x := by funext x; exact smul_add _ _ _
  simp only [quadraticMeanPair, he, complexJet_add (H := fun p => phase τ φ p • H p) (K := fun p => phase τ φ p • K p)
    ((phase_smooth hφ τ).smul hH)
    ((phase_smooth hφ τ).smul hK), quadraticComplex_add_left, Complex.add_re, mul_add, add_div,
    Finset.sum_add_distrib]

lemma quadraticMeanPair_add_right {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ L (fun x => H x + K x) τ t p =
      quadraticMeanPair P ε G φ L H τ t p + quadraticMeanPair P ε G φ L K τ t p := by
  have he : (fun x => phase τ φ x • (H x + K x)) =
      fun x => phase τ φ x • H x + phase τ φ x • K x := by funext x; exact smul_add _ _ _
  simp only [quadraticMeanPair, he, complexJet_add (H := fun p => phase τ φ p • H p) (K := fun p => phase τ φ p • K p)
    ((phase_smooth hφ τ).smul hH)
    ((phase_smooth hφ τ).smul hK), starDirectionJets_add, quadraticComplex_add_right,
    Complex.add_re, mul_add, add_div, Finset.sum_add_distrib]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanDifference
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Difference identity for the actual polynomial zero-phase mean. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma quadraticMeanPair_sub_left {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ (fun x => H x - K x) L τ t p =
      quadraticMeanPair P ε G φ H L τ t p - quadraticMeanPair P ε G φ K L τ t p := by
  have hh := quadraticMeanPair_add_left P ε G hφ (hH.sub hK) hK L τ t p
  have he : (fun x => (H x - K x) + K x) = H := by funext x; exact sub_add_cancel _ _
  rw [he] at hh
  exact eq_sub_of_add_eq hh.symm

lemma quadraticMeanPair_sub_right {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ L (fun x => H x - K x) τ t p =
      quadraticMeanPair P ε G φ L H τ t p - quadraticMeanPair P ε G φ L K τ t p := by
  have hh := quadraticMeanPair_add_right P ε G hφ (hH.sub hK) hK L τ t p
  have he : (fun x => (H x - K x) + K x) = H := by funext x; exact sub_add_cancel _ _
  rw [he] at hh
  exact eq_sub_of_add_eq hh.symm

lemma quadraticMeanCoefficient_difference {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (τ t : ℝ) (p : Base) :
    quadraticMeanCoefficient P ε G φ H τ t p - quadraticMeanCoefficient P ε G φ K τ t p =
      quadraticMeanPair P ε G φ (fun x => H x - K x) H τ t p +
        quadraticMeanPair P ε G φ K (fun x => H x - K x) τ t p := by
  rw [quadraticMeanPair_sub_left P ε G hφ hH hK,
    quadraticMeanPair_sub_right P ε G hφ hH hK,
    quadraticMeanPair_self P ε G hφ hH, quadraticMeanPair_self P ε G hφ hK]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanPairBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product estimates for the two independent amplitudes of the polynomial mean. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

lemma quadraticMeanPair_eq {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (H : Base → Fin 4 → ℂ)
    {K : Base → Fin 4 → ℂ} (hK : ContDiff ℝ ∞ K) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ H K τ t p =
      (conjugated P ε G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 (p, t)).re / 4 := by
  simp only [quadraticMeanPair, quadraticComplex_opposite_phases _ G hφ hK,
    conjugated, Complex.re_sum, Complex.real_smul, Finset.sum_div,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem quadraticMeanPair_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (H K : Base → Fin 4 → ℂ) (s τ ε C D : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ φ → ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      WeightedBound U s (m + order P) C H → WeightedBound U s (m + order P) D K →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / τ ^ loss P) (quadraticMeanPair P ε G φ H K τ t) := by
  obtain ⟨E, hE, he⟩ := compact_conjugated_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E / 4, div_nonneg hE (by norm_num), ?_⟩
  intro G φ H K s τ ε C D hτ hs hτs hs1 hε hε1 hC hD hG hφ hH hK hGQ hGb hHb hKb hφb t ht
  have hpb : ∀ j v, WeightedBound U s (m + order P) F
      (fun p => fderiv ℝ (pairPhases φ (fun p => -φ p) j) p (coordinateVector v)) := by
    intro j v
    fin_cases j
    · exact hφb v
    · have hh := (hφb v).neg hU.uniqueDiffOn
        ((hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).contDiffOn
      change WeightedBound U s (m + order P) F
        (fun p => fderiv ℝ (fun q => -φ q) p (coordinateVector v))
      simpa only [fderiv_fun_neg, neg_apply] using hh
    · change WeightedBound U s (m + order P) F (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
      simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
        (weightedBound_zero U s (m + order P)).mono_const hF
  have hhb : ∀ j, WeightedBound U s (m + order P) (![C, D, 1] j) (pairDirections H (starField K) j) := by
    intro j
    fin_cases j
    · exact hHb
    · exact weighted_starField hU.uniqueDiffOn hs hD.le hK hKb
    · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
  have hh := he G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) s τ ε ![C, D, 1]
    hτ hs hτs hs1 hε hε1 (fun j => by fin_cases j; exact hC; exact hD; norm_num)
    hG (pairPhases_smooth hφ hφ.neg) (pairDirections_smooth hH (starField_smooth hK))
    hGQ hGb hhb hpb t ht 1
  have hsm : ContDiffOn ℝ ∞ (fun p => conjugated P ε G
      (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 (p, t)) U :=
    ContDiffOn.sum fun l _ =>
      (conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hφ.neg)
        (pairDirections_smooth hH (starField_smooth hK)) hO (fun _ hp => hQO (hGQ hp)) τ 1 t).const_smul _
  have hr := hh.linear hU.uniqueDiffOn hs.le hsm Complex.reCLM
  have hn : 0 ≤ E * ε * (C * D * 1) / τ ^ loss P := by positivity
  have hr' := hr.mono_const (mul_le_of_le_one_left hn (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : ‖Complex.reCLM‖ ≤ 1))
  have hf := hr'.const_smul hU.uniqueDiffOn (Complex.reCLM.contDiff.comp_contDiffOn hsm) (1 / 4 : ℝ)
  have hfun : (fun p => (1 / 4 : ℝ) • Complex.reCLM
      (conjugated P ε G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 (p, t))) =
      quadraticMeanPair P ε G φ H K τ t := by
    funext p
    rw [quadraticMeanPair_eq P ε G hφ H hK]
    simp only [Complex.reCLM_apply, smul_eq_mul]
    ring
  change WeightedBound U s m _ _ at hf
  rw [Function.comp_def, hfun] at hf
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 3) ≤ 1 by decide,
    show ¬ (2 : Fin 3) ≤ 1 by decide, ↓reduceIte, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedPolynomialMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-phase Hessian estimate in the actual supported seminorms. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadraticMeanPair_zero_left {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ 0 K τ t p = 0 := by
  have hh := quadraticMeanPair_add_left P ε G hφ
    (H := 0) (K := 0) contDiff_const contDiff_const K τ t p
  have he : (fun x => (0 : Base → Fin 4 → ℂ) x + (0 : Base → Fin 4 → ℂ) x) = 0 := by
    funext x
    exact zero_add _
  rw [he] at hh
  linarith

lemma quadraticMeanPair_zero_right {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ H 0 τ t p = 0 := by
  have hh := quadraticMeanPair_add_right P ε G hφ
    (H := 0) (K := 0) contDiff_const contDiff_const H τ t p
  have he : (fun x => (0 : Base → Fin 4 → ℂ) x + (0 : Base → Fin 4 → ℂ) x) = 0 := by
    funext x
    exact zero_add _
  rw [he] at hh
  linarith

theorem supported_quadraticMeanPair_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (_hG : ContDiff ℝ ∞ G) (_hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
      (H J : SupportedField (F := Fin 4 → ℂ) K) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * supportedWeightedSeminorm K s (m + order P) H *
          supportedWeightedSeminorm K s (m + order P) J / τ ^ loss P)
          (quadraticMeanPair P ε G φ H J τ t) := by
  obtain ⟨E, hE, he⟩ := quadraticMeanPair_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ hG hφ K H J s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
  let C := supportedWeightedSeminorm K s (m + order P) H
  let D := supportedWeightedSeminorm K s (m + order P) J
  have hC : 0 ≤ C := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  change WeightedBound U s m (E * ε * C * D / τ ^ loss P) _
  by_cases hC0 : C = 0
  · have hH0 : H = 0 := supportedField_eq_zero_of_seminorm_eq_zero s (m + order P) hC0
    have hfun : (H : Base → Fin 4 → ℂ) = 0 := congrArg
      (fun Z : SupportedField (F := Fin 4 → ℂ) K => (Z : Base → Fin 4 → ℂ)) hH0
    have hz : quadraticMeanPair P ε G φ H J τ t = 0 := by
      funext x
      rw [hfun]
      exact quadraticMeanPair_zero_left P ε G hφ J τ t x
    rw [hC0, mul_zero, zero_mul, zero_div, hz]
    exact weightedBound_zero U s m
  by_cases hD0 : D = 0
  · have hJ0 : J = 0 := supportedField_eq_zero_of_seminorm_eq_zero s (m + order P) hD0
    have hfun : (J : Base → Fin 4 → ℂ) = 0 := congrArg
      (fun Z : SupportedField (F := Fin 4 → ℂ) K => (Z : Base → Fin 4 → ℂ)) hJ0
    have hz : quadraticMeanPair P ε G φ H J τ t = 0 := by
      funext x
      rw [hfun]
      exact quadraticMeanPair_zero_right P ε G hφ H τ t x
    rw [hD0, mul_zero, zero_div, hz]
    exact weightedBound_zero U s m
  exact he G φ H J s τ ε C D hτ hs hτs hs1 hε hε1
    (lt_of_le_of_ne hC (Ne.symm hC0)) (lt_of_le_of_ne hD (Ne.symm hD0))
    hG hφ H.contDiff J.contDiff hGQ hGb
    ((weightedBound_of_supportedSeminorm s (m + order P) H).restrict_open hU)
    ((weightedBound_of_supportedSeminorm s (m + order P) J).restrict_open hU) hφb t ht

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedPolynomialMeanDifference
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-loss difference estimate for the actual polynomial mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadraticMeanPair_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Base → Space} {φ : Base → ℝ} {H J : Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
    (hH : ContDiff ℝ ∞ H) (hJ : ContDiff ℝ ∞ J)
    (hQ : Set.MapsTo (lowJet G) U O) (ε τ t : ℝ) :
    ContDiffOn ℝ ∞ (quadraticMeanPair P ε G φ H J τ t) U := by
  have hs := fun l => conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hφ.neg)
    (pairDirections_smooth hH (starField_smooth hJ)) hO hQ τ 1 t
  have hh : ContDiffOn ℝ ∞ (fun p =>
      (conjugated P ε G (pairPhases φ (fun p => -φ p))
        (pairDirections H (starField J)) τ 1 (p, t)).re / 4) U :=
    (Complex.reCLM.contDiff.comp_contDiffOn
    (ContDiffOn.sum fun l _ => (hs l).const_smul (ε ^ (l.val + 1)))).div_const 4
  have he : quadraticMeanPair P ε G φ H J τ t =
      fun p => (conjugated P ε G (pairPhases φ (fun p => -φ p))
        (pairDirections H (starField J)) τ 1 (p, t)).re / 4 := by
    funext p
    exact quadraticMeanPair_eq P ε G hφ H hJ τ t p
  rw [he]
  exact hh

theorem supported_quadraticMean_difference {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (_hG : ContDiff ℝ ∞ G) (_hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
      (H J : SupportedField (F := Fin 4 → ℂ) K) (s : ℝ≥0) (τ ε A D : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 ≤ A → 0 ≤ D →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      supportedWeightedSeminorm K s (m + order P) H ≤ A →
      supportedWeightedSeminorm K s (m + order P) J ≤ A →
      supportedWeightedSeminorm K s (m + order P) (H - J) ≤ D →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (2 * E * ε * A * D / τ ^ loss P)
          (fun p => quadraticMeanCoefficient P ε G φ H τ t p -
            quadraticMeanCoefficient P ε G φ J τ t p) := by
  obtain ⟨E, hE, he⟩ := supported_quadraticMeanPair_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ hG hφ K H J s τ ε A D hτ hs hτs hs1 hε hε1 hA hD hGQ hGb hφb hH hJ hHJ t ht
  have h1 := he G φ hG hφ K (H - J) H s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
  have h2 := he G φ hG hφ K J (H - J) s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
  have h1' := h1.mono_const (show E * ε * supportedWeightedSeminorm K s _ (H - J) *
      supportedWeightedSeminorm K s _ H / τ ^ loss P ≤ E * ε * D * A / τ ^ loss P by gcongr)
  have h2' := h2.mono_const (show E * ε * supportedWeightedSeminorm K s _ J *
      supportedWeightedSeminorm K s _ (H - J) / τ ^ loss P ≤ E * ε * A * D / τ ^ loss P by gcongr)
  have hHQ : Set.MapsTo (lowJet G) U O := fun _ hx => hQO (hGQ hx)
  have hadd := h1'.add hU.uniqueDiffOn hs.le
    (quadraticMeanPair_smooth hO hP hG hφ (H - J).contDiff H.contDiff hHQ ε τ t)
    (quadraticMeanPair_smooth hO hP hG hφ J.contDiff (H - J).contDiff hHQ ε τ t) h2'
  have hfinal := hadd.congr (fun x _ =>
    quadraticMeanCoefficient_difference P ε G hφ (H := H) (K := J) H.contDiff J.contDiff τ t x)
  convert hfinal using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free geometric amplitude in the original coordinates. The same
actual polynomial operator is conjugated into the phase chart, and the
resulting amplitude is transported back with controlled derivative loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open WeightedEstimates RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma originalFreeSeed_sub (δ : ℝ) (q : ℕ)
    (b d : SupportedField (F := ℝ) c.chartCompact) :
    c.originalFreeSeed δ q (b - d) = c.originalFreeSeed δ q b - c.originalFreeSeed δ q d := by
  simp only [originalFreeSeed, freeSeed, correctedNormalSeed_sub, map_sub]

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedPolynomialMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial part of the normalized quadratic mean is O(η), with
finite-loss value and difference bounds and constants chosen before scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma normalized_product_scale {δ τ s ε E A D : ℝ} {r p : ℕ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hA : 0 ≤ A) (hD : 0 ≤ D) (hp : r ≤ p) :
    δ⁻¹ ^ 2 * (E * ε * (A * (δ * τ)) * (D * (δ * τ)) / τ ^ r) ≤
      (τ / s + ε / τ ^ p) * E * A * D := by
  have hfrac : ε / τ ^ r ≤ ε / τ ^ p :=
    div_le_div_of_nonneg_left hε (pow_pos hτ p) (pow_le_pow_of_le_one hτ.le hτ1 hp)
  have hsmall : ε * τ ^ 2 / τ ^ r ≤ τ / s + ε / τ ^ p := by
    calc
      _ = (ε / τ ^ r) * τ ^ 2 := by ring
      _ ≤ ε / τ ^ r := mul_le_of_le_one_right (div_nonneg hε (pow_nonneg hτ.le _))
        (pow_le_one₀ hτ.le hτ1)
      _ ≤ ε / τ ^ p := hfrac
      _ ≤ _ := le_add_of_nonneg_left (div_nonneg hτ.le hs.le)
  calc
    _ = (ε * τ ^ 2 / τ ^ r) * (E * A * D) := by
      field_simp [hδ.ne']
    _ ≤ (τ / s + ε / τ ^ p) * (E * A * D) :=
      mul_le_mul_of_nonneg_right hsmall (mul_nonneg (mul_nonneg hE hA) hD)
    _ = _ := by ring

theorem normalizedPolynomialMean_bounds {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (_hG : ContDiff ℝ ∞ G) (_hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
      (H J : SupportedField (F := Fin 4 → ℂ) K) (s : ℝ≥0) (δ τ ε A D : ℝ) (p : ℕ),
      0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → 0 ≤ A → 0 ≤ D → loss P ≤ p →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      supportedWeightedSeminorm K s (m + order P) H ≤ A * (δ * τ) →
      supportedWeightedSeminorm K s (m + order P) J ≤ A * (δ * τ) →
      supportedWeightedSeminorm K s (m + order P) (H - J) ≤ D * (δ * τ) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m ((τ / s + ε / τ ^ p) * E * A ^ 2)
          (normalizedPolynomialMean P δ ε G φ H τ t) ∧
        WeightedBound U s m ((τ / s + ε / τ ^ p) * (2 * E) * A * D)
          (fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
            normalizedPolynomialMean P δ ε G φ J τ t x) := by
  obtain ⟨Ev, hEv, hv⟩ := supported_quadraticMeanPair_bound hU hO hQ hQO P hP m B F hB hF
  obtain ⟨Ed, hEd, hd⟩ := supported_quadraticMean_difference hU hO hQ hQO P hP m B F hB hF
  let E := max Ev Ed
  have hE : 0 ≤ E := hEv.trans (le_max_left _ _)
  refine ⟨E, hE, ?_⟩
  intro G φ hG hφ K H J s δ τ ε A D p hδ hτ hs hτs hs1 hε hε1 hA hD hp hGQ hGb hφb hH hJ hHJ t ht
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hsH := quadraticMeanCoefficient_smooth hO hP hG hφ H.contDiff
    (fun _ hx => hQO (hGQ hx)) ε τ t
  have hsJ := quadraticMeanCoefficient_smooth hO hP hG hφ J.contDiff
    (fun _ hx => hQO (hGQ hx)) ε τ t
  constructor
  · have hh := hv G φ hG hφ K H H s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
    have hb := hh.mono_const (show Ev * ε * supportedWeightedSeminorm K s _ H *
        supportedWeightedSeminorm K s _ H / τ ^ loss P ≤
        Ev * ε * (A * (δ * τ)) * (A * (δ * τ)) / τ ^ loss P by gcongr)
    have heq : quadraticMeanPair P ε G φ H H τ t = quadraticMeanCoefficient P ε G φ H τ t := by
      funext x
      exact quadraticMeanPair_self P ε G hφ H.contDiff τ t x
    rw [heq] at hb
    have hscaled := hb.const_smul hU.uniqueDiffOn hsH (δ⁻¹ ^ 2)
    change WeightedBound U s m _ (normalizedPolynomialMean P δ ε G φ H τ t) at hscaled
    rw [abs_of_nonneg (sq_nonneg δ⁻¹)] at hscaled
    apply hscaled.mono_const
    calc
      _ ≤ (τ / s + ε / τ ^ p) * Ev * A * A :=
        normalized_product_scale hδ hτ hs hτ1 hε hEv hA hA hp
      _ ≤ (τ / s + ε / τ ^ p) * E * A * A := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  · have hh := hd G φ hG hφ K H J s τ ε (A * (δ * τ)) (D * (δ * τ))
      hτ hs hτs hs1 hε hε1 (by positivity) (by positivity) hGQ hGb hφb hH hJ hHJ t ht
    have hscaled := hh.const_smul hU.uniqueDiffOn (hsH.sub hsJ) (δ⁻¹ ^ 2)
    have heq : (fun x => δ⁻¹ ^ 2 • (quadraticMeanCoefficient P ε G φ H τ t x -
        quadraticMeanCoefficient P ε G φ J τ t x)) =
        fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
          normalizedPolynomialMean P δ ε G φ J τ t x := by
      funext x
      simp only [normalizedPolynomialMean, smul_eq_mul, mul_sub]
    rw [heq, abs_of_nonneg (sq_nonneg δ⁻¹)] at hscaled
    apply hscaled.mono_const
    calc
      _ ≤ (τ / s + ε / τ ^ p) * (2 * Ed) * A * D :=
        normalized_product_scale hδ hτ hs hτ1 hε (by positivity) hA hD hp
      _ ≤ _ := by gcongr; exact le_max_right _ _

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedPolynomialSupport
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support and global smoothness of the normalized polynomial mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma normalizedPolynomialMean_extend {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} (hU : IsOpen U) {G : Base → Space} {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H : SupportedField (F := Fin 4 → ℂ) K) (δ ε τ t : ℝ)
    {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C (normalizedPolynomialMean P δ ε G φ H τ t)) :
    WeightedBound Set.univ s m C (normalizedPolynomialMean P δ ε G φ H τ t) :=
  hb.extend_support hU
    (((normalizedPolynomialMean_tsupport P δ ε G hφ H.contDiff τ t).trans H.tsupport_subset).trans hKU) hC

lemma normalizedPolynomialMean_difference_extend {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} (hU : IsOpen U) {G : Base → Space} {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H J : SupportedField (F := Fin 4 → ℂ) K) (δ ε τ t : ℝ)
    {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C (fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
      normalizedPolynomialMean P δ ε G φ J τ t x)) :
    WeightedBound Set.univ s m C (fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
      normalizedPolynomialMean P δ ε G φ J τ t x) := by
  apply hb.extend_support hU _ hC
  apply (tsupport_sub _ _).trans
  apply Set.union_subset
  · exact ((normalizedPolynomialMean_tsupport P δ ε G hφ H.contDiff τ t).trans H.tsupport_subset).trans hKU
  · exact ((normalizedPolynomialMean_tsupport P δ ε G hφ J.contDiff τ t).trans J.tsupport_subset).trans hKU

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformMetricMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric mean budget is fixed before either scale is selected. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma freeMeanBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (q m : ℕ) :
    0 ≤ freeMeanBudget n L B D q m := by
  have hA := freeModeBudget_nonneg n L B D hB q (m + 1)
  unfold freeMeanBudget
  positivity

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformNormalizedMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit constants for the normalized geometric metric mean, independent
of its oscillation and amplitude scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

lemma normalizedMeanBudget_nonneg (L : ℕ) (B D : ℕ → ℝ)
    (hB : ∀ m, 0 ≤ B m) (q m : ℕ) (N : ℝ) :
    0 ≤ normalizedMeanBudget L B D q m N :=
  mul_nonneg (freeMeanBudget_nonneg 4 L B D hB q m) (sq_nonneg _)

end ClosedSurfaceR4.RealModes

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FixedMeanSubstitution
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean correction for one fixed operator with derivative loss.
The smallness threshold is uniform in the operator; no infinite-dimensional
inverse or convergence of a derivative-losing iteration is asserted. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma rescaledMean_self {η : ℝ} (hη : η ≠ 0) (A : (E → F) → E → F) :
    rescaledMean η A η = A := by
  funext f
  simp only [rescaledMean, div_self hη, one_smul]

lemma rescaledMean_bounds {U : Set E} (hU : UniqueDiffOn ℝ U) {s : ℝ}
    {reference : E → F} {r η : ℝ} {L : ℕ} (hη : 0 < η)
    (A : (E → F) → E → F) (B K : ℕ → ℝ → ℝ)
    (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C) (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C)
    (hsm : ∀ f, ContDiffOn ℝ ∞ f U → InTrialBall U reference r f → ContDiffOn ℝ ∞ (A f) U)
    (hv : ∀ m C f, 1 ≤ C → ContDiffOn ℝ ∞ f U → InTrialBall U reference r f →
      WeightedBound U s (m + L) C f → WeightedBound U s m (η * B m C) (A f))
    (hd : ∀ m C D f g, 1 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      InTrialBall U reference r f → InTrialBall U reference r g →
      WeightedBound U s (m + L) C f → WeightedBound U s (m + L) C g →
      WeightedBound U s (m + L) D (f - g) →
      WeightedBound U s m (K m C * η * D) (A f - A g)) :
    MeanBounds U s reference r L (rescaledMean η A) B K := by
  refine ⟨hB, hK, ?_, ?_, ?_⟩
  · intro θ _ _ f hf hb
    exact (hsm f hf hb).const_smul (θ / η)
  · intro θ hθ _ m C f hC hf hb hbf
    have hh := (hv m C f hC hf hb hbf).const_smul hU (hsm f hf hb) (θ / η)
    change WeightedBound U s m _ (rescaledMean η A θ f) at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp
  · intro θ hθ _ m C D f g hC hD hf hg hb hc hbf hbg hbd
    have hh := (hd m C D f g hC hD hf hg hb hc hbf hbg hbd).const_smul hU
      ((hsm f hf hb).sub (hsm g hg hc)) (θ / η)
    have he : (θ / η) • (A f - A g) = rescaledMean η A θ f - rescaledMean η A θ g :=
      smul_sub _ _ _
    change WeightedBound U s m _ ((θ / η) • (A f - A g)) at hh
    rw [he] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedUniformPolynomialMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial mean constant is chosen before the immersion and scales.
Only the fixed polynomial, compact low-jet range and indicated finite bounds
enter the choice. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes

theorem uniform_charted_polynomial_mean {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (C D J : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 1 ≤ J m)
    (k : Fin 3) (q m : ℕ) (B F A N : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F)
    (hA : 0 ≤ A) (hN : 0 ≤ N) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G)
      (φ : Base → ℝ) (K : Compacts Base) (ε τ : ℝ) (s : ℝ≥0)
      (c : PolynomialSolveData P ε G hG φ K τ s),
      c.U = U → c.C = C → c.D = D → c.J = J →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order (P k)) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order (P k)) F
        (fun x => fderiv ℝ φ x (coordinateVector v))) →
      WeightedBound c.e.target s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap) →
      ∀ δ : ℝ, 0 < δ → ∀ (b d : SupportedField (F := ℝ) c.chartCompact) (z : ℝ),
      0 ≤ z →
      supportedWeightedSeminorm c.chartCompact s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) b ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) d ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) (b - d) ≤ A * z →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * E)
        (normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0) ∧
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * (2 * E) * z)
        (fun x => normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0 x -
          normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q d) τ 0 x) := by
  obtain ⟨E₀,hE₀,he⟩ := normalizedPolynomialMean_bounds hU hO hQ hQO
    (P k) (hP k) m B F hB hF
  let r := m + order (P k)
  let S := (r.factorial : ℝ) * J r ^ r * correctedSeedBudget (tensorOrder P) C D q r N
  have hS : 0 ≤ S := mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (zero_le_one.trans (hJ r)) _))
    (correctedSeedBudget_nonneg (tensorOrder P) C D hC q r hN)
  refine ⟨E₀ * (S * A) ^ 2, mul_nonneg hE₀ (sq_nonneg _), ?_⟩
  intro G hG φ K ε τ s c hUeq hCeq hDeq hJeq hτ hs hτs hs1 hε hε1 hsmall hGQ hGb hφb hn
    δ hδ b d z hz hb hd hbd
  have hzb : supportedWeightedSeminorm K s r (c.originalFreeSeed δ q b) ≤ S * A * (δ * τ) := by
    simpa only [S, hCeq, hDeq, hJeq] using
      c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r hA hN hn b hb
  have hzd : supportedWeightedSeminorm K s r (c.originalFreeSeed δ q d) ≤ S * A * (δ * τ) := by
    simpa only [S, hCeq, hDeq, hJeq] using
      c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r hA hN hn d hd
  have hdiff : supportedWeightedSeminorm K s r
      (c.originalFreeSeed δ q b - c.originalFreeSeed δ q d) ≤ S * (A * z) * (δ * τ) := by
    simpa only [S, hCeq, hDeq, hJeq, c.originalFreeSeed_sub] using
      c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r
        (mul_nonneg hA hz) hN hn (b - d) hbd
  have hp : loss (P k) ≤ tensorLoss P :=
    Finset.le_sup (f := fun i => loss (P i)) (Finset.mem_univ k)
  have hh := he G φ hG c.smoothPhase K (c.originalFreeSeed δ q b) (c.originalFreeSeed δ q d)
    s δ τ ε (S * A) (S * (A * z)) (tensorLoss P) hδ hτ hs hτs hs1 hε hε1
    (mul_nonneg hS hA) (mul_nonneg hS (mul_nonneg hA hz)) hp hGQ hGb hφb hzb hzd hdiff 0 (by simp)
  rw [← hUeq] at hh
  constructor
  · convert normalizedPolynomialMean_extend c.openU c.smoothPhase K c.supportU
      (c.originalFreeSeed δ q b) δ ε τ 0 (by positivity) hh.1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · convert normalizedPolynomialMean_difference_extend c.openU c.smoothPhase K c.supportU
      (c.originalFreeSeed δ q b) (c.originalFreeSeed δ q d) δ ε τ 0 (by positivity) hh.2 using 1
    all_goals try with_reducible_and_instances rfl
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedUniformCombinedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform combined mean estimates. Constants precede every scale, map and
actual phase solver with the specified common geometric bounds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

theorem uniform_charted_combined_mean {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (C D J : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 1 ≤ J m)
    (q m : ℕ) (B F A N : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G)
      (φ : Base → ℝ) (K : Compacts Base) (ε τ : ℝ) (s : ℝ≥0)
      (c : PolynomialSolveData P ε G hG φ K τ s),
      c.U = U → c.C = C → c.D = D → c.J = J →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + tensorOrder P) F
        (fun x => fderiv ℝ φ x (coordinateVector v))) →
      WeightedBound c.e.target s
        (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap) →
      ∀ δ : ℝ, 0 < δ → ∀ (b d : SupportedField (F := ℝ) c.chartCompact) (z : ℝ),
      0 ≤ z →
      supportedWeightedSeminorm c.chartCompact s
        (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) b ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) d ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) (b - d) ≤ A * z →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * E)
        (c.combinedMeanField δ q b) ∧
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * (2 * E) * z)
        (fun x => c.combinedMeanField δ q b x - c.combinedMeanField δ q d x) := by
  have ho (k : Fin 3) : order (P k) ≤ tensorOrder P :=
    Finset.le_sup (f := fun i => order (P i)) (Finset.mem_univ k)
  have hi (k : Fin 3) : m + order (P k) + (q + 1) * (tensorOrder P + 1) ≤
      m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1) := by have := ho k; omega
  have hm : m + 1 + (q + 1) * (tensorOrder P + 1) ≤
      m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1) := by omega
  have hex (k : Fin 3) := uniform_charted_polynomial_mean hU hO hQ hQO
    P hP C D J hC hJ k q m B F A N hB hF hA hN
  choose E hE he using hex
  let T := tensorChartBudget m (J m) (J (m + 1))
  let M := normalizedMeanBudget (tensorOrder P) C D q m N
  have hT : 0 ≤ T := tensorChartBudget_nonneg m (zero_le_one.trans (hJ m))
    (zero_le_one.trans (hJ (m + 1)))
  have hM : 0 ≤ M := normalizedMeanBudget_nonneg (tensorOrder P) C D hC q m N
  have hsum : 0 ≤ ∑ k, E k := Finset.sum_nonneg (fun k _ => hE k)
  refine ⟨T * M * A ^ 2 + ∑ k, E k, by positivity, ?_⟩
  intro G hG φ K ε τ s c hUeq hCeq hDeq hJeq hτ hs hτs hs1 hε hε1 hsmall hGQ hGb hφb hn
    δ hδ b d z hz hb hd hbd
  let η := τ / s + ε / τ ^ tensorLoss P
  have hη : 0 ≤ η := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hp (k : Fin 3) := he k G hG φ K ε τ s c hUeq hCeq hDeq hJeq
    hτ hs hτs hs1 hε hε1 hsmall hGQ (hGb.mono_order (Nat.add_le_add_left (ho k) m))
    (fun v => (hφb v).mono_order (Nat.add_le_add_left (ho k) m)) (hn.mono_order (hi k))
    δ hδ b d z hz
    ((supportedWeightedSeminorm_mono s (hi k) b).trans hb)
    ((supportedWeightedSeminorm_mono s (hi k) d).trans hd)
    ((supportedWeightedSeminorm_mono s (hi k) (b - d)).trans hbd)
  have hle (k : Fin 3) : E k ≤ ∑ j, E j :=
    Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)
  have hpv : WeightedBound Set.univ s m (η * ∑ k, E k) (c.polynomialMeanField δ q b) :=
    WeightedBound.pi isOpen_univ.uniqueDiffOn hs (mul_nonneg hη hsum)
      (contDiffOn_pi.mp (c.polynomialMeanField δ q b).contDiff.contDiffOn)
      (fun k => (hp k).1.mono_const (mul_le_mul_of_nonneg_left (hle k) hη))
  have hpd : WeightedBound Set.univ s m (η * (2 * ∑ k, E k) * z)
      ((c.polynomialMeanField δ q b) - (c.polynomialMeanField δ q d)) := by
    apply WeightedBound.pi isOpen_univ.uniqueDiffOn hs (by positivity)
      (contDiffOn_pi.mp ((c.polynomialMeanField δ q b).contDiff.sub
        (c.polynomialMeanField δ q d).contDiff).contDiffOn)
    intro k
    exact (hp k).2.mono_const (by gcongr; exact hle k)
  have hpvc := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (c.polynomialMeanField δ q b).contDiff hpv
  have hpdc := weightedBound_comp_isometry planeCoordinateIsometry.symm
    ((c.polynomialMeanField δ q b).contDiff.sub (c.polynomialMeanField δ q d).contDiff) hpd
  have hmv := c.metricMeanField_bound hδ hτ hs hτs hs1 hε hsmall q m hA hN (hn.mono_order hm)
    b ((supportedWeightedSeminorm_mono s hm b).trans hb)
  have hmd := c.metricMeanField_difference_bound hδ hτ hs hτs hs1 hε hsmall q m hA hN
    (mul_nonneg hA hz) (hn.mono_order hm) b d
    ((supportedWeightedSeminorm_mono s hm b).trans hb)
    ((supportedWeightedSeminorm_mono s hm d).trans hd)
    ((supportedWeightedSeminorm_mono s hm (b - d)).trans hbd)
  simp only [hCeq, hDeq, hJeq] at hmv hmd
  constructor
  · have hh := hmv.add isOpen_univ.uniqueDiffOn s.coe_nonneg
      (c.metricMeanField δ q b).contDiff.contDiffOn
      ((c.polynomialMeanField δ q b).contDiff.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hpvc
    convert hh using 1 <;> first | rfl | (dsimp only [T, M, η]; ring)
  · have hh := hmd.add isOpen_univ.uniqueDiffOn s.coe_nonneg
      ((c.metricMeanField δ q b).contDiff.sub (c.metricMeanField δ q d).contDiff).contDiffOn
      (((c.polynomialMeanField δ q b).contDiff.sub (c.polynomialMeanField δ q d).contDiff).comp
        planeCoordinateIsometry.symm.contDiff).contDiffOn hpdc
    apply (hh.congr (fun x _ => show
      c.combinedMeanField δ q b x - c.combinedMeanField δ q d x = _ by
        change (c.metricMeanField δ q b x + c.polynomialMeanField δ q b (planeCoordinateIsometry.symm x)) -
          (c.metricMeanField δ q d x + c.polynomialMeanField δ q d (planeCoordinateIsometry.symm x)) =
          (c.metricMeanField δ q b x - c.metricMeanField δ q d x) +
          (c.polynomialMeanField δ q b (planeCoordinateIsometry.symm x) -
            c.polynomialMeanField δ q d (planeCoordinateIsometry.symm x))
        abel)).mono_const
    apply le_of_eq
    dsimp only [T, M, η]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedUniformTrialMean
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual trial mean has majorants depending only on the fixed profile,
before choosing either oscillation scale or immersion. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_trial_mean {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℝ, 1 ≤ β ∧ 1 ≤ κ ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∀ (A B : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A c.e.source → ContDiffOn ℝ ∞ B c.e.source →
      InTrialBall c.e.source reference r A → InTrialBall c.e.source reference r B →
      WeightedBound c.e.source s (m + L) C A → WeightedBound c.e.source s (m + L) C B →
      WeightedBound c.e.source s (m + L) D (A - B) →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * β) (d.mean hρ δ q A) ∧
      WeightedBound Set.univ s m (κ * (τ / s + ε / τ ^ tensorLoss P) * D)
        (d.mean hρ δ q A - d.mean hρ δ q B) := by
  let j := m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
  let I := 2 ^ j * p.forms j * (j.factorial : ℝ) * p.inv j ^ j
  have hI : 0 ≤ I := by
    have := p.oneLEForms j
    have := p.oneLEInv j
    dsimp [I]
    positivity
  obtain ⟨A₀,hA₀,ha⟩ := uniform_charted_trial_amplitude (R := R) p.openV hρ j C
    (p.inv j) (p.forms j) (p.psi j) (p.oneLEInv j) (p.oneLEForms j) (p.oneLEPsi j)
  have hA0 : 0 ≤ A₀ := zero_le_one.trans hA₀
  obtain ⟨E,hE,he⟩ := uniform_charted_combined_mean p.openU p.openO p.compact p.subsetDomain
    P p.smoothP p.C p.D p.J p.nonnegC p.oneLEJ q m (p.B m) (p.F m) A₀ (p.normal j)
    (p.oneLEB m) (p.nonnegF m) hA0 (zero_le_one.trans (p.oneLENormal j))
  refine ⟨max 1 E,max 1 (2 * E * I),le_max_left _ _,le_max_left _ _,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ A B D hC hD hA hB
    hballA hballB hbA hbB hbD
  have hj : m + (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) = j := by dsimp [j]; omega
  rw [hj] at hbA hbB hbD
  have hi : d.budgets.inv j = p.inv j := congrFun hd.inverse j
  have hq : d.budgets.forms j = p.forms j := congrFun hd.forms j
  have hp : d.budgets.psi j = p.psi j := congrFun hd.cutoff j
  obtain ⟨hu,hv,hbd⟩ := ha c d.cutoff d.form d.localBounds d.budgets hd.target hi hq hp hs hs1
    A B D hC hD hA hB hballA hballB hbA hbB hbD
  have hmaps : Set.MapsTo (lowJet G) p.U p.Q := by
    simpa only [hd.domain, hd.range] using d.mapsJets
  have hgb : WeightedBound p.U s (m + tensorOrder P) (p.B m) (lowJet G) := by
    simpa only [hd.domain, hd.jets] using d.jetsBound m
  have hfb : ∀ v, WeightedBound p.U s (m + tensorOrder P) (p.F m)
      (fun x => fderiv ℝ φ x (coordinateVector v)) := by
    intro v
    simpa only [hd.domain, hd.phase] using d.phaseBound m v
  have hn : WeightedBound c.e.target s j (p.normal j) (freeNormal c.realMap) := by
    simpa only [hd.normal] using d.budgets.normal_bound j
  have hdiff : supportedWeightedSeminorm c.chartCompact s j
      (d.amplitude hρ A - d.amplitude hρ B) ≤ A₀ * (I * D) := by
    simpa only [ChartedMeanData.amplitude, I, mul_assoc] using hbd
  have hh := he G hG φ K ε τ s c hd.domain hd.coefficients hd.perturbation hd.coordinates
    hτ hs hτs hs1 hε hε1 hsmall hmaps hgb hfb hn δ hδ (d.amplitude hρ A) (d.amplitude hρ B)
    (I * D) (mul_nonneg hI hD) hu hv hdiff
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  constructor
  · exact hh.1.mono_const (mul_le_mul_of_nonneg_left (le_max_right _ _) hη)
  · apply hh.2.mono_const
    calc
      _ = (2 * E * I) * (τ / s + ε / τ ^ tensorLoss P) * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hη) hD

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedUniformMajorants
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-loss majorants for the actual mean operators. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_majorants {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r L
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (d.mean hρ δ q)) β κ := by
  have hex (m : ℕ) (C : ℝ) := uniform_charted_trial_mean (R := R) p hρ q m C
  choose β κ hβ hκ he using hex
  refine ⟨β,κ,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  have hη : 0 < τ / s + ε / τ ^ tensorLoss P :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  apply rescaledMean_bounds isOpen_univ.uniqueDiffOn hη _ β κ
    (fun m C _ => hβ m C) (fun m C _ => hκ m C)
  · intro A _ _
    exact (c.combinedMeanField δ q (d.amplitude hρ A)).contDiff.contDiffOn
  · intro m C A hC hA hball hb
    have hz : WeightedBound c.e.source s
        (m + (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))) 0 (A - A) := by
      apply (weightedBound_zero c.e.source s _ (F := Tensor)).congr
      intro x _
      exact sub_self (A x)
    exact (he m C d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ A A 0
      (zero_le_one.trans hC) le_rfl
      (hA.mono (Set.subset_univ _)) (hA.mono (Set.subset_univ _))
      (fun x _ => hball x (Set.mem_univ x)) (fun x _ => hball x (Set.mem_univ x))
      (hb.restrict_open c.e.open_source) (hb.restrict_open c.e.open_source) hz).1
  · intro m C D A B hC hD hA hB hballA hballB hbA hbB hbD
    exact (he m C d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ A B D
      (zero_le_one.trans hC) hD (hA.mono (Set.subset_univ _)) (hB.mono (Set.subset_univ _))
      (fun x _ => hballA x (Set.mem_univ x)) (fun x _ => hballB x (Set.mem_univ x))
      (hbA.restrict_open c.e.open_source) (hbB.restrict_open c.e.open_source)
      (hbD.restrict_open c.e.open_source)).2

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

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r3b3cae_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_sub (f g : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (f-g) = A.tensorPlaneRestore f - A.tensorPlaneRestore g := by
  funext p
  simp only [tensorPlaneRestore, Pi.sub_apply, map_sub, bundleRestore, smul_sub,
    Finset.sum_sub_distrib]

variable [CompactSpace M]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteMeanSums
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble finitely many actual mean operators with a common derivative
loss while retaining their scale-independent majorants. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma MeanBounds.mono_loss {U : Set E} {s : ℝ} {reference : E → F} {r : ℝ}
    {L L' : ℕ} {T : ℝ → (E → F) → E → F} {B K : ℕ → ℝ → ℝ}
    (hT : MeanBounds U s reference r L T B K) (hL : L ≤ L') :
    MeanBounds U s reference r L' T B K := by
  refine ⟨hT.B_pos, hT.K_pos, hT.smooth, ?_, ?_⟩
  · intro η hη hη1 m C f hC hf hb hbf
    exact hT.value η hη hη1 m C f hC hf hb (hbf.mono_order (Nat.add_le_add_left hL m))
  · intro η hη hη1 m C D f g hC hD hf hg hbf hbg hF hG hFG
    exact hT.difference η hη hη1 m C D f g hC hD hf hg hbf hbg
      (hF.mono_order (Nat.add_le_add_left hL m)) (hG.mono_order (Nat.add_le_add_left hL m))
      (hFG.mono_order (Nat.add_le_add_left hL m))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma rescaledMean_finset {ι : Type*} (a : Finset ι) (η : ℝ)
    (A : ι → (E → F) → E → F) :
    rescaledMean η (fun f x => ∑ i ∈ a, A i f x) =
      fun θ f x => ∑ i ∈ a, rescaledMean η (A i) θ f x := by
  funext θ f x
  simp only [rescaledMean, Pi.smul_apply, Finset.smul_sum]

lemma MeanBounds.finset_rescaled {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference : E → F} {r η : ℝ}
    (a : Finset ι) (A : ι → (E → F) → E → F) (L : ι → ℕ) (L' : ℕ)
    (B K : ι → ℕ → ℝ → ℝ)
    (hL : ∀ i ∈ a, L i ≤ L')
    (hA : ∀ i ∈ a, MeanBounds U s reference r (L i) (rescaledMean η (A i)) (B i) (K i)) :
    MeanBounds U s reference r L' (rescaledMean η (fun f x => ∑ i ∈ a, A i f x))
      (fun m C => 1 + ∑ i ∈ a, B i m C) (fun m C => 1 + ∑ i ∈ a, K i m C) := by
  rw [rescaledMean_finset]
  exact MeanBounds.finset_sum hU hs a (fun i => rescaledMean η (A i)) B K
    (fun i hi => (hA i hi).mono_loss (hL i hi))

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAdjustedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-coordinate quadratic mean after finite substitution.
The threshold in this statement still concerns fixed scale data. -/
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
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)

lemma chartedFamilyMean_smooth (hρ : 0 < ρ) (δ : ℝ) (q : ℕ)
    (A : SmallModes.Base → Tensor) : ContDiff ℝ ∞ (chartedFamilyMean d hρ δ q A) :=
  ContDiff.sum (fun i _ => ((c i).combinedMeanField δ q ((d i).amplitude hρ A)).contDiff)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedUniformFiniteMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform threshold for the actual finite family of transported means.
The profiles, target and their bounds precede the threshold; the map, both
scales, and the actual polynomial solvers follow it. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_family_majorants {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} (p : ι → ChartedMeanProfile P)
    {ρ R : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : ι → Base → ℝ} {K : ι → Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference), (∀ i, (p i).Fits (d i)) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r L
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (chartedFamilyMean d hρ δ q)) β κ := by
  classical
  choose β κ hm using fun i => uniform_charted_majorants (R := R) (p i) hρ q
  refine ⟨(fun m C => 1 + ∑ i, β i m C),(fun m C => 1 + ∑ i, κ i m C),?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  exact MeanBounds.finset_rescaled isOpen_univ.uniqueDiffOn s.coe_nonneg Finset.univ
    (fun i => (d i).mean hρ δ q) (fun _ => tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))
    (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) β κ (fun _ _ => le_rfl)
    (fun i _ => hm i (d i) (hd i) hτ hs hτs hs1 hε hε1 hsmall δ hδ)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanFamilyData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite charted phase family with its actual solvers and amplitudes,
packaged for assembling different coordinate patches on one surface. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanFamilyData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ} {s : ℝ≥0}
  {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma mean_smooth (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (d.mean hρ δ q f) := chartedFamilyMean_smooth d.data hρ δ q f

end ChartedMeanFamilyData

theorem uniform_chartedFamilyData_majorants {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : Fin 3 → ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    ∃ β κ : ℕ → ℝ → ℝ, ∀ {ε τ : ℝ} {s : ℝ≥0} {r : ℝ}
      {reference : SmallModes.Base → Tensor} (d : ChartedMeanFamilyData P ε τ s r ρ R reference),
      d.Fits p → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r
        (tensorOrder P + 1 + (q+1)*(tensorOrder P+1))
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (d.mean hρ δ q)) β κ := by
  obtain ⟨β,κ,h⟩ := uniform_charted_family_majorants (R := R) p hρ q
  refine ⟨β,κ,?_⟩
  intro ε τ s r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  exact h d.data hd hτ hs hτs hs1 hε hε1 hsmall δ hδ

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global nonlinear mean is the finite restoration of the actual
local means evaluated on unweighted chart readings. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberSpace
local instance atlasMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberNormed
local instance atlasMeanSectionNormed_r3b3cae_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMeanSectionSpace_r3b3cae_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma atlasMean_sub
    (μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor)
    (u v : ∀ x : M, CovariantTwoTensor x) :
    A.atlasMean μ u - A.atlasMean μ v = A.tensorPlaneRestore
      (fun i => μ i (A.tensorPlaneRead i u) - μ i (A.tensorPlaneRead i v)) :=
  (A.tensorPlaneRestore_sub _ _).symm

lemma tensorReadBallConstant_ball
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (f : Base → A.centers → TensorFiber) (r : ℝ) (hr : 0 ≤ r)
    (hf : ContDiff ℝ ∞ f) (hb : InTrialBall univ (A.tensorEncode reference) r f)
    (i : A.centers) :
    InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
      (A.tensorPlaneRead i (A.tensorDecode f)) :=
  (Classical.choose_spec A.tensorPlaneRead_decode_ball).2 reference href f r hr hf hb i

/-- Fixed atlas constants turn local value and difference estimates into
exactly the hypotheses used by finite global mean substitution. -/
theorem atlasMean_majorants_fixed_ball
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (L : ℕ) (B K : ℕ → ℝ → ℝ)
    (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C) (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C) :
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ η : ℝ, 0 < η →
      ∀ μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor,
      (∀ i f, ContDiff ℝ ∞ f → InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        ContDiff ℝ ∞ (μ i f)) →
      (∀ i m C f, 1 ≤ C → ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (η * B m C) (μ i f)) →
      (∀ i m C D f g, 1 ≤ C → 0 ≤ D → ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) g →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C g →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) D (f-g) →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (K m C * η * D) (μ i f - μ i g)) →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator (A.atlasMean μ))) β κ := by
  classical
  have hball := A.tensorReadBallConstant_ball
  intro r hr
  choose D hD hd using A.tensorPlaneRead_decode_bound
  choose E hE he using A.tensorPlaneRestore_bound
  let β : ℕ → ℝ → ℝ := fun m C => max 1 (E m * B m (D (m+L)*C))
  let κ : ℕ → ℝ → ℝ := fun m C => max 1 (E m * K m (D (m+L)*C) * D (m+L))
  refine ⟨(fun f hf hb i => hball reference href f r hr hf hb i),β,κ,?_⟩
  intro s hs hs1 η hη μ hsm hv hdiff
  have hb0 (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f)
      (hb : InTrialBall univ (A.tensorEncode reference) r f) (i : A.centers) :=
    hball reference href f r hr hf hb i
  have hf0 (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f) (i : A.centers) :=
    A.tensorPlaneRead_smooth i (A.tensorDecode_smooth hf)
  have hms (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f)
      (hb : InTrialBall univ (A.tensorEncode reference) r f) :
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (A.atlasMean μ (A.tensorDecode f) x)) :=
    A.tensorPlaneRestore_smooth (fun i => hsm i _ (hf0 f hf i) (hb0 f hf hb i))
  apply rescaledMean_bounds uniqueDiffOn_univ hη
  · exact fun m C _ => le_max_left _ _
  · exact fun m C _ => le_max_left _ _
  · intro f hf hb
    exact (A.tensorEncode_smooth (hms f (contDiffOn_univ.mp hf) hb)).contDiffOn
  · intro m C f hC hf hb hbf
    have hfs := contDiffOn_univ.mp hf
    have hDC : 1 ≤ D (m+L)*C := one_le_mul_of_one_le_of_one_le (hD _) hC
    have hl (i : A.centers) := hv i m (D (m+L)*C) _ hDC (hf0 f hfs i) (hb0 f hfs hb i)
      (hd (m+L) i f s C hs hs1 (zero_le_one.trans hC) hfs hbf)
    have hg := he m (fun i => μ i (A.tensorPlaneRead i (A.tensorDecode f))) s
      (η * B m (D (m+L)*C)) hs hs1 (mul_nonneg hη.le (zero_le_one.trans (hB _ _ hDC)))
      (fun i => hsm i _ (hf0 f hfs i) (hb0 f hfs hb i)) hl
    have henc := A.tensorEncode_bound (hms f hfs hb) hs
      (mul_nonneg (hE m) (mul_nonneg hη.le (zero_le_one.trans (hB _ _ hDC)))) hg
    apply henc.mono_const
    calc
      _ = η * (E m * B m (D (m+L)*C)) := by ring
      _ ≤ η * β m C := mul_le_mul_of_nonneg_left (le_max_right _ _) hη.le
  · intro m C D' f g hC hD' hf hg hbf hbg hbf' hbg' hfg
    have hfs := contDiffOn_univ.mp hf
    have hgs := contDiffOn_univ.mp hg
    have hDC : 1 ≤ D (m+L)*C := one_le_mul_of_one_le_of_one_le (hD _) hC
    have hl (i : A.centers) := hdiff i m (D (m+L)*C) (D (m+L)*D') _ _ hDC
      (mul_nonneg (zero_le_one.trans (hD _)) hD') (hf0 f hfs i) (hf0 g hgs i)
      (hb0 f hfs hbf i) (hb0 g hgs hbg i)
      (hd (m+L) i f s C hs hs1 (zero_le_one.trans hC) hfs hbf')
      (hd (m+L) i g s C hs hs1 (zero_le_one.trans hC) hgs hbg')
      (by rw [← A.tensorPlaneRead_decode_sub]; exact
        hd (m+L) i (f-g) s D' hs hs1 hD' (hfs.sub hgs) hfg)
    have hnon : 0 ≤ K m (D (m+L)*C) * η * (D (m+L)*D') :=
      mul_nonneg (mul_nonneg (zero_le_one.trans (hK _ _ hDC)) hη.le)
        (mul_nonneg (zero_le_one.trans (hD _)) hD')
    have hb := he m (fun i => μ i (A.tensorPlaneRead i (A.tensorDecode f)) -
      μ i (A.tensorPlaneRead i (A.tensorDecode g))) s _ hs hs1 hnon
      (fun i => (hsm i _ (hf0 f hfs i) (hb0 f hfs hbf i)).sub
        (hsm i _ (hf0 g hgs i) (hb0 g hgs hbg i))) hl
    rw [← A.atlasMean_sub μ] at hb
    have hsec := (hms f hfs hbf).sub_section (hms g hgs hbg)
    have henc := A.tensorEncode_bound hsec hs (mul_nonneg (hE m) hnon) hb
    rw [A.tensorEncode_sub] at henc
    apply henc.mono_const
    calc
      _ = (E m * K m (D (m+L)*C) * D (m+L)) * η * D' := by ring
      _ ≤ κ m C * η * D' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hη.le) hD'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform global majorants for the actual charted polynomial means.
Constants precede both scales, all coordinate maps and all local solvers. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberSpace
local instance uniformAtlasDualAdd_r3b3cae_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberNormed
local instance uniformAtlasSectionNormed_r3b3cae_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformAtlasSectionSpace_r3b3cae_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_atlas_mean_majorants_fixed_ball_oai
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x))) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      ∀ {ε τ : ℝ} {s : ℝ≥0}
        (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean (τ / s + ε / τ ^ loss)
          (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ := by
  classical
  dsimp only
  let Ls := fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1)
  let L := Finset.univ.sup Ls
  let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
  choose B K hlocal using fun i : A.centers => uniform_chartedFamilyData_majorants (R := R) (p i) hρ q
  let B' := fun m C => 1 + ∑ i : A.centers, max 1 (B i m C)
  let K' := fun m C => 1 + ∑ i : A.centers, max 1 (K i m C)
  have hB (m : ℕ) (C : ℝ) (_ : 1 ≤ C) : 1 ≤ B' m C := by
    have hn : 0 ≤ ∑ i : A.centers, max 1 (B i m C) :=
      Finset.sum_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
    change 1 ≤ 1 + ∑ i : A.centers, max 1 (B i m C)
    linarith
  have hK (m : ℕ) (C : ℝ) (_ : 1 ≤ C) : 1 ≤ K' m C := by
    have hn : 0 ≤ ∑ i : A.centers, max 1 (K i m C) :=
      Finset.sum_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
    change 1 ≤ 1 + ∑ i : A.centers, max 1 (K i m C)
    linarith
  have hBle (i : A.centers) (m : ℕ) (C : ℝ) : B i m C ≤ B' m C := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := fun j => max 1 (B j m C)) (fun _ _ => zero_le_one.trans (le_max_left _ _)) (Finset.mem_univ i)
    change B i m C ≤ 1 + ∑ j : A.centers, max 1 (B j m C)
    linarith [le_max_right 1 (B i m C)]
  have hKle (i : A.centers) (m : ℕ) (C : ℝ) : K i m C ≤ K' m C := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := fun j => max 1 (K j m C)) (fun _ _ => zero_le_one.trans (le_max_left _ _)) (Finset.mem_univ i)
    change K i m C ≤ 1 + ∑ j : A.centers, max 1 (K j m C)
    linarith [le_max_right 1 (K i m C)]
  have hall := A.atlasMean_majorants_fixed_ball reference href L B' K' hB hK
  intro r hr
  obtain ⟨hball,β,κ,hm⟩ := hall r hr
  refine ⟨hball,β,κ,?_⟩
  intro ε τ s d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  let η := τ / s + ε / τ ^ loss
  have hη : 0 < η := add_pos_of_pos_of_nonneg (div_pos hτ hs)
    (div_nonneg hε (pow_nonneg hτ.le _))
  have hηle (i : A.centers) : τ / s + ε / τ ^ tensorLoss (P i) ≤ η := by
    change τ / s + ε / τ ^ tensorLoss (P i) ≤ τ / s + ε / τ ^ loss
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    apply pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
    exact Finset.le_sup (f := fun i : A.centers => tensorLoss (P i)) (Finset.mem_univ i)
  have hηi (i : A.centers) : 0 < τ / s + ε / τ ^ tensorLoss (P i) :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  have hL (i : A.centers) : Ls i ≤ L := Finset.le_sup (Finset.mem_univ i)
  have hmi (i : A.centers) := hlocal i (d i) (hd i) hτ hs hτs hs1 hε hε1
    ((hηle i).trans hsmall) δ hδ
  apply hm hs hs1 η hη (fun i => (d i).mean hρ δ q)
  · intro i f _ _
    exact (d i).mean_smooth hρ δ q f
  · intro i m C f hC hf hb hbf
    have hh := (hmi i).value _ (hηi i) ((hηle i).trans hsmall) m C f hC hf.contDiffOn hb
      (hbf.mono_order (Nat.add_le_add_left (hL i) m))
    rw [rescaledMean_self (hηi i).ne'] at hh
    apply hh.mono_const
    calc
      _ ≤ η * B i m C := mul_le_mul_of_nonneg_right (hηle i)
        (zero_le_one.trans ((hmi i).B_pos m C hC))
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBle i m C) hη.le
  · intro i m C D f g hC hD hf hg hbf hbg hbf' hbg' hdiff
    have hh := (hmi i).difference _ (hηi i) ((hηle i).trans hsmall) m C D f g hC hD
      hf.contDiffOn hg.contDiffOn hbf hbg
      (hbf'.mono_order (Nat.add_le_add_left (hL i) m))
      (hbg'.mono_order (Nat.add_le_add_left (hL i) m))
      (hdiff.mono_order (Nat.add_le_add_left (hL i) m))
    rw [rescaledMean_self (hηi i).ne'] at hh
    apply hh.mono_const
    apply mul_le_mul_of_nonneg_right _ hD
    exact mul_le_mul (hKle i m C) (hηle i)
      (hηi i).le (zero_le_one.trans (hK m C hC))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball_oai.{u_1}
