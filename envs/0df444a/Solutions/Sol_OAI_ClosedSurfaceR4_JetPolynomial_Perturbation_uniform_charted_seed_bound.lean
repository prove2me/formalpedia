-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:57.907952+00:00
-- url     : https://prove2.me/submissions/76ba7cb5-d017-47d5-98ca-c926b38e0748

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedUniformSeed
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds for the original-coordinate free amplitudes,
as required by the quadratic target estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_seed_bound_oai {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ s m (B * (δ * τ)) (d.freeAmplitude hρ δ q A) := by
  let j := PolynomialSolveData.inputOrder (P := P) q m
  obtain ⟨A₀,hA₀,ha⟩ := uniform_charted_trial_amplitude (R := R) p.openV hρ j C
    (p.inv j) (p.forms j) (p.psi j) (p.oneLEInv j) (p.oneLEForms j) (p.oneLEPsi j)
  let B₀ := (m.factorial : ℝ) * p.J m ^ m *
    correctedSeedBudget (tensorOrder P) p.C p.D q m (p.normal j)
  refine ⟨max 1 (B₀ * A₀),le_max_left _ _,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  have hz : WeightedBound c.e.source s j 0 (A - A) := by
    apply (weightedBound_zero c.e.source s j (F := Tensor)).congr
    intro x _
    exact sub_self (A x)
  obtain ⟨hu,_,_⟩ := ha c d.cutoff d.form d.localBounds d.budgets hd.target
    (congrFun hd.inverse j) (congrFun hd.forms j) (congrFun hd.cutoff j) hs hs1
    A A 0 hC le_rfl hA.contDiffOn hA.contDiffOn
    (fun x _ => hball x (Set.mem_univ x)) (fun x _ => hball x (Set.mem_univ x))
    (hbA.restrict_open c.e.open_source) (hbA.restrict_open c.e.open_source) hz
  have hn : WeightedBound c.e.target s j (p.normal j) (freeNormal c.realMap) := by
    simpa only [hd.normal] using d.budgets.normal_bound j
  have hb := c.originalFreeSeed_bound hδ hτ hs hτs hs1 hε hsmall q m
    (zero_le_one.trans hA₀) (zero_le_one.trans (p.oneLENormal j)) hn (d.amplitude hρ A) hu
  have hb' : supportedWeightedSeminorm K s m (d.freeAmplitude hρ δ q A) ≤
      B₀ * A₀ * (δ * τ) := by
    simpa only [ChartedMeanData.freeAmplitude,hd.coefficients,hd.perturbation,hd.coordinates,B₀] using hb
  exact ((weightedBound_of_supportedSeminorm s m (d.freeAmplitude hρ δ q A)).mono_const hb').mono_const
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound_oai := @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound_oai
