-- Prove2me | solution 1 for OAI.SKValue.shiftedCoefficientSum_le_groundState
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:05:47.051893+00:00
-- url     : https://prove2.me/submissions/ff9aa22c-b56b-4c98-bbcb-49d76c2fcfff

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_sourceStripRegularity

section
-- module Solutions.OAIQ4_Sk.Compat
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_PredictableNormalizer
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SKValue

lemma independent_of_coordinate_not_in {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) {j : ι} (hj : j ∉ S) {F : (ι → ℝ) → β}
    (hF : Measurable F)
    (hdep : ∀ x y, (∀ i ∈ S, x i=y i) → F x=F y) :
    IndepFun F (fun x ↦ x j) (Measure.pi μ) := by
  let fill : (S → ℝ) → ι → ℝ := fun x i ↦ if hi : i ∈ S then x ⟨i,hi⟩ else 0
  have hfill : Measurable fill := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ S
    · simpa only [fill, dite_eq_left hi] using (measurable_pi_apply (⟨i,hi⟩ : S))
    · simp only [fill, dite_eq_right hi]
      exact measurable_const
  have hid : ∀ x : ι → ℝ, F (fill (fun i : S ↦ x i)) = F x := by
    intro x
    apply hdep
    intro i hi
    simp [fill,hi]
  have hST : Disjoint S {j} := by simpa using hj
  have hind : iIndepFun (fun i (x : ι → ℝ) ↦ x i) (Measure.pi μ) :=
    iIndepFun_pi (fun i ↦ (measurable_id : Measurable (id : ℝ → ℝ)).aemeasurable)
  have H := (hind.indepFun_finset S {j} hST (fun i ↦ measurable_pi_apply i)).comp
    (hF.comp hfill) (measurable_pi_apply (⟨j,by simp⟩ : ({j} : Finset ι)))
  simpa only [Function.comp_def, hid] using H

lemma measurable_coordinate (N j : ℕ) : Measurable (coordinate N j) :=
  measurable_pi_apply _

lemma coordinate_eq_apply {N j : ℕ} (hj : j < N+1) (z : Fin (N+1) → ℝ) :
    coordinate N j z = z ⟨j,hj⟩ := by
  simp [coordinate, Nat.mod_eq_of_lt hj]

lemma euler_depends_on_past (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) (z z' : Fin (N+1) → ℝ)
    (h : ∀ i < j, coordinate N i z=coordinate N i z') :
    euler T N γ u z j=euler T N γ u z' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := ih (fun i hi ↦ h i (by omega))
    simp only [euler, hp,h j (by omega)]

lemma measurable_euler (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hU : ∀ k < N, Measurable (u (meshTime T N k))) :
    ∀ j ≤ N, Measurable (fun z ↦ euler T N γ u z j) := by
  intro j hj
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hjN : j < N := by omega
    have hy := ih (by omega)
    have hz := measurable_coordinate N j
    have hu := (hU j hjN).comp hy
    simp only [euler]
    fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_mean {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_id_gaussianReal]

lemma gaussian_memLp {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  have H : MemLp (id : ℝ → ℝ) p (μ.map Z) := by
    rw [hZ.map_eq]
    exact memLp_id_gaussianReal' p hp
  simpa using (memLp_map_measure_iff H.aestronglyMeasurable hZ.aemeasurable).1 H

lemma gaussian_second_moment {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, (Z ω)^2 ∂μ = 1 := by
  have hvar := hZ.variance_eq
  rw [variance_eq_integral hZ.aemeasurable, gaussian_mean hZ] at hvar
  simpa using hvar

lemma normalizedIncrement_second_moment {H Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) (hHpos : 0 < ∫ ω, (H ω)^2 ∂μ) :
    ∫ ω, (normalizedIncrement H Z μ ω)^2 ∂μ = 1 := by
  have hind2 : IndepFun (fun ω ↦ (H ω)^2) (fun ω ↦ (Z ω)^2) μ :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind2.integral_mul_eq_mul_integral
    (hH.fun_pow 2)
    (hZ.aemeasurable.aestronglyMeasurable.fun_pow 2)
  change (∫ ω, (H ω)^2 * (Z ω)^2 ∂μ) =
    (∫ ω, (H ω)^2 ∂μ) * (∫ ω, (Z ω)^2 ∂μ) at hi
  simp only [normalizedIncrement, mul_pow, mul_assoc]
  rw [integral_const_mul, hi, gaussian_second_moment hZ, mul_one]
  simp only [predictableNormalizer, inv_pow, Real.sq_sqrt (le_of_lt hHpos)]
  exact inv_mul_cancel₀ (ne_of_gt hHpos)

lemma normalizedIncrement_memLp_two {H Z : Ω → ℝ}
    (hH : MemLp H 2 μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) :
    MemLp (normalizedIncrement H Z μ) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    ((hH.aestronglyMeasurable.const_mul _).mul hZ.aemeasurable.aestronglyMeasurable)).2
  have hi := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
     hH.integrable_sq (gaussian_memLp hZ 2 (by norm_num)).integrable_sq
  have hj := hi.const_mul (predictableNormalizer H μ ^ 2)
  simpa only [normalizedIncrement, Pi.mul_apply, mul_pow, mul_assoc, Function.comp_def, id_eq] using hj

lemma predictable_product_mean_zero {H K Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hK : AEStronglyMeasurable K μ)
    (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun (fun ω ↦ H ω * K ω) Z μ) :
    ∫ ω, K ω * normalizedIncrement H Z μ ω ∂μ = 0 := by
  have hi := hind.integral_mul_eq_mul_integral (hH.mul hK)
    hZ.aemeasurable.aestronglyMeasurable
  change (∫ ω, (H ω * K ω) * Z ω ∂μ) = _ at hi
  calc
    _ = predictableNormalizer H μ * ∫ ω, (H ω * K ω) * Z ω ∂μ := by
      rw [← integral_const_mul]
      congr 1
      ext ω
      simp only [normalizedIncrement]
      ring
    _ = 0 := by rw [hi, gaussian_mean hZ, mul_zero, mul_zero]

lemma coordinate_hasLaw (N j : ℕ) :
    HasLaw (coordinate N j) (gaussianReal 0 1) (gaussianProduct (Fin (N+1))) :=
  (measurePreserving_eval (fun _ : Fin (N+1) ↦ standardGaussian)
    ⟨j % (N+1), Nat.mod_lt _ (Nat.succ_pos _)⟩).hasLaw

lemma DependsBefore.independent {N j : ℕ} {β : Type*} [MeasurableSpace β] (hj : j<N+1)
    {F : (Fin (N+1) → ℝ) → β} (hF : DependsBefore j F) (hm : Measurable F) :
    IndepFun F (coordinate N j) (gaussianProduct (Fin (N+1))) := by
  have H := independent_of_coordinate_not_in (μ := fun _ : Fin (N+1) ↦ standardGaussian)
    (Finset.univ.filter (fun i : Fin (N+1) ↦ (i : ℕ)<j))
    (j := ⟨j,hj⟩) (by simp) hm (fun z z' heq ↦ hF z z' (by simpa using heq))
  have heq : coordinate N j = fun z : Fin (N+1) → ℝ ↦ z ⟨j,hj⟩ :=
    funext (coordinate_eq_apply hj)
  rw [heq]
  exact H

lemma DependsBefore.mono {N i j : ℕ} {β : Type*} {F : (Fin (N+1) → ℝ) → β}
    (hF : DependsBefore i F) (hij : i≤j) : DependsBefore j F :=
  fun z z' h ↦ hF z z' (fun k hk ↦ h k (hk.trans_le hij))

lemma DependsBefore.mul {N j : ℕ} {F G : (Fin (N+1) → ℝ) → ℝ}
    (hF : DependsBefore j F) (hG : DependsBefore j G) :
    DependsBefore j (fun z ↦ F z * G z) := by
  intro z z' h
  dsimp only
  rw [hF z z' h, hG z z' h]

lemma eulerCoefficient_dependsBefore (T : ℝ) {N j : ℕ} (hj : j≤N)
    (γ : ℝ → ℝ) (u a : ℝ → ℝ → ℝ) :
    DependsBefore j (fun z ↦ a (meshTime T N j) (euler T N γ u z j)) := by
  intro z z' h
  apply congrArg (a (meshTime T N j))
  apply euler_depends_on_past
  intro i hi
  have hiN : i<N+1 := by omega
  rw [coordinate_eq_apply hiN, coordinate_eq_apply hiN]
  exact h ⟨i,hiN⟩ hi

lemma normalizedIncrement_dependsBefore {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hH : DependsBefore j H) :
    DependsBefore (j+1) (normalizedIncrement H (coordinate N j) (gaussianProduct (Fin (N+1)))) := by
  intro z z' h
  have heq := hH.mono (Nat.le_succ j) z z' h
  have hz : coordinate N j z=coordinate N j z' := by
    rw [coordinate_eq_apply hj, coordinate_eq_apply hj]
    exact h ⟨j,hj⟩ (Nat.lt_succ_self j)
  simp only [normalizedIncrement,heq,hz]

lemma measurable_normalizedIncrement {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hH : Measurable H) :
    Measurable (normalizedIncrement H (coordinate N j) (gaussianProduct (Fin (N+1)))) :=
  (hH.const_mul _).mul (measurable_coordinate N j)

lemma normalizedIncrements_orthogonal {N i j : ℕ} (hij : i<j) (hj : j<N+1)
    {H K : (Fin (N+1) → ℝ) → ℝ} (hHm : Measurable H) (hKm : Measurable K)
    (hH : DependsBefore i H) (hK : DependsBefore j K) :
    ∫ z, normalizedIncrement H (coordinate N i) (gaussianProduct (Fin (N+1))) z *
      normalizedIncrement K (coordinate N j) (gaussianProduct (Fin (N+1))) z
      ∂gaussianProduct (Fin (N+1)) = 0 := by
  have hi : i<N+1 := hij.trans hj
  have hprev := (normalizedIncrement_dependsBefore hi hH).mono (by omega : i+1≤j)
  exact predictable_product_mean_zero hKm.aestronglyMeasurable
    (measurable_normalizedIncrement hHm).aestronglyMeasurable (coordinate_hasLaw N j)
    ((hK.mul hprev).independent hj
      (hKm.mul (measurable_normalizedIncrement hHm)))

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientStrip
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_mem_strip_ito {δ T : ℝ} {N j : ℕ} (hδ : 0≤δ)
    (horizon : (N : ℝ)*δ=T) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
  constructor
  · positivity
  · rw [← horizon]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientErrorConstant
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SKValue

lemma continuous_cdf_of_nullSingleton (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hz := (cdf μ).measure_singleton x
  rw [measure_cdf μ, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hz
  have hleft : Function.leftLim (cdf μ) x = cdf μ x := by
    have hl := (monotone_cdf μ).leftLim_le (le_refl x)
    linarith
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, (cdf μ).right_continuous x⟩
  rw [← continuousWithinAt_Iio_iff_Iic]
  exact (monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq.mpr hleft

lemma strictMono_gaussian_cdf {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal m v)) := by
  intro x y hxy
  apply lt_of_le_of_ne ((monotone_cdf _) hxy.le)
  intro heq
  have hz : gaussianReal m v (Ioc x y) = 0 := by
    rw [← measure_cdf (gaussianReal m v), StieltjesFunction.measure_Ioc, heq, sub_self,
      ENNReal.ofReal_zero]
  have hz' := gaussianReal_absolutelyContinuous' m hv hz
  have hyx : y ≤ x := by simpa [Real.volume_Ioc, ENNReal.ofReal_eq_zero, sub_nonpos] using hz'
  exact (not_le_of_gt hxy) hyx

lemma cdf_mem_Ioo_of_strictMono (μ : Measure ℝ) (hmono : StrictMono (cdf μ)) (x : ℝ) :
    cdf μ x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact lt_of_le_of_lt (cdf_nonneg μ (x-1)) (hmono (by linarith))
  · exact lt_of_lt_of_le (hmono (show x < x+1 by linarith)) (cdf_le_one μ (x+1))

lemma exists_cdf_eq (μ : Measure ℝ) (hc : Continuous (cdf μ))
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ∃ x, cdf μ x = r := by
  obtain ⟨a,ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const hr.1).exists
  obtain ⟨b,hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt hr.2).exists
  exact intermediate_value_univ a b hc ⟨ha.le, hb.le⟩

lemma cdf_hasLaw_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) (hmono : StrictMono (cdf μ)) :
    HasLaw (cdf μ) (volume.restrict (Ioc (0 : ℝ) 1)) μ := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply hc.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  rcases le_or_gt r 0 with hr | hr
  · have hp : (cdf μ) ⁻¹' Iic r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_le_of_gt (lt_of_le_of_lt hr (cdf_mem_Ioo_of_strictMono μ hmono x).1)) hx
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact not_lt_of_ge (hx.1.trans hr) hx.2.1
    simp [hp,hi]
  rcases le_or_gt 1 r with hr1 | hr1
  · have hp : (cdf μ) ⁻¹' Iic r = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (cdf_le_one μ x).trans hr1
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 :=
      inter_eq_right.mpr (fun x hx ↦ hx.2.trans hr1)
    simp [hp,hi]
  · obtain ⟨x,hx⟩ := exists_cdf_eq μ hc ⟨hr,hr1⟩
    have hp : (cdf μ) ⁻¹' Iic r = Iic x := by
      ext y
      simp only [mem_preimage, mem_Iic, ← hx, hmono.le_iff_le]
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 r := by
      ext y
      constructor
      · exact fun hy ↦ ⟨hy.2.1,hy.1⟩
      · exact fun hy ↦ ⟨hy.2,hy.1,hy.2.trans hr1.le⟩
    rw [hp,hi, ← ofReal_cdf μ, hx, Real.volume_Ioc, sub_zero]

lemma standardGaussian_cdf_hasLaw_uniform :
    HasLaw (cdf (gaussianReal 0 1)) (volume.restrict (Ioc (0 : ℝ) 1)) (gaussianReal 0 1) := by
  let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  exact cdf_hasLaw_uniform _ (continuous_cdf_of_nullSingleton _) (strictMono_gaussian_cdf (by norm_num))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshRaw
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_time_mem {T : ℝ} (hT : 0≤T) {N j : ℕ} (hN : 0<N) (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  apply mesh_mem_strip_ito (δ := stepSize T N) (div_nonneg hT (Nat.cast_nonneg N)) _ hj
  have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold stepSize
  field_simp

lemma mesh_terminal_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    Measurable (meshTerminal T N γ u) :=
  (h.smooth T ⟨hT,le_rfl⟩).continuous.measurable.comp
    (measurable_euler T N γ u (fun _ hj ↦
      (h.smooth _ (mesh_time_mem hT hN hj.le)).continuous.measurable) N le_rfl)

lemma mesh_raw_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    Measurable (meshRaw T N γ u j) :=
  ((h.smooth _ (mesh_time_mem hT hN hj)).continuous_deriv (by norm_num)).measurable.comp
    (measurable_euler T N γ u (fun k hk ↦
      (h.smooth _ (mesh_time_mem hT hN hk.le)).continuous.measurable) j hj)

lemma mesh_raw_depends (T : ℝ) {N j : ℕ} (hj : j≤N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    DependsBefore j (meshRaw T N γ u j) :=
  eulerCoefficient_dependsBefore T hj γ u (fun t ↦ deriv (u t))

lemma mesh_terminal_depends (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    DependsBefore N (meshTerminal T N γ u) :=
  eulerCoefficient_dependsBefore T le_rfl γ u (fun _ ↦ u T)

lemma mesh_raw_memLp {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (meshRaw T N γ u j) 2 (gaussianProduct (Fin (N+1))) := by
  have := gaussianProduct_probability (Fin (N+1))
  apply MemLp.of_bound (mesh_raw_measurable hT h hN hj).aestronglyMeasurable D
  exact Eventually.of_forall (fun z ↦ by
    simpa only [meshRaw, Real.norm_eq_abs] using hD _ (mesh_time_mem hT hN hj) (euler T N γ u z j))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_LiteralNormalizer
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma literal_coefficientA_succ (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    coefficientA W γ T N (j+1)=meshA T N γ.coeff (gradient W γ) j := by
  simp only [coefficientA, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
  rfl

lemma literal_coefficientB_succ (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    coefficientB W γ T N (j+1)=meshB T N γ.coeff (gradient W γ) j := by
  simp only [coefficientB, Nat.add_sub_cancel]
  rfl

lemma literal_shiftedCoefficientSum (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N : ℕ) :
    shiftedCoefficientSum W γ T N=finiteShiftedValue T N γ.coeff (gradient W γ) := by
  unfold shiftedCoefficientSum
  rw [←Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, coefficientA, ↓reduceIte, zero_mul, zero_add]
  unfold finiteShiftedValue
  apply Finset.sum_congr rfl
  intro i hi
  change coefficientA W γ T N ((i : ℕ)+1)*coefficientB W γ T N (((i : ℕ)+1)+1)=_
  rw [literal_coefficientA_succ, literal_coefficientB_succ]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_StandardGaussian
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -y^2/2) (-x) x := by
    have hh := ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)
    simpa only [Pi.pow_def,Pi.neg_def,id_eq,pow_one,show (2 : ℕ)-1=1 from rfl,
      Nat.cast_ofNat,mul_one,neg_div,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hd := h1.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  convert hd using 1 <;> try rfl
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    ring

lemma density_mul_integrable {f : ℝ → ℝ} (hf : Integrable f standardGaussian) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x*f x) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Eventually.of_forall (fun x ↦ gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma standardGaussian_integrable_id : Integrable (fun x : ℝ ↦ x) standardGaussian := by
  have hh := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (1 : ℝ≥0∞) (by norm_num))
  exact hh.integrable (by norm_num)

lemma gaussian_stein_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hm : AEStronglyMeasurable f' standardGaussian)
    (hC : ∀ x, |f x|≤C) (hD : ∀ x, |f' x|≤D) :
    (∫ x, x*f x ∂standardGaussian) = ∫ x, f' x ∂standardGaussian := by
  have hfm : Continuous f := continuous_iff_continuousAt.mpr (fun x ↦ (hf x).continuousAt)
  have hfi : Integrable f standardGaussian := Integrable.of_bound hfm.aestronglyMeasurable C
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hf'i : Integrable f' standardGaussian := Integrable.of_bound hm D
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hD x)))
  have hxfi : Integrable (fun x ↦ x*f x) standardGaussian :=
    standardGaussian_integrable_id.mul_bdd hfm.aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hi1 : Integrable (fun x ↦ f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert (density_mul_integrable hxfi).neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x ↦ f' x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hf'i
  have hi3 : Integrable (fun x ↦ f x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hfi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := f') (v' := fun x ↦ -x*gaussianPDFReal 0 1 x)
    (fun x _ ↦ hf x) (fun x _ ↦ density_hasDerivAt x) hi1 hi2 hi3
  have hb : (∫ x, f x*(-x*gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x*(x*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by ring)
  rw [hb] at hibp
  have he : (∫ x, gaussianPDFReal 0 1 x*(x*f x)) =
      ∫ x, gaussianPDFReal 0 1 x*f' x := by
    exact neg_injective hibp |>.trans (by congr 1; funext x; ring)
  simpa only [standardGaussian,integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul] using he

lemma gaussian_coordinate_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun z : ι → ℝ ↦ z i) (gaussianProduct ι) := by
  exact ((measurePreserving_eval (fun _ : ι ↦ standardGaussian) i).integrable_comp
    standardGaussian_integrable_id.aestronglyMeasurable).mpr standardGaussian_integrable_id

lemma gaussian_pi_stein_bounded {n : ℕ} (i : Fin n) {f f' : (Fin n → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ z, HasDerivAt (fun x ↦ f (Function.update z i x)) (f' z) (z i))
    (hC : ∀ z, |f z| ≤ C) (hD : ∀ z, |f' z| ≤ D) :
    (∫ z, z i*f z ∂gaussianProduct (Fin n)) = ∫ z, f' z ∂gaussianProduct (Fin n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) i
    have he : MeasurePreserving e.symm (standardGaussian.prod (gaussianProduct (Fin n)))
        (gaussianProduct (Fin (n+1))) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ standardGaussian) i).symm
    have hi : Integrable (fun z : Fin (n+1) → ℝ ↦ z i*f z) (gaussianProduct (Fin (n+1))) :=
      (gaussian_coordinate_integrable i).mul_bdd hf.aestronglyMeasurable
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hC z)))
    have hi' : Integrable f' (gaussianProduct (Fin (n+1))) :=
      Integrable.of_bound hf'.aestronglyMeasurable D
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hD z)))
    have hip : Integrable (fun p ↦ e.symm p i * f (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi.aestronglyMeasurable).mpr hi
    have hi'p : Integrable (fun p ↦ f' (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi'.aestronglyMeasurable).mpr hi'
    rw [← he.integral_comp' (fun z ↦ z i*f z), ← he.integral_comp' f',
      integral_prod _ hip, integral_prod _ hi'p,
      integral_integral_swap (f := fun x y ↦ e.symm (x,y) i * f (e.symm (x,y))) hip,
      integral_integral_swap (f := fun x y ↦ f' (e.symm (x,y))) hi'p]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same]
    change (∫ x, x*f (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian) =
      ∫ x, f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian
    have hmeas : Measurable (fun x : ℝ ↦ i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) := by
      exact e.symm.measurable.comp (measurable_id.prodMk measurable_const)
    apply gaussian_stein_bounded (f' := fun x ↦ f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y))
    · intro x
      simpa only [Fin.update_insertNth,Fin.insertNth_apply_same] using hd (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y)
    · exact (hf'.measurable.comp hmeas).aestronglyMeasurable
    · exact fun x ↦ hC _
    · exact fun x ↦ hD _

lemma partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) : 0 < partition x := by
  exact Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty

lemma gibbsWeight_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    0 ≤ gibbsWeight x i := le_of_lt (div_pos (Real.exp_pos _) (partition_pos x))

lemma sum_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∑ i, gibbsWeight x i = 1 := by
  simp only [gibbsWeight,← Finset.sum_div]
  change partition x / partition x = 1
  exact div_self (ne_of_gt (partition_pos x))

lemma gibbsWeight_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    gibbsWeight x i ≤ 1 := by
  calc
    _ ≤ ∑ j, gibbsWeight x j := Finset.single_le_sum (fun j _ ↦ gibbsWeight_nonneg x j) (Finset.mem_univ i)
    _ = 1 := sum_gibbsWeight x

lemma continuous_partition {ι : Type*} [Fintype ι] : Continuous (@partition ι _) := by
  unfold partition
  fun_prop

lemma continuous_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (i : ι) :
    Continuous (fun x : ι → ℝ ↦ gibbsWeight x i) := by
  exact (Real.continuous_exp.comp (continuous_apply i)).div continuous_partition (fun x ↦ ne_of_gt (partition_pos x))

lemma hasDerivAt_partition {ι : Type*} [Fintype ι] {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ partition (x s)) (∑ i, Real.exp (x t i)*v i) t := by
  simpa only [partition,Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (h i).exp))

lemma hasDerivAt_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ logPartition (x s)) (∑ i, gibbsWeight (x t) i*v i) t := by
  convert (hasDerivAt_partition h).log (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight,Finset.sum_div,mul_div_assoc]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hasDerivAt_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) (i : ι) :
    HasDerivAt (fun s ↦ gibbsWeight (x s) i)
      (gibbsWeight (x t) i*(v i-∑ j, gibbsWeight (x t) j*v j)) t := by
  convert (h i).exp.div (hasDerivAt_partition h) (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight]
  rw [show (∑ j, Real.exp (x t j)/partition (x t)*v j) =
      (∑ j, Real.exp (x t j)*v j)/partition (x t) by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring]
  field_simp [ne_of_gt (partition_pos (x t))]

lemma abs_gibbsMean_le {ι : Type*} [Fintype ι] [Nonempty ι] (x v : ι → ℝ) {C : ℝ}
    (hC : ∀ i, |v i| ≤ C) : |∑ i, gibbsWeight x i*v i| ≤ C := by
  calc
    _ ≤ ∑ i, |gibbsWeight x i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, gibbsWeight x i*|v i| := by simp only [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
    _ ≤ ∑ i, gibbsWeight x i*C := Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hC i) (gibbsWeight_nonneg _ _))
    _ = C := by rw [← Finset.sum_mul,sum_gibbsWeight,one_mul]

lemma continuous_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) :
    Continuous (linearProcess c) := by
  unfold linearProcess
  fun_prop

lemma hasDerivAt_linearProcess_update {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ι → κ → ℝ) (z : κ → ℝ) (i : ι) (k : κ) :
    HasDerivAt (fun x ↦ linearProcess c (Function.update z k x) i) (c i k) (z k) := by
  have h : ∀ j, HasDerivAt (fun x ↦ c i j * Function.update z k x j)
      (if j=k then c i k else 0) (z k) := by
    intro j
    by_cases hj : j=k
    · subst j
      simpa only [Function.update_self,ite_true,mul_one,id_eq] using (hasDerivAt_id (z k)).const_mul (c i k)
    · simpa only [Function.update_of_ne hj,ite_eq_right hj] using hasDerivAt_const (z k) (c i j*z j)
  simpa only [linearProcess,Finset.sum_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h j)

lemma continuous_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Continuous (fun z ↦ gibbsWeight (linearProcess c z) i) :=
  (continuous_gibbsWeight i).comp (continuous_linearProcess c)

lemma integrable_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Integrable (fun z ↦ gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply Integrable.of_bound (continuous_linear_gibbsWeight c i).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma coordinate_gibbsWeight_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) (k : κ) :
    Integrable (fun z ↦ z k*gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply (gaussian_coordinate_integrable k).mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma gaussian_coordinate_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n) := by
  apply gaussian_pi_stein_bounded k (C := 1) (D := 2*∑ j, |c j k|)
  · exact continuous_linear_gibbsWeight c i
  · apply Continuous.mul (continuous_linear_gibbsWeight c i)
    apply continuous_const.sub
    exact continuous_finsetSum _ (fun j _ ↦ (continuous_linear_gibbsWeight c j).mul continuous_const)
  · intro z
    simpa only [Function.update_eq_self] using
      hasDerivAt_gibbsWeight (fun j ↦ hasDerivAt_linearProcess_update c z j k) i
  · intro z
    rw [abs_of_nonneg (gibbsWeight_nonneg _ _)]
    exact gibbsWeight_le_one _ _
  · intro z
    have hsum : ∀ j, |c j k| ≤ ∑ l, |c l k| := fun j ↦
      Finset.single_le_sum (f := fun l ↦ |c l k|) (fun l _ ↦ abs_nonneg _) (Finset.mem_univ j)
    calc
      _ = gibbsWeight (linearProcess c z) i * |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| := by
        rw [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
      _ ≤ |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| :=
        mul_le_of_le_one_left (abs_nonneg _) (gibbsWeight_le_one _ _)
      _ ≤ |c i k| + |∑ j, gibbsWeight (linearProcess c z) j*c j k| := abs_sub _ _
      _ ≤ (∑ j, |c j k|) + (∑ j, |c j k|) := add_le_add (hsum i) (abs_gibbsMean_le _ _ hsum)
      _ = _ := by ring

lemma le_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    x i ≤ logPartition x := by
  apply (Real.le_log_iff_exp_le (partition_pos x)).mpr
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)

lemma logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) {C : ℝ}
    (h : ∀ i, x i ≤ C) : logPartition x ≤ Real.log (Fintype.card ι) + C := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    logPartition x ≤ Real.log ((Fintype.card ι : ℝ)*Real.exp C) := by
      apply Real.log_le_log (partition_pos x)
      calc
        partition x ≤ ∑ _ : ι, Real.exp C := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_exp.mpr (h i))
        _ = _ := by simp
    _ = _ := by rw [Real.log_mul (ne_of_gt hc) (Real.exp_ne_zero _),Real.log_exp]

lemma abs_logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |logPartition x| ≤ |Real.log (Fintype.card ι)| + ∑ i, |x i| := by
  have hsum : ∀ i, |x i| ≤ ∑ j, |x j| := fun i ↦
    Finset.single_le_sum (f := fun j ↦ |x j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  have hu := logPartition_le x (fun i ↦ (le_abs_self _).trans (hsum i))
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hl := le_logPartition x i
  have hx := neg_abs_le (x i)
  have hxi := hsum i
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (Fintype.card ι)),abs_nonneg (Real.log (Fintype.card ι))]

lemma continuous_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@logPartition ι _) :=
  continuous_partition.log (fun x ↦ ne_of_gt (partition_pos x))

lemma linearProcess_integrable {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    Integrable (fun z ↦ linearProcess c z i) (gaussianProduct κ) :=
  integrable_finsetSum _ (fun k _ ↦ (gaussian_coordinate_integrable k).const_mul (c i k))

lemma logPartition_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ logPartition (linearProcess c z)) (gaussianProduct κ) := by
  have hb := (integrable_const (|Real.log (Fintype.card ι)| : ℝ)).add
    (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs))
  apply hb.mono' ((continuous_logPartition.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,Pi.add_apply] using abs_logPartition_le (linearProcess c z))

lemma gibbsWeight_mul_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) {f : (κ → ℝ) → ℝ} (hi : Integrable f (gaussianProduct κ)) :
    Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*f z) (gaussianProduct κ) := by
  simpa only [mul_comm] using hi.mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _))

lemma gaussian_linear_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ) (i : ι) :
    (∫ z, gibbsWeight (linearProcess c z) i * linearProcess d z i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k) - ∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
        ∂gaussianProduct (Fin n) := by
  have hid : ∀ k, Integrable (fun z ↦ d i k * (z k*gibbsWeight (linearProcess c z) i))
      (gaussianProduct (Fin n)) := fun k ↦ (coordinate_gibbsWeight_integrable c i k).const_mul _
  have hic : ∀ k, Integrable (fun z ↦ d i k * (gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k))) (gaussianProduct (Fin n)) := by
    intro k
    apply Integrable.const_mul
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum Finset.univ
      (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  calc
    _ = ∫ z, ∑ k, d i k*(z k*gibbsWeight (linearProcess c z) i) ∂gaussianProduct (Fin n) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z ↦ by simp only [linearProcess,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring)
    _ = ∑ k, d i k * (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hid k)]
      simp only [integral_const_mul]
    _ = ∑ k, d i k * (∫ z, gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n)) := by
      simp only [gaussian_coordinate_gibbsWeight]
    _ = ∫ z, ∑ k, d i k * (gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k)) ∂gaussianProduct (Fin n) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hic k)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl; intro k _; ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _; ring

lemma weighted_covariance_pairs {ι : Type*} [Fintype ι] (p : ι → ℝ) (D : ι → ι → ℝ)
    (hp : ∑ i, p i = 1) :
    ∑ i, p i*(D i i-∑ j, p j*D i j) =
    (1/2 : ℝ)*∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i) := by
  have h1 : (∑ i, ∑ j, p i*p j*D i i) = ∑ i, p i*D i i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = p i*D i i*∑ j, p j := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by rw [hp,mul_one]
  have h2 : (∑ i, ∑ j, p i*p j*D j j) = ∑ j, p j*D j j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (∑ i, p i)*(p j*D j j) := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by rw [hp,one_mul]
  have h3 : (∑ i, ∑ j, p i*p j*D j i) = ∑ i, ∑ j, p i*p j*D i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hl : (∑ i, p i*(D i i-∑ j, p j*D i j)) =
      (∑ i, p i*D i i) - ∑ i, ∑ j, p i*p j*D i j := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  have hr : (∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i)) =
      2*(∑ i, p i*D i i)-2*(∑ i, ∑ j, p i*p j*D i j) := by
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [h1,h2,h3]
    ring
  rw [hl,hr]
  ring

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RotatedCoefficients
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma gaussian_gibbs_derivative_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ)
    (h : ∀ i j, 0 ≤ ∑ k, (d i k-d j k)*(c i k-c j k)) :
    0 ≤ ∫ z, ∑ i, gibbsWeight (linearProcess c z) i*linearProcess d z i ∂gaussianProduct (Fin n) := by
  have hi : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*linearProcess d z i)
      (gaussianProduct (Fin n)) := fun i ↦ gibbsWeight_mul_integrable c i (linearProcess_integrable d i)
  have hi' : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k)))
      (gaussianProduct (Fin n)) := by
    intro i
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum _ (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [gaussian_linear_gibbsWeight]
  rw [← integral_finsetSum _ (fun i _ ↦ hi' i)]
  apply integral_nonneg
  intro z
  change (0 : ℝ) ≤ ∑ i, gibbsWeight (linearProcess c z) i *
    ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
  rw [weighted_covariance_pairs _ (fun i j ↦ ∑ k, d i k*c j k) (sum_gibbsWeight (linearProcess c z))]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (gibbsWeight_nonneg _ _) (gibbsWeight_nonneg _ _))
  have he : (∑ k, d i k*c i k)+(∑ k, d j k*c j k)-
      (∑ k, d i k*c j k)-(∑ k, d j k*c i k) = ∑ k, (d i k-d j k)*(c i k-c j k) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact h i j

lemma hasDerivAt_rotatedProcess {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ)
    (t : ℝ) (z : κ → ℝ) (i : ι) :
    HasDerivAt (fun s ↦ linearProcess (rotatedCoefficients a b s) z i)
      (linearProcess (rotationVelocity a b t) z i) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (((Real.hasDerivAt_cos t).mul_const (a i k)).add ((Real.hasDerivAt_sin t).mul_const (b i k))).mul_const (z k))

lemma abs_rotationVelocity_le {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) :
    |rotationVelocity a b t i k| ≤ |a i k|+|b i k| := by
  calc
    _ ≤ |-Real.sin t*a i k| + |Real.cos t*b i k| := abs_add_le _ _
    _ = |Real.sin t| *|a i k| + |Real.cos t| *|b i k| := by rw [abs_mul,abs_neg,abs_mul]
    _ ≤ 1*|a i k| + 1*|b i k| := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg _))
    _ = _ := by ring

lemma rotation_derivative_bound {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a b : ι → κ → ℝ) (t : ℝ) (z : κ → ℝ) :
    |∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i| ≤
      ∑ i, ∑ k, (|a i k|+|b i k|)*|z k| := by
  apply abs_gibbsMean_le
  intro i
  calc
    _ ≤ ∑ k, |rotationVelocity a b t i k*z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (|a i k|+|b i k|)*|z k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_rotationVelocity_le _ _ _ _ _) (abs_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun j ↦ ∑ k, (|a j k|+|b j k|)*|z k|) (fun j _ ↦ Finset.sum_nonneg (fun k _ ↦ mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))) (Finset.mem_univ i)

lemma hasDerivAt_expected_rotated_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b s) z) ∂gaussianProduct (Fin n))
      (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t := by
  have hb : Integrable (fun z : Fin n → ℝ ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
      (gaussianProduct (Fin n)) :=
    integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun k _ ↦
      (gaussian_coordinate_integrable k).abs.const_mul _))
  have hmc : Continuous (fun z : Fin n → ℝ ↦ ∑ i,
      gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i) := by
    apply continuous_finsetSum
    intro i _
    apply (continuous_linear_gibbsWeight _ _).mul
    exact (continuous_apply i).comp (continuous_linearProcess _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) (μ := gaussianProduct (Fin n))
    (F := fun s z ↦ logPartition (linearProcess (rotatedCoefficients a b s) z))
    (F' := fun s z ↦ ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b s) z) i *
      linearProcess (rotationVelocity a b s) z i)
    (bound := fun z ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
    (Filter.univ_mem)
    (Eventually.of_forall (fun s ↦ (continuous_logPartition.comp (continuous_linearProcess _)).aestronglyMeasurable))
    (logPartition_integrable _) hmc.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ ↦ by simpa only [Real.norm_eq_abs] using rotation_derivative_bound a b s z)) hb
    (Eventually.of_forall (fun z s _ ↦ hasDerivAt_logPartition (hasDerivAt_rotatedProcess a b s z)))).2

lemma rotation_pair_covariance {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ) (t : ℝ) (i j : ι) :
    (∑ k, (rotationVelocity a b t i k-rotationVelocity a b t j k)*
      (rotatedCoefficients a b t i k-rotatedCoefficients a b t j k)) =
    Real.sin t*Real.cos t*((∑ k, (b i k-b j k)^2)-(∑ k, (a i k-a j k)^2)) +
      ((Real.cos t)^2-(Real.sin t)^2)*∑ k, (a i k-a j k)*(b i k-b j k) := by
  simp only [rotationVelocity,rotatedCoefficients,← Finset.sum_sub_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma expected_logPartition_le_of_pair_distances {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
    ∫ z, logPartition (linearProcess b z) ∂gaussianProduct (Fin n) := by
  let F := fun t ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b t) z) ∂gaussianProduct (Fin n)
  have hd : ∀ t, HasDerivAt F (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t :=
    hasDerivAt_expected_rotated_logPartition a b
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt)
  have hm : MonotoneOn F (Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
      (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (Real.pi/2) := interior_subset ht
    rw [(hd t).deriv]
    apply gaussian_gibbs_derivative_nonneg
    intro i j
    rw [rotation_pair_covariance,horth,mul_zero,add_zero]
    exact mul_nonneg (mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 (ht'.2.trans (by linarith [Real.pi_pos])))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht'.1],ht'.2⟩)) (sub_nonneg.mpr (hdist i j))
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hh := hm ⟨le_rfl,hπ⟩ ⟨hπ,le_rfl⟩ hπ
  have ha0 : rotatedCoefficients a b 0 = a := by funext i k; simp [rotatedCoefficients]
  have hb0 : rotatedCoefficients a b (Real.pi/2) = b := by funext i k; simp [rotatedCoefficients]
  simpa only [F,ha0,hb0] using hh

lemma le_finiteMaximum {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : x i ≤ finiteMaximum x :=
  le_csSup (Set.finite_range x).bddAbove (Set.mem_range_self i)

lemma exists_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∃ i, x i = finiteMaximum x := (Set.range_nonempty x).csSup_mem (Set.finite_range x)

lemma continuous_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@finiteMaximum ι) := by
  have he (x : ι → ℝ) : finiteMaximum x = Finset.univ.sup' Finset.univ_nonempty x := by
    rw [Finset.sup'_eq_csSup_image]
    simp only [Finset.coe_univ,Set.image_univ,finiteMaximum]
  simp_rw [funext he]
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ ↦ continuous_apply i)

lemma abs_finiteMaximum_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |finiteMaximum x| ≤ ∑ i, |x i| := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (Finset.mem_univ i)

lemma finiteMaximum_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ finiteMaximum (linearProcess c z)) (gaussianProduct κ) := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs)).mono'
    ((continuous_finiteMaximum.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def] using abs_finiteMaximum_le (linearProcess c z))

lemma scaled_max_le_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (β : ℝ) : β*finiteMaximum x ≤ logPartition (fun i ↦ β*x i) := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact le_logPartition (fun i ↦ β*x i) i

lemma logPartition_le_scaled_max {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    {β : ℝ} (hβ : 0 ≤ β) : logPartition (fun i ↦ β*x i) ≤ β*finiteMaximum x+Real.log (Fintype.card ι) := by
  exact (logPartition_le _ (fun i ↦ mul_le_mul_of_nonneg_left (le_finiteMaximum x i) hβ)).trans_eq (add_comm _ _)

lemma linearProcess_scaled {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (β : ℝ) (z : κ → ℝ) :
    linearProcess (fun i k ↦ β*c i k) z = fun i ↦ β*linearProcess c z i := by
  funext i
  simp only [linearProcess,Finset.mul_sum,mul_assoc]

lemma expected_max_le_of_pair_distances_orthogonal {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n) := by
  have hb (β : ℝ) (hβ : 0 ≤ β) :
      β*(∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
      β*(∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n)) + Real.log (Fintype.card ι) := by
    have hiA := logPartition_integrable (fun i k ↦ β*a i k)
    have hiB := logPartition_integrable (fun i k ↦ β*b i k)
    have hcomp := expected_logPartition_le_of_pair_distances
      (fun i k ↦ β*a i k) (fun i k ↦ β*b i k)
      (fun i j ↦ by
        calc
          (∑ k, (β*a i k-β*a j k)*(β*b i k-β*b j k)) =
              β^2*(∑ k, (a i k-a j k)*(b i k-b j k)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
          _ = 0 := by rw [horth,mul_zero])
      (fun i j ↦ by
        have he (c : ι → Fin n → ℝ) : (∑ k, (β*c i k-β*c j k)^2) = β^2*∑ k, (c i k-c j k)^2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        rw [he,he]
        exact mul_le_mul_of_nonneg_left (hdist i j) (sq_nonneg β))
    calc
      _ = ∫ z, β*finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n) := by rw [integral_const_mul]
      _ ≤ ∫ z, logPartition (linearProcess (fun i k ↦ β*a i k) z) ∂gaussianProduct (Fin n) := by
        apply integral_mono ((finiteMaximum_integrable a).const_mul _) hiA
        intro z
        change β*finiteMaximum (linearProcess a z) ≤ logPartition (linearProcess (fun i k ↦ β*a i k) z)
        rw [linearProcess_scaled]
        exact scaled_max_le_logPartition _ _
      _ ≤ _ := hcomp
      _ ≤ ∫ z, β*finiteMaximum (linearProcess b z)+Real.log (Fintype.card ι) ∂gaussianProduct (Fin n) := by
        apply integral_mono hiB (((finiteMaximum_integrable b).const_mul _).add (integrable_const _))
        intro z
        change logPartition (linearProcess (fun i k ↦ β*b i k) z) ≤ β*finiteMaximum (linearProcess b z)+Real.log (Fintype.card ι)
        rw [linearProcess_scaled]
        exact logPartition_le_scaled_max _ hβ
      _ = _ := by rw [integral_add ((finiteMaximum_integrable b).const_mul _) (integrable_const _),integral_const_mul,integral_const]; simp
  by_contra hh
  have hΔ : 0 < (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) -
      (∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n)) := sub_pos.mpr (lt_of_not_ge hh)
  let Δ := (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) -
      (∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n))
  let β := (|Real.log (Fintype.card ι)|+1)/Δ
  have hβ : 0 < β := div_pos (by positivity) hΔ
  have hh' := hb β hβ.le
  have he : β*Δ = |Real.log (Fintype.card ι)|+1 := div_mul_cancel₀ _ hΔ.ne'
  have hlog := le_abs_self (Real.log (Fintype.card ι))
  dsimp [Δ] at he
  nlinarith

lemma gaussian_integral_reindex {κ ν : Type*} [Fintype κ] [Fintype ν] (e : κ ≃ ν)
    (f : (κ → ℝ) → ℝ) :
    (∫ z : ν → ℝ, f (fun k ↦ z (e k)) ∂gaussianProduct ν) = ∫ z, f z ∂gaussianProduct κ := by
  have he := measurePreserving_piCongrLeft (α := fun _ : κ ↦ ℝ)
    (fun _ : κ ↦ standardGaussian) e.symm
  have hf (z : ν → ℝ) : (MeasurableEquiv.piCongrLeft (π := fun _ : κ ↦ ℝ) e.symm) z = fun k ↦ z (e k) := by
    funext k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simpa only [gaussianProduct,hf] using he.integral_comp' f

lemma linearProcess_reindex {ι κ ν : Type*} [Fintype κ] [Fintype ν]
    (c : ι → κ → ℝ) (e : κ ≃ ν) (z : ν → ℝ) :
    linearProcess c (fun k ↦ z (e k)) = linearProcess (fun i l ↦ c i (e.symm l)) z := by
  funext i
  simpa only [linearProcess, Equiv.symm_apply_apply] using e.sum_comp (fun l ↦ c i (e.symm l)*z l)

lemma expected_max_reindex {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (c : ι → κ → ℝ) (e : κ ≃ ν) :
    (∫ z, finiteMaximum (linearProcess (fun i l ↦ c i (e.symm l)) z) ∂gaussianProduct ν) =
    ∫ z, finiteMaximum (linearProcess c z) ∂gaussianProduct κ := by
  simpa only [linearProcess_reindex] using gaussian_integral_reindex e (fun z ↦ finiteMaximum (linearProcess c z))

lemma expected_max_le_of_pair_distances_orthogonal_fintype {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ι → κ → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct κ := by
  let e := Fintype.equivFin κ
  have hh := expected_max_le_of_pair_distances_orthogonal
    (fun i k ↦ a i (e.symm k)) (fun i k ↦ b i (e.symm k))
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)*(b i k-b j k))]
      exact horth i j)
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)^2), e.symm.sum_comp (fun k ↦ (b i k-b j k)^2)]
      exact hdist i j)
  simpa only [expected_max_reindex] using hh

lemma expected_max_embedLeft {ι κ ν : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) :
    (∫ z, finiteMaximum (linearProcess (embedLeft (ν := ν) a) z) ∂gaussianProduct (κ ⊕ ν)) =
    ∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, finiteMaximum (linearProcess (embedLeft a) z) ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ finiteMaximum (linearProcess (embedLeft a) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedLeft a) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ ν ↦ ℝ)).symm p) =
      linearProcess a p.1 := by
    funext i
    simp [linearProcess,embedLeft,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_fst (μ := gaussianProduct κ) (ν := gaussianProduct ν) (fun z ↦ finiteMaximum (linearProcess a z))

lemma expected_max_embedRight {ι κ ν : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (b : ι → ν → ℝ) :
    (∫ z, finiteMaximum (linearProcess (embedRight (κ := κ) b) z) ∂gaussianProduct (κ ⊕ ν)) =
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct ν := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, finiteMaximum (linearProcess (embedRight b) z) ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ finiteMaximum (linearProcess (embedRight b) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedRight b) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ ν ↦ ℝ)).symm p) =
      linearProcess b p.2 := by
    funext i
    simp [linearProcess,embedRight,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_snd (μ := gaussianProduct κ) (ν := gaussianProduct ν) (fun z ↦ finiteMaximum (linearProcess b z))

lemma expected_max_le_of_pair_distances {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct ν := by
  have h := expected_max_le_of_pair_distances_orthogonal_fintype
    (embedLeft (ν := ν) a) (embedRight (κ := κ) b)
    (fun i j ↦ by simp [embedLeft,embedRight,Fintype.sum_sum_type])
    (fun i j ↦ by simpa only [Fintype.sum_sum_type,embedLeft,embedRight,
      Sum.elim_inl,Sum.elim_inr,sub_self,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_add,add_zero] using hdist i j)
  simpa only [expected_max_embedLeft,expected_max_embedRight] using h

lemma spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]

lemma linearProcess_hamCoeff (n : ℕ) (J : (Fin n × Fin n) → ℝ) :
    linearProcess (hamCoeff n) J = hamiltonian n J := by
  funext σ
  simp only [linearProcess,hamCoeff,hamiltonian,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma groundStateSequence_eq (n : ℕ) : groundStateSequence n = (n : ℝ)⁻¹ * expectedMaximum n := by
  simp only [groundStateSequence,expectedMaximum,linearProcess_hamCoeff,finiteMaximum]

lemma twice_upper_sum {ι : Type*} [Fintype ι] [LinearOrder ι] (f : ι → ι → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    2*(∑ i, ∑ j, if i < j then f i j else 0) = ∑ i, ∑ j, f i j := by
  have hs : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hsplit (i j : ι) : f i j = (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp [hdiag]
    · simp [h,not_lt_of_ge h.le]
  conv_rhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
  simp only [Finset.sum_add_distrib,hs]
  ring

lemma spin_pair_difference {dimension : ℕ} (σ τ : Fin dimension → Bool) (i j : Fin dimension) :
    (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 =
      2-2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by
  have h1 := spin_sq (σ i)
  have h2 := spin_sq (σ j)
  have h3 := spin_sq (τ i)
  have h4 := spin_sq (τ j)
  calc
    _ = (spin (σ i))^2*(spin (σ j))^2+(spin (τ i))^2*(spin (τ j))^2 -
      2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by ring
    _ = _ := by rw [h1,h2,h3,h4]; ring

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BlockCoeff
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma hamCoeff_distance {n : ℕ} (hn : 0 < n) (σ τ : Fin n → Bool) :
    (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
    (n : ℝ) - (∑ i, spin (σ i)*spin (τ i))^2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt := Real.sq_sqrt hn'.le
  have hn0 := ne_of_gt hn'
  have hs0 := Real.sqrt_ne_zero'.mpr hn'
  have hu := twice_upper_sum (fun i j ↦ (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2)
    (fun i j ↦ by ring) (fun i ↦ by rw [← sq,← sq,spin_sq,spin_sq]; norm_num)
  have he : (∑ i, ∑ j, (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2) =
      2*(n : ℝ)^2 - 2*(∑ i, spin (σ i)*spin (τ i))^2 := by
    simp_rw [spin_pair_difference,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hc : (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
      (Real.sqrt (n : ℝ))⁻¹^2 *
      ∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0 := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum,hamCoeff]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hc,inv_pow,hsqrt]
  rw [he] at hu
  have ht : (∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0) =
      (n : ℝ)^2 - (∑ i, spin (σ i)*spin (τ i))^2 := by linarith
  rw [ht]
  field_simp

lemma weighted_square_div_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    (x+y)^2/(a+b) ≤ x^2/a+y^2/b := by
  have hab : 0 < a+b := add_pos ha hb
  have he : x^2/a+y^2/b = (b*x^2+a*y^2)/(a*b) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ hab (mul_pos ha hb)).2
  nlinarith [sq_nonneg (b*x-a*y)]

lemma blockCoeff_distance_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (σ τ : Fin (n+m) → Bool) :
    (∑ k, (blockCoeff n m σ k-blockCoeff n m τ k)^2) ≤
      ∑ k, (hamCoeff (n+m) σ k-hamCoeff (n+m) τ k)^2 := by
  simp only [Fintype.sum_sum_type,blockCoeff,Sum.elim_inl,Sum.elim_inr]
  rw [hamCoeff_distance hn,hamCoeff_distance hm,hamCoeff_distance (by omega)]
  rw [Fin.sum_univ_add,Nat.cast_add]
  have hh := weighted_square_div_le (by exact_mod_cast hn : (0 : ℝ) < n)
    (by exact_mod_cast hm : (0 : ℝ) < m)
    (∑ i : Fin n, spin (σ (Fin.castAdd m i))*spin (τ (Fin.castAdd m i)))
    (∑ i : Fin m, spin (σ (Fin.natAdd n i))*spin (τ (Fin.natAdd n i)))
  linarith

lemma finiteMaximum_append_sum {n m : ℕ} (f : (Fin n → Bool) → ℝ)
    (g : (Fin m → Bool) → ℝ) :
    finiteMaximum (fun σ : Fin (n+m) → Bool ↦
      f (fun i ↦ σ (Fin.castAdd m i))+g (fun i ↦ σ (Fin.natAdd n i))) =
    finiteMaximum f + finiteMaximum g := by
  apply le_antisymm
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum (fun σ : Fin (n+m) → Bool ↦
      f (fun i ↦ σ (Fin.castAdd m i))+g (fun i ↦ σ (Fin.natAdd n i)))
    rw [← hσ]
    exact add_le_add (le_finiteMaximum _ _) (le_finiteMaximum _ _)
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum f
    obtain ⟨τ,hτ⟩ := exists_finiteMaximum g
    have hh := le_finiteMaximum (fun η : Fin (n+m) → Bool ↦
      f (fun i ↦ η (Fin.castAdd m i))+g (fun i ↦ η (Fin.natAdd n i))) (Fin.append σ τ)
    simpa only [Fin.append_left,Fin.append_right,hσ,hτ] using hh

lemma expected_max_block (n m : ℕ) :
    (∫ J, finiteMaximum (linearProcess (blockCoeff n m) J)
      ∂gaussianProduct ((Fin n × Fin n) ⊕ (Fin m × Fin m))) =
    expectedMaximum n + expectedMaximum m := by
  have he := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ standardGaussian)
  change (∫ J, finiteMaximum (linearProcess (blockCoeff n m) J)
    ∂Measure.pi (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun J ↦ finiteMaximum (linearProcess (blockCoeff n m) J))]
  have hlin (p : ((Fin n × Fin n) → ℝ) × ((Fin m × Fin m) → ℝ)) :
      linearProcess (blockCoeff n m)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ ℝ)).symm p) =
      (fun σ ↦ linearProcess (hamCoeff n) p.1 (fun i ↦ σ (Fin.castAdd m i))+
        linearProcess (hamCoeff m) p.2 (fun i ↦ σ (Fin.natAdd n i))) := by
    funext σ
    simp [linearProcess,blockCoeff,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin,finiteMaximum_append_sum]
  change (∫ p, finiteMaximum (linearProcess (hamCoeff n) p.1)+
    finiteMaximum (linearProcess (hamCoeff m) p.2)
      ∂(gaussianProduct (Fin n × Fin n)).prod (gaussianProduct (Fin m × Fin m))) = _
  rw [integral_add ((finiteMaximum_integrable (hamCoeff n)).comp_fst _)
    ((finiteMaximum_integrable (hamCoeff m)).comp_snd _),
    integral_fun_fst (fun J ↦ finiteMaximum (linearProcess (hamCoeff n) J)),
    integral_fun_snd (fun J ↦ finiteMaximum (linearProcess (hamCoeff m) J))]
  simp [expectedMaximum]

lemma expectedMaximum_zero : expectedMaximum 0 = 0 := by
  have hh (J : (Fin 0 × Fin 0) → ℝ) : linearProcess (hamCoeff 0) J = fun _ ↦ 0 := by
    funext σ
    simp [linearProcess]
  simp [expectedMaximum,hh,finiteMaximum]

lemma expectedMaximum_superadditive (n m : ℕ) : expectedMaximum n + expectedMaximum m ≤ expectedMaximum (n+m) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [expectedMaximum_zero]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [expectedMaximum_zero]
  exact (expected_max_block n m).symm.le.trans
    (expected_max_le_of_pair_distances (blockCoeff n m) (hamCoeff (n+m)) (blockCoeff_distance_le hn hm))

lemma integrable_exp_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    Integrable (fun z ↦ Real.exp (linearProcess c z i)) (gaussianProduct κ) := by
  simpa only [gaussianProduct,standardGaussian,linearProcess,Real.exp_sum] using
    Integrable.fintype_prod (fun k : κ ↦ integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (c i k))

lemma integral_exp_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    (∫ z, Real.exp (linearProcess c z i) ∂gaussianProduct κ) = Real.exp ((∑ k, (c i k)^2)/2) := by
  simp only [gaussianProduct,linearProcess,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun k x ↦ Real.exp (c i k*x))]
  have hg (r : ℝ) : (∫ x, Real.exp (r*x) ∂standardGaussian) = Real.exp (r^2/2) := by
    simpa [mgf,standardGaussian] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) r
  simp_rw [hg]
  rw [← Real.exp_sum,Finset.sum_div]

lemma integral_logPartition_upper {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess c z) ∂gaussianProduct κ) ≤
      Real.log (∑ i, Real.exp ((∑ k, (c i k)^2)/2)) := by
  let Z := fun z ↦ ∑ i, Real.exp (linearProcess c z i)
  let E := ∑ i, Real.exp ((∑ k, (c i k)^2)/2)
  have hZ : Integrable Z (gaussianProduct κ) := integrable_finsetSum _ (fun i _ ↦ integrable_exp_linearProcess c i)
  have hE : (∫ z, Z z ∂gaussianProduct κ) = E := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_exp_linearProcess c i)]
    simp only [integral_exp_linearProcess,E]
  have hEp : 0 < E := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hZp (z) : 0 < Z z := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hlog (z) : logPartition (linearProcess c z) ≤ Z z/E-1+Real.log E := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hZp z) hEp)
    rw [Real.log_div (hZp z).ne' hEp.ne'] at hh
    exact sub_le_iff_le_add.mp hh
  have hh := integral_mono (logPartition_integrable c)
    (((hZ.div_const E).sub (integrable_const 1)).add (integrable_const (Real.log E))) hlog
  change (∫ z, logPartition (linearProcess c z) ∂gaussianProduct κ) ≤
    (∫ z, (Z z/E-1)+Real.log E ∂gaussianProduct κ) at hh
  rw [integral_add (f := fun z ↦ Z z/E-1) (g := fun _ ↦ Real.log E)
    ((hZ.div_const E).sub (integrable_const 1)) (integrable_const _),
    integral_sub (f := fun z ↦ Z z/E) (g := fun _ ↦ 1) (hZ.div_const E) (integrable_const 1),
    integral_div,hE] at hh
  simpa only [div_self hEp.ne',integral_const,probReal_univ,one_smul,sub_self,zero_add] using hh

lemma upper_triangle_count_bound (n : ℕ) :
    2*(∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) ≤ (n : ℝ)^2 := by
  have h := twice_upper_sum (fun i j : Fin n ↦ if i=j then (0 : ℝ) else 1)
    (fun i j ↦ by simp only [eq_comm]) (fun i ↦ by simp)
  have he : (∑ i : Fin n, ∑ j : Fin n, if i < j then (if i=j then (0 : ℝ) else 1) else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [hij,ne_of_lt hij]
    · simp [hij]
  rw [he] at h
  rw [h]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> norm_num
    _ = _ := by simp; ring

lemma hamCoeff_variance_bound (n : ℕ) (σ : Fin n → Bool) :
    (∑ k, (hamCoeff n σ k)^2) ≤ (n : ℝ)/2 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (∑ k, (hamCoeff n σ k)^2) = (n : ℝ)⁻¹ *
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0 := by
    simp only [hamCoeff,Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [mul_pow,mul_pow,spin_sq,spin_sq,inv_pow,Real.sq_sqrt hn'.le]
      ring
    · ring
  rw [he,← div_eq_inv_mul]
  apply (div_le_iff₀ hn').2
  have hh := upper_triangle_count_bound n
  nlinarith

lemma expectedMaximum_upper (n : ℕ) :
    expectedMaximum n ≤ (n : ℝ)*(Real.log 2+1/4) := by
  have hmax (J) : finiteMaximum (linearProcess (hamCoeff n) J) ≤
      logPartition (linearProcess (hamCoeff n) J) := by
    obtain ⟨σ,hσ⟩ := exists_finiteMaximum (linearProcess (hamCoeff n) J)
    rw [← hσ]
    exact le_logPartition _ _
  have hsum : (∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2)) ≤
      (2 : ℝ)^n * Real.exp ((n : ℝ)/4) := by
    calc
      _ ≤ ∑ σ : Fin n → Bool, Real.exp ((n : ℝ)/4) := by
        apply Finset.sum_le_sum
        intro σ _
        apply Real.exp_le_exp.mpr
        have hh := hamCoeff_variance_bound n σ
        linarith
      _ = _ := by simp
  have hsumpos : (0 : ℝ) < ∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2) :=
    Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty
  calc
    expectedMaximum n ≤ ∫ J, logPartition (linearProcess (hamCoeff n) J) ∂gaussianProduct (Fin n × Fin n) :=
      integral_mono (finiteMaximum_integrable (hamCoeff n)) (logPartition_integrable (hamCoeff n)) hmax
    _ ≤ Real.log (∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2)) :=
      integral_logPartition_upper (hamCoeff n)
    _ ≤ Real.log ((2 : ℝ)^n*Real.exp ((n : ℝ)/4)) := Real.log_le_log hsumpos hsum
    _ = _ := by rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (Real.exp_ne_zero _),Real.log_pow,Real.log_exp]; ring

theorem groundStateSequence_tendsto :
    Tendsto groundStateSequence atTop (𝓝 groundStateValue) := by
  let u : ℕ → ℝ := fun n ↦ -expectedMaximum n
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [expectedMaximum_superadditive n m]
  have hC : 0 ≤ Real.log 2+1/4 := by positivity
  have hb : BddBelow (range (fun n : ℕ ↦ u n/n)) := by
    refine ⟨-(Real.log 2+1/4), ?_⟩
    rintro y ⟨n,rfl⟩
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [Nat.cast_zero,div_zero]
      linarith
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hh : expectedMaximum n/n ≤ Real.log 2+1/4 := by
      apply (div_le_iff₀ hn').2
      simpa only [mul_comm] using expectedMaximum_upper n
    dsimp [u]
    rw [neg_div]
    linarith
  apply tendsto_nhds_limUnder
  refine ⟨-hu.lim, ?_⟩
  have hh := (hu.tendsto_lim hb).neg
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp [groundStateSequence_eq,u,div_eq_mul_inv,mul_comm]

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_LogComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma expected_logPartition_reindex {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [Fintype ν] (e : κ ≃ ν) (a : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess (fun i k ↦ a i (e.symm k)) z)
      ∂gaussianProduct ν) = ∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ := by
  simpa only [linearProcess_reindex] using gaussian_integral_reindex e
    (fun z ↦ logPartition (linearProcess a z))

lemma expected_logPartition_le_orthogonal {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ι → κ → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ) ≤
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct κ := by
  let e := Fintype.equivFin κ
  have h := expected_logPartition_le_of_pair_distances
    (fun i k ↦ a i (e.symm k)) (fun i k ↦ b i (e.symm k))
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)*(b i k-b j k))]
      exact horth i j)
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)^2),
        e.symm.sum_comp (fun k ↦ (b i k-b j k)^2)]
      exact hdist i j)
  simpa only [expected_logPartition_reindex] using h

lemma expected_logPartition_embedLeft {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess (embedLeft (ν := ν) a) z) ∂gaussianProduct (κ ⊕ ν)) =
      ∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, logPartition (linearProcess (embedLeft a) z)
    ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ logPartition (linearProcess (embedLeft a) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedLeft a) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : κ ⊕ ν ↦ ℝ)).symm p) = linearProcess a p.1 := by
    funext i
    simp [linearProcess,embedLeft,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_fst (μ := gaussianProduct κ)
    (ν := gaussianProduct ν) (fun z ↦ logPartition (linearProcess a z))

lemma expected_logPartition_embedRight {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (b : ι → ν → ℝ) :
    (∫ z, logPartition (linearProcess (embedRight (κ := κ) b) z) ∂gaussianProduct (κ ⊕ ν)) =
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct ν := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, logPartition (linearProcess (embedRight b) z)
    ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ logPartition (linearProcess (embedRight b) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedRight b) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : κ ⊕ ν ↦ ℝ)).symm p) = linearProcess b p.2 := by
    funext i
    simp [linearProcess,embedRight,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_snd (μ := gaussianProduct κ)
    (ν := gaussianProduct ν) (fun z ↦ logPartition (linearProcess b z))

lemma expected_logPartition_le {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ) ≤
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct ν := by
  have h := expected_logPartition_le_orthogonal
    (embedLeft (ν := ν) a) (embedRight (κ := κ) b)
    (fun i j ↦ by simp [embedLeft,embedRight,Fintype.sum_sum_type])
    (fun i j ↦ by simpa only [Fintype.sum_sum_type,embedLeft,embedRight,
      Sum.elim_inl,Sum.elim_inr,sub_self,zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero,zero_add,add_zero] using hdist i j)
  simpa only [expected_logPartition_embedLeft,expected_logPartition_embedRight] using h

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma finiteMaximum_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) : finiteMaximum (fun i ↦ x i+c)=finiteMaximum x+c := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  obtain ⟨j,hj⟩ := exists_finiteMaximum (fun i ↦ x i+c)
  apply le_antisymm
  · rw [← hj]
    linarith [le_finiteMaximum x j]
  · rw [← hi]
    exact le_finiteMaximum (fun i ↦ x i+c) i

lemma affineMaximum_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a : ι → κ → ℝ) (d : ι → ℝ) :
    Integrable (fun z ↦ finiteMaximum (fun i ↦ linearProcess a z i+d i)) (gaussianProduct κ) := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦
    ((linearProcess_integrable a i).add (integrable_const (d i))).abs)).mono'
  · exact (continuous_finiteMaximum.comp ((continuous_linearProcess a).add continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z ↦ by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_finiteMaximum_le
        (fun i ↦ linearProcess a z i + d i))

lemma replicated_partition_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (x d : ι → ℝ) (β : ℝ) (hβ : 0≤β) (m : ι → ℕ)
    (hl : ∀ i, Real.exp (β*d i) ≤ (m i : ℝ))
    (hu : ∀ i, (m i : ℝ) ≤ 2*Real.exp (β*d i)) :
    β*finiteMaximum (fun i ↦ x i+d i) ≤
        logPartition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ∧
      logPartition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ≤
        β*finiteMaximum (fun i ↦ x i+d i)+Real.log (2*(Fintype.card ι : ℝ)) := by
  have hp : partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) =
      ∑ i, (m i : ℝ)*Real.exp (β*x i) := by
    simp [partition,Fintype.sum_sigma]
  have hlo : Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) ≤
      partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) := by
    obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i ↦ x i+d i)
    rw [← hi,hp]
    calc
      _ = Real.exp (β*d i)*Real.exp (β*x i) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ (m i : ℝ)*Real.exp (β*x i) := mul_le_mul_of_nonneg_right (hl i) (Real.exp_pos _).le
      _ ≤ _ := Finset.single_le_sum (f := fun j ↦ (m j : ℝ)*Real.exp (β*x j)) (fun j _ ↦ by positivity) (Finset.mem_univ i)
  have hup : partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ≤
      2*(Fintype.card ι : ℝ)*Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) := by
    rw [hp]
    calc
      _ ≤ ∑ i : ι, 2*Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ 2*Real.exp (β*d i)*Real.exp (β*x i) :=
            mul_le_mul_of_nonneg_right (hu i) (Real.exp_pos _).le
          _ = 2*Real.exp (β*(x i+d i)) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_finiteMaximum (fun i ↦ x i+d i) i) hβ)) (by norm_num)
      _ = _ := by simp; ring
  refine ⟨?_,?_⟩
  · simpa only [Real.log_exp,logPartition] using Real.log_le_log (Real.exp_pos _) hlo
  · have hc : 0<2*(Fintype.card ι : ℝ) := by positivity
    have hh := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hup
    simpa only [logPartition,Real.log_mul hc.ne' (Real.exp_pos _).ne',
      Real.log_exp,add_comm] using hh

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_AffineComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

theorem expected_affine_max_le {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ) (d : ι → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (fun i ↦ linearProcess a z i+d i) ∂gaussianProduct κ) ≤
      ∫ z, finiteMaximum (fun i ↦ linearProcess b z i+d i) ∂gaussianProduct ν := by
  classical
  let A := fun z ↦ finiteMaximum (fun i ↦ linearProcess a z i+d i)
  let B := fun z ↦ finiteMaximum (fun i ↦ linearProcess b z i+d i)
  have hiA : Integrable A (gaussianProduct κ) := affineMaximum_integrable a d
  have hiB : Integrable B (gaussianProduct ν) := affineMaximum_integrable b d
  let C := ∑ i, |d i|
  have hC (i : ι) : 0 ≤ d i+C := by
    have h := Finset.single_le_sum (fun j _ ↦ abs_nonneg (d j)) (Finset.mem_univ i)
    have hh := neg_abs_le (d i)
    dsimp [C]
    linarith
  let L := Real.log (2*(Fintype.card ι : ℝ))
  have hβbound (β : ℝ) (hβ : 0 ≤ β) :
      β*(∫ z, A z ∂gaussianProduct κ) ≤ β*(∫ z, B z ∂gaussianProduct ν)+L := by
    let m : ι → ℕ := fun i ↦ ⌈Real.exp (β*(d i+C))⌉₊
    have hm (i : ι) : 0 < m i := Nat.ceil_pos.mpr (Real.exp_pos _)
    let : Nonempty (Σ i, Fin (m i)) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty ι),⟨0,hm _⟩⟩⟩
    have hl (i : ι) : Real.exp (β*(d i+C)) ≤ (m i : ℝ) := Nat.le_ceil _
    have hu (i : ι) : (m i : ℝ) ≤ 2*Real.exp (β*(d i+C)) := by
      have he : 1 ≤ Real.exp (β*(d i+C)) := Real.one_le_exp_iff.mpr (mul_nonneg hβ (hC i))
      have hh := Nat.ceil_lt_add_one (Real.exp_pos (β*(d i+C))).le
      dsimp [m]
      linarith
    let a' : (Σ i, Fin (m i)) → κ → ℝ := fun i k ↦ β*a i.1 k
    let b' : (Σ i, Fin (m i)) → ν → ℝ := fun i k ↦ β*b i.1 k
    have hcomp := expected_logPartition_le a' b' (fun i j ↦ by
      have heA : (∑ k, (β*a i.1 k-β*a j.1 k)^2) =
          β^2*∑ k, (a i.1 k-a j.1 k)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      have heB : (∑ k, (β*b i.1 k-β*b j.1 k)^2) =
          β^2*∑ k, (b i.1 k-b j.1 k)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      dsimp [a',b']
      rw [heA,heB]
      exact mul_le_mul_of_nonneg_left (hdist i.1 j.1) (sq_nonneg β))
    have hAi := logPartition_integrable a'
    have hBi := logPartition_integrable b'
    have hlow (z : κ → ℝ) : β*(A z+C) ≤ logPartition (linearProcess a' z) := by
      have h := (replicated_partition_bounds (linearProcess a z)
        (fun i ↦ d i+C) β hβ m hl hu).1
      have he : (fun i ↦ linearProcess a z i+(d i+C)) =
          (fun i ↦ (linearProcess a z i+d i)+C) := by funext i; ring
      rw [he,finiteMaximum_add_const] at h
      simpa only [A,a',linearProcess_scaled,linearProcess] using h
    have hupp (z : ν → ℝ) : logPartition (linearProcess b' z) ≤ β*(B z+C)+L := by
      have h := (replicated_partition_bounds (linearProcess b z)
        (fun i ↦ d i+C) β hβ m hl hu).2
      have he : (fun i ↦ linearProcess b z i+(d i+C)) =
          (fun i ↦ (linearProcess b z i+d i)+C) := by funext i; ring
      rw [he,finiteMaximum_add_const] at h
      simpa only [B,b',linearProcess_scaled,linearProcess,L] using h
    have h1 := integral_mono ((hiA.add (integrable_const C)).const_mul β) hAi hlow
    have h2 := integral_mono hBi
      (((hiB.add (integrable_const C)).const_mul β).add (integrable_const L)) hupp
    have h := h1.trans (hcomp.trans h2)
    simp only [Pi.add_apply] at h
    rw [integral_const_mul,integral_add hiA (integrable_const C),integral_const] at h
    have hiB' : Integrable (fun z ↦ β*(B z+C)) (gaussianProduct ν) :=
      (hiB.add (integrable_const C)).const_mul β
    rw [integral_add hiB' (integrable_const L),
      integral_const_mul,integral_add hiB (integrable_const C),integral_const,integral_const] at h
    simp only [probReal_univ,one_smul] at h
    linarith
  by_contra hh
  have hΔ : 0 < (∫ z, A z ∂gaussianProduct κ)-(∫ z, B z ∂gaussianProduct ν) :=
    sub_pos.mpr (lt_of_not_ge hh)
  let Δ := (∫ z, A z ∂gaussianProduct κ)-(∫ z, B z ∂gaussianProduct ν)
  let β := (|L|+1)/Δ
  have hb : 0<β := div_pos (by positivity) hΔ
  have h := hβbound β hb.le
  have he : β*Δ=|L|+1 := div_mul_cancel₀ _ hΔ.ne'
  have hl := le_abs_self L
  dsimp [Δ] at he
  nlinarith

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma product_inner_sum {κ ν : Type*} [Fintype κ] [Fintype ν]
    (x y : κ → ℝ) (u v : ν → ℝ) :
    (∑ k : κ×ν, (x k.1*u k.2)*(y k.1*v k.2)) =
      (∑ k, x k*y k)*(∑ k, u k*v k) := by
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sq_distance_sum {κ : Type*} [Fintype κ] (x y : κ → ℝ) :
    (∑ k, (x k-y k)^2) = (∑ k, x k^2)+(∑ k, y k^2)-2*(∑ k, x k*y k) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GaussianColumn
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable {κ : Type*} [Fintype κ]

lemma euclidean_inner_sum (x y : EuclideanSpace ℝ κ) :
    ⟪x,y⟫=∑ k,x k*y k := by
  simp only [PiLp.inner_apply,Real.inner_apply]

lemma columnResidual_inner {v : EuclideanSpace ℝ κ} (hv : ⟪v,v⟫=1)
    (w w' : EuclideanSpace ℝ κ) :
    ⟪columnResidual v w,columnResidual v w'⟫=⟪w,w'⟫-⟪v,w⟫*⟪v,w'⟫ := by
  simp only [columnResidual,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,hv]
  rw [real_inner_comm w v]
  ring

lemma columnResidual_orthogonal {v : EuclideanSpace ℝ κ} (hv : ⟪v,v⟫=1)
    (w : EuclideanSpace ℝ κ) : ⟪v,columnResidual v w⟫=0 := by
  simp only [columnResidual,inner_sub_right,real_inner_smul_right,hv,mul_one,sub_self]

lemma quadraticCoeff_inner (x y : EuclideanSpace ℝ κ) :
    (∑ k,quadraticCoeff x k*quadraticCoeff y k)=⟪x,y⟫^2/2 := by
  have hs : Real.sqrt 2 ^ 2=2 := Real.sq_sqrt (by norm_num)
  calc
    _ = (∑ k : κ×κ,(x k.1*x k.2)*(y k.1*y k.2))/(Real.sqrt 2)^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [quadraticCoeff]
      ring
    _ = _ := by rw [product_inner_sum,←euclidean_inner_sum,hs]; ring

lemma columnVector_inner {v : EuclideanSpace ℝ κ} (hv : ⟪v,v⟫=1)
    (w w' : EuclideanSpace ℝ κ) :
    ⟪columnVector v w,columnVector v w'⟫=
      ⟪v,w⟫*⟪v,w'⟫*(⟪w,w'⟫-⟪v,w⟫*⟪v,w'⟫)+⟪v,w⟫^2*⟪v,w'⟫^2/2 := by
  have hs : Real.sqrt 2 ^ 2=2 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have ho := columnResidual_orthogonal hv w
  have ho' := columnResidual_orthogonal hv w'
  have hor : ⟪columnResidual v w,v⟫=0 := by rwa [real_inner_comm]
  simp only [columnVector,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,ho',hor,hv,columnResidual_inner hv]
  field_simp
  ring_nf
  simp only [hs]
  ring

lemma columnSplitCoeff_inner {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w w' : EuclideanSpace ℝ κ) :
    (∑ k,columnSplitCoeff v w k*columnSplitCoeff v w' k)=
      ∑ k,quadraticCoeff w k*quadraticCoeff w' k := by
  rcases hv with rfl|hv
  · simp [columnSplitCoeff,columnVector,columnResidual,Fintype.sum_sum_type]
  · rw [Fintype.sum_sum_type]
    simp only [columnSplitCoeff,Sum.elim_inl,Sum.elim_inr]
    rw [←euclidean_inner_sum,columnVector_inner hv,quadraticCoeff_inner,
      columnResidual_inner hv,quadraticCoeff_inner]
    ring

lemma columnSplitCoeff_distance {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w w' : EuclideanSpace ℝ κ) :
    (∑ k,(columnSplitCoeff v w k-columnSplitCoeff v w' k)^2)=
      ∑ k,(quadraticCoeff w k-quadraticCoeff w' k)^2 := by
  rw [sq_distance_sum,sq_distance_sum]
  simp only [sq]
  rw [columnSplitCoeff_inner hv,columnSplitCoeff_inner hv,columnSplitCoeff_inner hv]

theorem expected_max_column_split {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ)
    (v : EuclideanSpace ℝ κ) (hv : v=0 ∨ ⟪v,v⟫=1) :
    (∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w i)) z i+d i)
       ∂gaussianProduct (κ×κ))=
    ∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ columnSplitCoeff v (w i)) z i+d i)
       ∂gaussianProduct (κ ⊕ (κ×κ)) := by
  apply le_antisymm
  · exact expected_affine_max_le _ _ d (fun i j ↦ (columnSplitCoeff_distance hv (w i) (w j)).symm.le)
  · exact expected_affine_max_le _ _ d (fun i j ↦ (columnSplitCoeff_distance hv (w i) (w j)).le)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

omit [Fintype ι] [Nonempty ι] in
lemma linearProcess_integral_zero [Fintype ι] [Nonempty ι] {ν : Type*} [Fintype ν]
    (a : ι → ν → ℝ) (i : ι) :
    (∫ z,linearProcess a z i ∂gaussianProduct ν)=0 := by
  simp only [linearProcess]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro k _
    rw [integral_const_mul]
    simp [gaussianProduct,standardGaussian,integral_eval]
  · intro k _
    exact (gaussian_coordinate_integrable k).const_mul _

lemma quadraticValue_ge_offset (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ) (i : ι) :
    d i≤quadraticValue w d := by
  have h := integral_mono
    ((linearProcess_integrable (fun i ↦ quadraticCoeff (w i)) i).add (integrable_const (d i)))
    (affineMaximum_integrable (fun i ↦ quadraticCoeff (w i)) d)
    (fun z ↦ le_finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w i)) z i+d i) i)
  simp only [Pi.add_apply] at h
  rw [integral_add (linearProcess_integrable _ _) (integrable_const _),
    linearProcess_integral_zero,integral_const,probReal_univ,one_smul,zero_add] at h
  exact h

lemma column_product_integrable (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ)
    (v : EuclideanSpace ℝ κ) :
    Integrable (fun p : (κ → ℝ)×((κ×κ) → ℝ) ↦
      finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (columnResidual v (w i))) p.2 i+
        (d i+linearProcess (fun i k ↦ columnVector v (w i) k) p.1 i)))
      ((gaussianProduct κ).prod (gaussianProduct (κ×κ))) := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ (κ×κ) ↦ standardGaussian)
  have hi := affineMaximum_integrable (fun i ↦ columnSplitCoeff v (w i)) d
  have h := (he.integrable_comp hi.aestronglyMeasurable).2 hi
  change Integrable _ ((gaussianProduct κ).prod (gaussianProduct (κ×κ))) at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  congr 1
  ext i
  simp [linearProcess,columnSplitCoeff,Fintype.sum_sum_type,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  ring

theorem quadraticValue_column (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ)
    (v : EuclideanSpace ℝ κ) (hv : v=0 ∨ ⟪v,v⟫=1) :
    quadraticValue w d =
      ∫ z,quadraticValue (fun i ↦ columnResidual v (w i))
        (fun i ↦ d i+linearProcess (fun i k ↦ columnVector v (w i) k) z i)
        ∂gaussianProduct κ := by
  unfold quadraticValue
  rw [expected_max_column_split w d v hv]
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ (κ×κ) ↦ standardGaussian)
  change (∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ columnSplitCoeff v (w i)) z i+d i)
    ∂Measure.pi (fun _ : κ ⊕ (κ×κ) ↦ standardGaussian)) = _
  rw [←he.integral_comp' (fun z ↦ finiteMaximum (fun i ↦
    linearProcess (fun i ↦ columnSplitCoeff v (w i)) z i+d i))]
  have heq (p : (κ → ℝ)×((κ×κ) → ℝ)) :
      (fun i ↦ linearProcess (fun i ↦ columnSplitCoeff v (w i))
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ (κ×κ) ↦ ℝ)).symm p) i+d i)=
      (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (columnResidual v (w i))) p.2 i+
        (d i+linearProcess (fun i k ↦ columnVector v (w i) k) p.1 i)) := by
    ext i
    simp [linearProcess,columnSplitCoeff,Fintype.sum_sum_type,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm,Sum.elim_inl,Sum.elim_inr]
    ring
  simp only [heq]
  exact integral_prod _ (column_product_integrable w d v)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_ColumnBounds
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {κ : Type*} [Fintype κ]

lemma columnResidual_norm_le {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w : EuclideanSpace ℝ κ) :
    ‖columnResidual v w‖≤‖w‖ := by
  rcases hv with rfl|hv
  · simp [columnResidual]
  · have he := columnResidual_inner hv w w
    simp only [real_inner_self_eq_norm_sq] at he
    nlinarith [norm_nonneg w,norm_nonneg (columnResidual v w),sq_nonneg ⟪v,w⟫]

lemma columnVector_norm_le {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w : EuclideanSpace ℝ κ) :
    ‖columnVector v w‖≤‖w‖^2 := by
  have he := columnSplitCoeff_inner hv w w
  rw [Fintype.sum_sum_type] at he
  simp only [columnSplitCoeff,Sum.elim_inl,Sum.elim_inr] at he
  rw [←euclidean_inner_sum,quadraticCoeff_inner,quadraticCoeff_inner] at he
  simp only [real_inner_self_eq_norm_sq] at he
  have hn : 0≤‖columnVector v w‖ := norm_nonneg _
  have hp := sq_nonneg (‖columnResidual v w‖^2)
  have hw := sq_nonneg (‖w‖^2)
  exact (sq_le_sq₀ hn (sq_nonneg _)).mp (by nlinarith)

lemma quadraticCoeff_coord_bound (w : EuclideanSpace ℝ κ) (k : κ×κ) :
    |quadraticCoeff w k|≤‖w‖^2 := by
  have h1 : |w k.1|≤‖w‖ := PiLp.norm_apply_le w k.1
  have h2 : |w k.2|≤‖w‖ := PiLp.norm_apply_le w k.2
  have hs : 1≤Real.sqrt 2 := by norm_num
  rw [quadraticCoeff,abs_div,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
  calc
    _ ≤ ‖w‖*‖w‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = ‖w‖^2 := by ring
    _ ≤ ‖w‖^2*Real.sqrt 2 := le_mul_of_one_le_right (sq_nonneg _) hs

lemma measurable_columnResidual {Ω : Type*} [MeasurableSpace Ω]
    {v w : Ω → EuclideanSpace ℝ κ} (hv : Measurable v) (hw : Measurable w) :
    Measurable (fun ω ↦ columnResidual (v ω) (w ω)) := by
  unfold columnResidual
  fun_prop

lemma measurable_columnVector {Ω : Type*} [MeasurableSpace Ω]
    {v w : Ω → EuclideanSpace ℝ κ} (hv : Measurable v) (hw : Measurable w) :
    Measurable (fun ω ↦ columnVector (v ω) (w ω)) := by
  unfold columnVector
  have hi : Measurable (fun ω ↦ (⟪v ω,w ω⟫ : ℝ)) := hv.inner hw
  exact (hi.smul (measurable_columnResidual hv hw)).add
    ((hi.pow_const 2 |>.div_const _).smul hv)

lemma gramSchmidt_eq_sub_sum_nat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E) (j : ℕ) :
    gramSchmidt ℝ f j=f j-∑ i∈Finset.range j,
      (⟪gramSchmidt ℝ f i,f j⟫/‖gramSchmidt ℝ f i‖^2) • gramSchmidt ℝ f i := by
  have he := gramSchmidt_def'' ℝ f j
  simp only [Nat.Iio_eq_range] at he
  exact eq_sub_iff_add_eq.mpr he.symm

lemma measurable_gramSchmidt {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : Ω → ℕ → E) (hf : ∀ j,Measurable (fun ω ↦ f ω j))
    (j : ℕ) : Measurable (fun ω ↦ gramSchmidt ℝ (f ω) j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    simp_rw [show (fun ω ↦ gramSchmidt ℝ (f ω) j) =
      (fun ω ↦ f ω j-∑ i∈Finset.range j,
        (⟪gramSchmidt ℝ (f ω) i,f ω j⟫/‖gramSchmidt ℝ (f ω) i‖^2) •
          gramSchmidt ℝ (f ω) i) from funext (fun ω ↦ gramSchmidt_eq_sub_sum_nat (f ω) j)]
    apply (hf j).sub
    apply Finset.measurable_sum
    intro i hi
    have hg := ih i (Finset.mem_range.mp hi)
    exact ((hg.inner (hf j)).div (hg.norm.pow_const 2)).smul hg

lemma measurable_gramSchmidtNormed {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : Ω → ℕ → E) (hf : ∀ j,Measurable (fun ω ↦ f ω j))
    (j : ℕ) : Measurable (fun ω ↦ gramSchmidtNormed ℝ (f ω) j) := by
  have hg := measurable_gramSchmidt f hf j
  change Measurable (fun ω ↦ ‖gramSchmidt ℝ (f ω) j‖⁻¹ • gramSchmidt ℝ (f ω) j)
  exact hg.norm.inv.smul hg

lemma gramSchmidtNormed_unitOrZero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E) (j : ℕ) :
    gramSchmidtNormed ℝ f j=0 ∨ ⟪gramSchmidtNormed ℝ f j,gramSchmidtNormed ℝ f j⟫=1 := by
  by_cases h : gramSchmidtNormed ℝ f j=0
  · exact Or.inl h
  · right
    rw [real_inner_self_eq_norm_sq,gramSchmidtNormed_unit_length' h]
    norm_num

lemma gramSchmidtNormed_pairwise_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E) {i j : ℕ} (hij : i≠j) :
    ⟪gramSchmidtNormed ℝ f i,gramSchmidtNormed ℝ f j⟫=0 := by
  simp only [gramSchmidtNormed,real_inner_smul_left,real_inner_smul_right,
    gramSchmidt_orthogonal ℝ f hij,mul_zero]

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RandomColumn
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {Ω ι κ ν : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
  [Fintype κ] [Fintype ν] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma integrable_randomMaximum [IsProbabilityMeasure μ] {f : Ω → ι → ℝ}
    (hf : ∀ i,Integrable (fun ω ↦ f ω i) μ) :
    Integrable (fun ω ↦ finiteMaximum (f ω)) μ := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (hf i).abs)).mono'
    (continuous_finiteMaximum.comp_aestronglyMeasurable
      ((integrable_pi_iff.mpr hf).aestronglyMeasurable))
  exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using abs_finiteMaximum_le (f ω))

omit [Fintype ι] [Nonempty ι] in
lemma random_linear_integrable [Fintype ι] [Nonempty ι] (a : Ω → ι → ν → ℝ)
    (ha : ∀ i k,Measurable (fun ω ↦ a ω i k)) (C : ℝ)
    (hC : ∀ ω i k,|a ω i k|≤C) (i : ι) :
    Integrable (fun p : Ω×(ν → ℝ) ↦ linearProcess (a p.1) p.2 i)
      (μ.prod (gaussianProduct ν)) := by
  unfold linearProcess
  apply integrable_finsetSum
  intro k _
  apply ((gaussian_coordinate_integrable k).abs.const_mul C |>.comp_snd μ).mono'
    (((ha i k).comp measurable_fst).mul ((measurable_pi_apply k).comp measurable_snd)).aestronglyMeasurable
  exact Eventually.of_forall (fun p ↦ by
    change |a p.1 i k * p.2 k| ≤ C * |p.2 k|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hC p.1 i k) (abs_nonneg _))

lemma random_quadratic_integrable (w : Ω → ι → EuclideanSpace ℝ κ) (d : Ω → ι → ℝ)
    (hw : ∀ i,Measurable (fun ω ↦ w ω i)) (hd : ∀ i,Integrable (fun ω ↦ d ω i) μ)
    (R : ℝ) (hR : ∀ ω i,‖w ω i‖≤R) :
    Integrable (fun ω ↦ quadraticValue (w ω) (d ω)) μ := by
  have hi : Integrable (fun p : Ω×((κ×κ) → ℝ) ↦
      finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w p.1 i)) p.2 i+d p.1 i))
      (μ.prod (gaussianProduct (κ×κ))) := by
    apply integrable_randomMaximum
    intro i
    apply Integrable.add _ ((hd i).comp_fst _)
    apply random_linear_integrable (fun ω i ↦ quadraticCoeff (w ω i)) _ (R^2) _ i
    · intro i k; unfold quadraticCoeff; fun_prop
    · intro ω i k
      exact (quadraticCoeff_coord_bound _ _).trans (sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) (hR ω i)) |>.mpr (hR ω i))
  exact hi.integral_prod_left

lemma columnVector_coord_bound {v : EuclideanSpace ℝ κ} (hv : v=0 ∨ ⟪v,v⟫=1)
    (w : EuclideanSpace ℝ κ) (k : κ) : |columnVector v w k|≤‖w‖^2 :=
  (PiLp.norm_apply_le _ k).trans (columnVector_norm_le hv w)

theorem random_column_identity (w : Ω → ι → EuclideanSpace ℝ κ) (d : Ω → ι → ℝ)
    (v : Ω → EuclideanSpace ℝ κ) (hw : ∀ i,Measurable (fun ω ↦ w ω i))
    (_hdm : ∀ i,Measurable (fun ω ↦ d ω i))
    (hd : ∀ i,Integrable (fun ω ↦ d ω i) μ) (hv : Measurable v)
    (hu : ∀ ω,v ω=0 ∨ ⟪v ω,v ω⟫=1) (R : ℝ) (hR : ∀ ω i,‖w ω i‖≤R) :
    (∫ ω,quadraticValue (w ω) (d ω) ∂μ)=
      ∫ p : Ω×(κ → ℝ),quadraticValue (fun i ↦ columnResidual (v p.1) (w p.1 i))
        (fun i ↦ d p.1 i+linearProcess (fun i k ↦ columnVector (v p.1) (w p.1 i) k) p.2 i)
        ∂μ.prod (gaussianProduct κ) := by
  have hw' (i : ι) : Measurable (fun p : Ω×(κ → ℝ) ↦ columnResidual (v p.1) (w p.1 i)) :=
    measurable_columnResidual (hv.comp measurable_fst) ((hw i).comp measurable_fst)
  have hd' (i : ι) : Integrable (fun p : Ω×(κ → ℝ) ↦
      d p.1 i+linearProcess (fun i k ↦ columnVector (v p.1) (w p.1 i) k) p.2 i)
      (μ.prod (gaussianProduct κ)) := by
    apply ((hd i).comp_fst _).add
    apply random_linear_integrable (fun ω i k ↦ columnVector (v ω) (w ω i) k) _ (R^2) _ i
    · intro i k
      exact (PiLp.continuous_apply 2 (fun _ : κ ↦ ℝ) k).measurable.comp (measurable_columnVector hv (hw i))
    · intro ω i k
      exact (columnVector_coord_bound (hu ω) _ _).trans
        ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hR ω i))).mpr (hR ω i))
  have hi := random_quadratic_integrable _ _ hw' hd' R
    (fun p i ↦ (columnResidual_norm_le (hu p.1) (w p.1 i)).trans (hR p.1 i))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω ↦ quadraticValue_column (w ω) (d ω) (v ω) (hu ω))

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable (κ : Type*) [Fintype κ]

omit [Fintype κ] in
lemma historySplit_apply [Fintype κ] (j : ℕ) (h : ColumnHistory κ (j+1)) :
    historySplit κ j h=(historyInit κ h,h (Fin.last j)) := by
  simp [historySplit,MeasurableEquiv.piFinSuccAbove,Fin.insertNthEquiv]
  rfl

lemma historySplit_preserving (j : ℕ) :
    MeasurePreserving (historySplit κ j) (columnHistoryLaw κ (j+1))
      ((columnHistoryLaw κ j).prod (gaussianProduct κ)) := by
  exact (Measure.measurePreserving_swap).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (j+1) ↦ gaussianProduct κ) (Fin.last j))

omit [Fintype κ] in
lemma historyInit_measurable [Fintype κ] (j : ℕ) : Measurable (historyInit κ (j:=j)) := by
  unfold historyInit; fun_prop

lemma history_integral_succ (j : ℕ) (f : ColumnHistory κ j × (κ → ℝ) → ℝ) :
    (∫ h,f (historyInit κ h,h (Fin.last j)) ∂columnHistoryLaw κ (j+1))=
      ∫ p,f p ∂(columnHistoryLaw κ j).prod (gaussianProduct κ) := by
  simpa only [historySplit_apply] using (historySplit_preserving κ j).integral_comp' f

lemma history_integrable_succ (j : ℕ) {f : ColumnHistory κ j × (κ → ℝ) → ℝ}
    (hf : Integrable f ((columnHistoryLaw κ j).prod (gaussianProduct κ))) :
    Integrable (fun h ↦ f (historyInit κ h,h (Fin.last j))) (columnHistoryLaw κ (j+1)) := by
  simpa only [Function.comp_def,historySplit_apply] using (historySplit_preserving κ j).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_AdaptiveColumns
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

variable (w : ι → EuclideanSpace ℝ κ)
  (v : (j : ℕ) → ColumnHistory κ j → EuclideanSpace ℝ κ)
  (hv : ∀ j,Measurable (v j)) (hu : ∀ j h,v j h=0 ∨ ⟪v j h,v j h⟫=1)

include hv in
omit [Fintype ι] [Nonempty ι] in
lemma adaptiveResidual_measurable [Fintype ι] [Nonempty ι] (j : ℕ) (i : ι) :
    Measurable (fun h ↦ adaptiveResidual w v j h i) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    exact measurable_columnResidual ((hv j).comp (historyInit_measurable κ j))
      (ih.comp (historyInit_measurable κ j))

include hu in
omit [Fintype ι] [Nonempty ι] in
lemma adaptiveResidual_bound [Fintype ι] [Nonempty ι] (R : ℝ) (hR : ∀ i,‖w i‖≤R) (j : ℕ)
    (h : ColumnHistory κ j) (i : ι) : ‖adaptiveResidual w v j h i‖≤R := by
  induction j with
  | zero => exact hR i
  | succ j ih =>
    exact (columnResidual_norm_le (hu j _) _).trans (ih _)

include hv in
lemma adaptiveOffset_measurable (j : ℕ) (i : ι) :
    Measurable (fun h ↦ adaptiveOffset w v j h i) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    unfold adaptiveOffset
    apply (ih.comp (historyInit_measurable κ j)).add
    unfold linearProcess
    apply Finset.measurable_sum
    intro k _
    apply Measurable.mul _ (by fun_prop)
    exact (PiLp.continuous_apply 2 (fun _ : κ ↦ ℝ) k).measurable.comp
      (measurable_columnVector ((hv j).comp (historyInit_measurable κ j))
        ((adaptiveResidual_measurable w v hv j i).comp (historyInit_measurable κ j)))

include hv hu in
lemma adaptiveOffset_integrable (R : ℝ) (hR : ∀ i,‖w i‖≤R) (j : ℕ) (i : ι) :
    Integrable (fun h ↦ adaptiveOffset w v j h i) (columnHistoryLaw κ j) := by
  induction j with
  | zero => exact integrable_const 0
  | succ j ih =>
    change Integrable (fun h ↦ adaptiveOffset w v j (historyInit κ h) i+
      linearProcess (fun i k ↦ columnVector (v j (historyInit κ h))
        (adaptiveResidual w v j (historyInit κ h) i) k) (h (Fin.last j)) i) _
    exact history_integrable_succ κ j (f:=fun p ↦ adaptiveOffset w v j p.1 i+
      linearProcess (fun i k ↦ columnVector (v j p.1) (adaptiveResidual w v j p.1 i) k) p.2 i) (by
    apply (ih.comp_fst _).add
    apply random_linear_integrable (fun h i k ↦ columnVector (v j h) (adaptiveResidual w v j h i) k)
      _ (R^2) _ i
    · intro i k
      exact (PiLp.continuous_apply 2 (fun _ : κ ↦ ℝ) k).measurable.comp
        (measurable_columnVector (hv j) (adaptiveResidual_measurable w v hv j i))
    · intro h i k
      exact (columnVector_coord_bound (hu j h) _ k).trans
        ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans
          (adaptiveResidual_bound w v hu R hR j h i))).mpr
            (adaptiveResidual_bound w v hu R hR j h i)))

include hv hu in

theorem adaptive_value_identity (R : ℝ) (hR : ∀ i,‖w i‖≤R) (K : ℕ) :
    quadraticValue w (fun _ ↦ 0)=
      ∫ h,quadraticValue (adaptiveResidual w v K h) (adaptiveOffset w v K h)
        ∂columnHistoryLaw κ K := by
  induction K with
  | zero => simp [adaptiveResidual,adaptiveOffset]
  | succ K ih =>
    rw [ih]
    change _ = ∫ h,quadraticValue
      (fun i ↦ columnResidual (v K (historyInit κ h))
        (adaptiveResidual w v K (historyInit κ h) i))
      (fun i ↦ adaptiveOffset w v K (historyInit κ h) i+
        linearProcess (fun i k ↦ columnVector (v K (historyInit κ h))
          (adaptiveResidual w v K (historyInit κ h) i) k) (h (Fin.last K)) i)
      ∂columnHistoryLaw κ (K+1)
    rw [history_integral_succ κ K (fun p ↦ quadraticValue
      (fun i ↦ columnResidual (v K p.1) (adaptiveResidual w v K p.1 i))
      (fun i ↦ adaptiveOffset w v K p.1 i+
        linearProcess (fun i k ↦ columnVector (v K p.1)
          (adaptiveResidual w v K p.1 i) k) p.2 i))]
    exact random_column_identity _ _ _ (adaptiveResidual_measurable w v hv K)
      (adaptiveOffset_measurable w v hv K) (adaptiveOffset_integrable w v hv hu R hR K)
      (hv K) (hu K) R (adaptiveResidual_bound w v hu R hR K)

include hv hu in

theorem adaptive_spin_lower (R : ℝ) (hR : ∀ i,‖w i‖≤R) (K : ℕ)
    (s : ColumnHistory κ K → ι)
    (hs : Measurable (fun h ↦ adaptiveOffset w v K h (s h))) :
    (∫ h,adaptiveOffset w v K h (s h) ∂columnHistoryLaw κ K)≤
      quadraticValue w (fun _ ↦ 0) := by
  have hd := adaptiveOffset_integrable w v hv hu R hR K
  have hi : Integrable (fun h ↦ adaptiveOffset w v K h (s h)) (columnHistoryLaw κ K) := by
    apply (integrable_finsetSum Finset.univ (fun i _ ↦ (hd i).abs)).mono' hs.aestronglyMeasurable
    exact Eventually.of_forall (fun h ↦ by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (adaptiveOffset w v K h i)) (Finset.mem_univ (s h)))
  rw [adaptive_value_identity w v hv hu R hR K]
  apply integral_mono hi
    (random_quadratic_integrable _ _ (adaptiveResidual_measurable w v hv K) hd R
      (adaptiveResidual_bound w v hu R hR K))
  intro h
  exact quadraticValue_ge_offset _ _ (s h)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalVectors
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {Ω : Type*}

lemma empiricalVector_inner (f g : Ω → ℝ) (x : ℕ → Ω) (n : ℕ) :
    ⟪empiricalVector f x n,empiricalVector g x n⟫=
      (∑ i∈Finset.range n,f (x i)*g (x i))/(n : ℝ) := by
  rw [empiricalVector,empiricalVector,real_inner_smul_left,real_inner_smul_right,
    euclidean_inner_sum]
  change (Real.sqrt (n : ℝ))⁻¹*((Real.sqrt (n : ℝ))⁻¹*
    ∑ i : Fin n,f (x i)*g (x i)) = _
  rw [←Fin.sum_univ_eq_sum_range]
  have hs : Real.sqrt (n : ℝ)^2=(n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  calc
    _ = (∑ i : Fin n,f (x i)*g (x i))/(Real.sqrt (n : ℝ))^2 := by ring
    _ = _ := by rw [hs]

variable [MeasurableSpace Ω]

lemma iid_sample_law (μ : Measure Ω) [IsProbabilityMeasure μ] (i : ℕ) :
    HasLaw (fun x : ℕ → Ω ↦ x i) μ (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).hasLaw

lemma iid_prefix_law (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    HasLaw (fun x : ℕ → Ω ↦ fun i : Fin n ↦ x i) (Measure.pi (fun _ : Fin n ↦ μ))
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  apply iIndepFun.hasLaw_pi (fun i : Fin n ↦ iid_sample_law μ i.val)
  exact (iIndepFun_infinitePi (P:=fun _ : ℕ ↦ μ) (X:=fun _ x ↦ x)
    (fun _ ↦ measurable_id)).precomp Fin.val_injective

lemma iid_average_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hm : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun n ↦ (∑ i∈Finset.range n,f (x i))/(n : ℝ)) atTop (𝓝 (∫ y,f y ∂μ)) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → Ω) ↦ f (x i)
  have hl (i : ℕ) : HasLaw (X i) (Measure.map f μ) P := (show HasLaw f (Measure.map f μ) μ from ⟨hm.aemeasurable,rfl⟩).comp (iid_sample_law μ i)
  have hind : iIndepFun X P := iIndepFun_infinitePi (fun _ ↦ hm)
  have hi' : Integrable (X 0) P :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).integrable_comp_of_integrable hi
  have he : (∫ x,X 0 x ∂P)=∫ y,f y ∂μ := (iid_sample_law μ 0).integral_comp hi.aestronglyMeasurable
  simpa only [X,he] using strong_law_ae_real X hi'
    (fun i j hij ↦ hind.indepFun hij) (fun i ↦ (hl i).identDistrib (hl 0))

lemma empirical_inner_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hm : Measurable (fun x ↦ f x*g x))
    (hi : Integrable (fun x ↦ f x*g x) μ) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun n ↦ ⟪empiricalVector f x n,empiricalVector g x n⟫) atTop
        (𝓝 (∫ y,f y*g y ∂μ)) := by
  simpa only [empiricalVector_inner] using iid_average_tendsto μ (fun x ↦ f x*g x) hm hi

lemma empirical_norm_tendsto_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hm : Measurable f) (hi : Integrable (fun x ↦ (f x)^2) μ)
    (he : (∫ x,(f x)^2 ∂μ)=1) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun n ↦ ‖empiricalVector f x n‖) atTop (𝓝 1) := by
  have hi' : Integrable (fun x ↦ f x*f x) μ := by simpa only [sq] using hi
  filter_upwards [empirical_inner_tendsto μ f f (hm.mul hm) hi'] with x hx
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hx
  simp only [←sq,he,Real.sqrt_one] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [Function.comp_apply,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma gramSchmidt_congr_prefix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : ℕ → E) (j : ℕ) (h : ∀ i≤j,f i=g i) :
    gramSchmidt ℝ f j=gramSchmidt ℝ g j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rw [gramSchmidt_eq_sub_sum_nat,gramSchmidt_eq_sub_sum_nat,h j le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij := Finset.mem_range.mp hi
    rw [ih i hij (fun l hl ↦ h l (by omega))]

lemma gramSchmidtNormed_congr_prefix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : ℕ → E) (j : ℕ) (h : ∀ i≤j,f i=g i) :
    gramSchmidtNormed ℝ f j=gramSchmidtNormed ℝ g j := by
  simp only [gramSchmidtNormed,gramSchmidt_congr_prefix f g j h]

variable (K n : ℕ)

lemma paddedRow_measurable (j : ℕ) (i : Fin n) :
    Measurable (fun h : ColumnHistory (Fin n) j ↦ paddedRow K n h i) := by
  unfold paddedRow
  apply Measurable.of_eval
  intro l
  split_ifs <;> fun_prop

lemma rawHistory_measurable (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (hf : ∀ l,Measurable (f l)) (j l : ℕ) :
    Measurable (fun h : ColumnHistory (Fin n) j ↦ rawHistory K n f h l) := by
  have hm : Measurable (fun h : ColumnHistory (Fin n) j ↦
      WithLp.toLp 2 (fun i : Fin n ↦ f l (paddedRow K n h i))) := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply Measurable.of_eval
    intro i
    exact (hf l).comp (paddedRow_measurable K n j i)
  exact hm.const_smul (Real.sqrt (n : ℝ))⁻¹

lemma predictableDirection_measurable (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (hf : ∀ l,Measurable (f l)) (j : ℕ) : Measurable (predictableDirection K n f j) := by
  cases j with
  | zero => exact measurable_const
  | succ j => exact measurable_gramSchmidtNormed _ (rawHistory_measurable K n f hf (j+1)) j

lemma predictableDirection_unitOrZero (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (j : ℕ) (h : ColumnHistory (Fin n) j) :
    predictableDirection K n f j h=0 ∨
      ⟪predictableDirection K n f j h,predictableDirection K n f j h⟫=1 := by
  cases j with
  | zero => exact Or.inl rfl
  | succ j => exact gramSchmidtNormed_unitOrZero _ _

lemma rawHistory_rows (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (x : Fin n → Fin (K+1) → ℝ) (j l : ℕ) (hl : l<j) :
    rawHistory K n f (rowHistory K n x j) l=
      (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i ↦ f l (x i)) := by
  unfold rawHistory
  congr 1
  congr 1
  funext i
  apply ha
  intro k hk
  simp only [paddedRow,rowHistory,rowColumn]
  rw [dite_eq_left (show k.val<j by omega),dite_eq_left k.isLt]

lemma predictableDirection_rows (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (x : ℕ → (Fin (K+1) → ℝ)) (j : ℕ) :
    predictableDirection K n f (j+1) (rowHistory K n (fun i ↦ x i) (j+1))=
      gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j := by
  apply gramSchmidtNormed_congr_prefix
  intro l hl
  exact rawHistory_rows K n f ha _ _ _ (by omega)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GramSchmidtLimit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Set InnerProductSpace
open scoped Topology BigOperators RealInnerProductSpace
namespace SKValueG
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

lemma inner_approx_tendsto {x x' y : (n : ℕ) → E n} {a b : ℝ}
    (hx : Tendsto (fun n ↦ ‖x n-x' n‖) atTop (𝓝 0))
    (hy : Tendsto (fun n ↦ ‖y n‖) atTop (𝓝 b))
    (hxy : Tendsto (fun n ↦ ⟪x' n,y n⟫) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ⟪x n,y n⟫) atTop (𝓝 a) := by
  have hdiff : Tendsto (fun n ↦ ⟪x n,y n⟫-⟪x' n,y n⟫) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) (by simpa using hx.mul hy)
    rw [←inner_sub_left,Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  simpa only [sub_add_cancel,zero_add] using hdiff.add hxy

omit [∀ n, InnerProductSpace ℝ (E n)] in
lemma norm_approx_tendsto {x x' : (n : ℕ) → E n} {a : ℝ}
    (hx : Tendsto (fun n ↦ ‖x n-x' n‖) atTop (𝓝 0))
    (hx' : Tendsto (fun n ↦ ‖x' n‖) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 a) := by
  have hd : Tendsto (fun n ↦ ‖x n‖-‖x' n‖) atTop (𝓝 0) := by
    exact squeeze_zero_norm (fun n ↦ by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (x n) (x' n)) hx
  simpa only [sub_add_cancel,zero_add] using hd.add hx'

theorem gramSchmidt_approx (a : (n : ℕ) → ℕ → E n) (K : ℕ)
    (hn : ∀ i≤K,Tendsto (fun n ↦ ‖a n i‖) atTop (𝓝 1))
    (hi : ∀ i j,i<j → j≤K → Tendsto (fun n ↦ ⟪a n i,a n j⟫) atTop (𝓝 0))
    (j : ℕ) (hj : j≤K) :
    Tendsto (fun n ↦ ‖gramSchmidt ℝ (a n) j-a n j‖) atTop (𝓝 0) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hnorm (i : ℕ) (hij : i<j) :
        Tendsto (fun n ↦ ‖gramSchmidt ℝ (a n) i‖) atTop (𝓝 1) :=
      norm_approx_tendsto (ih i hij (hij.le.trans hj)) (hn i (hij.le.trans hj))
    have hinner (i : ℕ) (hij : i<j) :
        Tendsto (fun n ↦ ⟪gramSchmidt ℝ (a n) i,a n j⟫) atTop (𝓝 0) :=
      inner_approx_tendsto (ih i hij (hij.le.trans hj)) (hn j hj) (hi i j hij hj)
    have hterm (i : ℕ) (hij : i<j) :
        Tendsto (fun n ↦ ‖(⟪gramSchmidt ℝ (a n) i,a n j⟫ /
          ‖gramSchmidt ℝ (a n) i‖^2) • gramSchmidt ℝ (a n) i‖) atTop (𝓝 0) := by
      simp only [norm_smul,Real.norm_eq_abs]
      have h := ((hinner i hij).div ((hnorm i hij).pow 2) (by norm_num)).abs.mul (hnorm i hij)
      simpa using h
    have hs : Tendsto (fun n ↦ ∑ i∈Finset.range j,
        ‖(⟪gramSchmidt ℝ (a n) i,a n j⟫/‖gramSchmidt ℝ (a n) i‖^2) •
          gramSchmidt ℝ (a n) i‖) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range j)
        (fun i hi ↦ hterm i (Finset.mem_range.mp hi))
    apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hs
    have he := gramSchmidt_def'' ℝ (a n) j
    have he' : gramSchmidt ℝ (a n) j-a n j =
        -(∑ i∈Finset.range j,(⟪gramSchmidt ℝ (a n) i,a n j⟫ /
          ‖gramSchmidt ℝ (a n) i‖^2) • gramSchmidt ℝ (a n) i) := by
      simp only [Nat.Iio_eq_range] at he
      calc
        _ = gramSchmidt ℝ (a n) j-(gramSchmidt ℝ (a n) j+_) := congrArg (fun x ↦ gramSchmidt ℝ (a n) j-x) he
        _ = _ := by abel
    rw [he',norm_neg]
    exact norm_sum_le _ _

theorem gramSchmidtNormed_approx (a : (n : ℕ) → ℕ → E n) (K : ℕ)
    (hn : ∀ i≤K,Tendsto (fun n ↦ ‖a n i‖) atTop (𝓝 1))
    (hi : ∀ i j,i<j → j≤K → Tendsto (fun n ↦ ⟪a n i,a n j⟫) atTop (𝓝 0))
    (j : ℕ) (hj : j≤K) :
    Tendsto (fun n ↦ ‖gramSchmidtNormed ℝ (a n) j-a n j‖) atTop (𝓝 0) := by
  have hg := gramSchmidt_approx a K hn hi j hj
  have hgn := norm_approx_tendsto hg (hn j hj)
  have hscale : Tendsto (fun n ↦ |‖gramSchmidt ℝ (a n) j‖⁻¹-1| *
      ‖gramSchmidt ℝ (a n) j‖) atTop (𝓝 0) := by
    simpa using ((hgn.inv₀ (by norm_num)).sub_const 1).abs.mul hgn
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (by simpa using hscale.add hg)
  calc
    _ ≤ ‖gramSchmidtNormed ℝ (a n) j-gramSchmidt ℝ (a n) j‖+
        ‖gramSchmidt ℝ (a n) j-a n j‖ := by
      calc
        _ = ‖(gramSchmidtNormed ℝ (a n) j-gramSchmidt ℝ (a n) j)+(gramSchmidt ℝ (a n) j-a n j)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    _ = _ := by
      congr 1
      change ‖‖gramSchmidt ℝ (a n) j‖⁻¹ • gramSchmidt ℝ (a n) j-gramSchmidt ℝ (a n) j‖ = _
      have he : ‖gramSchmidt ℝ (a n) j‖⁻¹ • gramSchmidt ℝ (a n) j-gramSchmidt ℝ (a n) j =
          (‖gramSchmidt ℝ (a n) j‖⁻¹-1) • gramSchmidt ℝ (a n) j := by rw [sub_smul,one_smul]
      rw [he,norm_smul,Real.norm_eq_abs]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_orthogonalRemainder (v : ℕ → E) (w : E) (j : ℕ)
    (ho : ∀ i<j,⟪v j,v i⟫=0) :
    ⟪v j,orthogonalRemainder v w j⟫=⟪v j,w⟫ := by
  simp only [orthogonalRemainder,inner_sub_right,inner_sum,real_inner_smul_right]
  have hz : (∑ i∈Finset.range j,⟪v i,w⟫*⟪v j,v i⟫)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [ho i (Finset.mem_range.mp hi)]
  rw [hz,sub_zero]

lemma orthogonalRemainder_succ (v : ℕ → E) (w : E) (j : ℕ) :
    orthogonalRemainder v w (j+1)=orthogonalRemainder v w j-⟪v j,w⟫ • v j := by
  simp only [orthogonalRemainder,Finset.sum_range_succ]
  abel

lemma columnResidual_orthogonalRemainder {κ : Type*} [Fintype κ]
    (v : ℕ → EuclideanSpace ℝ κ) (w : EuclideanSpace ℝ κ) (j : ℕ)
    (ho : ∀ i<j,⟪v j,v i⟫=0) :
    columnResidual (v j) (orthogonalRemainder v w j)=orthogonalRemainder v w (j+1) := by
  rw [columnResidual,inner_orthogonalRemainder v w j ho,orthogonalRemainder_succ]

lemma column_revealed_energy {κ : Type*} [Fintype κ]
    (v : ℕ → EuclideanSpace ℝ κ) (w z : EuclideanSpace ℝ κ) (j : ℕ)
    (ho : ∀ i<j,⟪v j,v i⟫=0) :
    ⟪columnVector (v j) (orthogonalRemainder v w j),z⟫=
      ⟪v j,w⟫*⟪orthogonalRemainder v w (j+1),z⟫+
      (⟪v j,w⟫^2/Real.sqrt 2)*⟪v j,z⟫ := by
  simp only [columnVector,inner_add_left,real_inner_smul_left]
  rw [inner_orthogonalRemainder v w j ho,columnResidual_orthogonalRemainder v w j ho]

section Limit
variable {E' : ℕ → Type*} [∀ n,NormedAddCommGroup (E' n)] [∀ n,InnerProductSpace ℝ (E' n)]

lemma orthogonalRemainder_inner_tendsto (v : (n : ℕ) → ℕ → E' n)
    (w z : (n : ℕ) → E' n) (K : ℕ) (A : ℕ → ℝ) (B : ℝ)
    (ha : ∀ j<K,Tendsto (fun n ↦ ⟪v n j,w n⟫) atTop (𝓝 (A j)))
    (hz : ∀ j<K,Tendsto (fun n ↦ ⟪v n j,z n⟫) atTop (𝓝 0))
    (hwz : Tendsto (fun n ↦ ⟪w n,z n⟫) atTop (𝓝 B)) :
    Tendsto (fun n ↦ ⟪orthogonalRemainder (v n) (w n) K,z n⟫) atTop (𝓝 B) := by
  have hs : Tendsto (fun n ↦ ∑ j∈Finset.range K,⟪v n j,w n⟫*⟪v n j,z n⟫) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (s:=Finset.range K)
      (fun j hj ↦ (ha j (Finset.mem_range.mp hj)).mul (hz j (Finset.mem_range.mp hj)))
    simpa using hh
  have ht := hwz.sub hs
  simpa only [orthogonalRemainder,inner_sub_left,sum_inner,real_inner_smul_left,sub_zero] using ht

theorem normalized_column_energy_tendsto (a : (n : ℕ) → ℕ → E' n)
    (w z : (n : ℕ) → E' n) (K : ℕ) (A : ℕ → ℝ) (B : ℝ)
    (hn : ∀ i≤K,Tendsto (fun n ↦ ‖a n i‖) atTop (𝓝 1))
    (hi : ∀ i j,i<j → j≤K → Tendsto (fun n ↦ ⟪a n i,a n j⟫) atTop (𝓝 0))
    (hwn : Tendsto (fun n ↦ ‖w n‖) atTop (𝓝 1))
    (hzn : Tendsto (fun n ↦ ‖z n‖) atTop (𝓝 1))
    (ha : ∀ j≤K,Tendsto (fun n ↦ ⟪a n j,w n⟫) atTop (𝓝 (A j)))
    (hz : ∀ j≤K,Tendsto (fun n ↦ ⟪a n j,z n⟫) atTop (𝓝 0))
    (hb : Tendsto (fun n ↦ ⟪w n,z n⟫) atTop (𝓝 B)) :
    Tendsto (fun n ↦
      ⟪gramSchmidtNormed ℝ (a n) K,w n⟫*
        ⟪orthogonalRemainder (gramSchmidtNormed ℝ (a n)) (w n) (K+1),z n⟫+
      (⟪gramSchmidtNormed ℝ (a n) K,w n⟫^2/Real.sqrt 2)*
        ⟪gramSchmidtNormed ℝ (a n) K,z n⟫) atTop (𝓝 (A K*B)) := by
  have hp (j : ℕ) (hj : j≤K) :
      Tendsto (fun n ↦ ‖gramSchmidtNormed ℝ (a n) j-a n j‖) atTop (𝓝 0) :=
    gramSchmidtNormed_approx a j (fun i h ↦ hn i (h.trans hj))
      (fun i l hil hl ↦ hi i l hil (hl.trans hj)) j le_rfl
  have ha' (j : ℕ) (hj : j≤K) := inner_approx_tendsto (hp j hj) hwn (ha j hj)
  have hz' (j : ℕ) (hj : j≤K) := inner_approx_tendsto (hp j hj) hzn (hz j hj)
  have hr := orthogonalRemainder_inner_tendsto (fun n ↦ gramSchmidtNormed ℝ (a n)) w z
    (K+1) A B (fun j hj ↦ ha' j (by omega)) (fun j hj ↦ hz' j (by omega)) hb
  simpa only [mul_zero,add_zero] using
    ((ha' K le_rfl).mul hr).add (((ha' K le_rfl).pow 2 |>.div_const _).mul (hz' K le_rfl))
end Limit
end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_QuadraticSK
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma spinVector_inner (n : ℕ) (s t : Fin n → Bool) :
    ⟪spinVector n s,spinVector n t⟫=∑ i,spin (s i)*spin (t i) := euclidean_inner_sum _ _

lemma spinVector_sqNorm (n : ℕ) (s : Fin n → Bool) : ‖spinVector n s‖^2=(n : ℝ) := by
  rw [←real_inner_self_eq_norm_sq,spinVector_inner]
  simp only [←sq,spin_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma spinVector_norm (n : ℕ) (s : Fin n → Bool) : ‖spinVector n s‖=Real.sqrt (n : ℝ) := by
  rw [←spinVector_sqNorm n s,Real.sqrt_sq (norm_nonneg _)]

lemma finiteMaximum_mul_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    finiteMaximum (fun i ↦ c*f i)=c*finiteMaximum f := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum f
  apply le_antisymm
  · obtain ⟨j,hj⟩ := exists_finiteMaximum (fun i ↦ c*f i)
    rw [←hj]
    exact mul_le_mul_of_nonneg_left (le_finiteMaximum f j) hc
  · rw [←hi]
    exact le_finiteMaximum (fun i ↦ c*f i) i

lemma scaled_linearProcess {ι κ : Type*} [Fintype κ] (a : ι → κ → ℝ) (c : ℝ)
    (z : κ → ℝ) (i : ι) : linearProcess (fun i k ↦ c*a i k) z i=c*linearProcess a z i := by
  simp only [linearProcess,Finset.mul_sum,mul_assoc]

lemma quadratic_spin_distance {n : ℕ} (hn : 0<n) (s t : Fin n → Bool) :
    (∑ k,(quadraticCoeff (spinVector n s) k-quadraticCoeff (spinVector n t) k)^2)=
      ∑ k,(Real.sqrt (n : ℝ)*hamCoeff n s k-Real.sqrt (n : ℝ)*hamCoeff n t k)^2 := by
  have hs0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have hq (s : Fin n → Bool) :
      (∑ k,(quadraticCoeff (spinVector n s) k)^2)=(n : ℝ)^2/2 := by
    simp only [sq]
    rw [quadraticCoeff_inner,real_inner_self_eq_norm_sq,spinVector_sqNorm]
    ring
  rw [sq_distance_sum,hq,hq,quadraticCoeff_inner,spinVector_inner]
  have hs : (∑ k,(Real.sqrt (n : ℝ)*hamCoeff n s k-Real.sqrt (n : ℝ)*hamCoeff n t k)^2)=
      (n : ℝ)*(∑ k,(hamCoeff n s k-hamCoeff n t k)^2) := by
    simp only [←mul_sub,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Finset.mul_sum]
  rw [hs,hamCoeff_distance hn]
  field_simp
  ring

theorem quadraticValue_spin {n : ℕ} (hn : 0<n) :
    quadraticValue (spinVector n) (fun _ ↦ 0)=Real.sqrt (n : ℝ)*expectedMaximum n := by
  have he : (∫ z,finiteMaximum (fun s ↦ linearProcess (fun s ↦ quadraticCoeff (spinVector n s)) z s+0)
      ∂gaussianProduct (Fin n×Fin n))=
      ∫ z,finiteMaximum (fun s ↦ linearProcess (fun s k ↦ Real.sqrt (n : ℝ)*hamCoeff n s k) z s+0)
      ∂gaussianProduct (Fin n×Fin n) := by
    apply le_antisymm
    · exact expected_affine_max_le _ _ (fun _ ↦ 0) (fun s t ↦ (quadratic_spin_distance hn s t).le)
    · exact expected_affine_max_le _ _ (fun _ ↦ 0) (fun s t ↦ (quadratic_spin_distance hn s t).ge)
  unfold quadraticValue
  rw [he]
  simp only [add_zero,scaled_linearProcess,finiteMaximum_mul_nonneg _ (Real.sqrt_nonneg _)]
  rw [integral_const_mul]
  rfl

theorem finite_adaptive_SK_lower {n : ℕ} (hn : 0<n)
    (v : (j : ℕ) → ColumnHistory (Fin n) j → EuclideanSpace ℝ (Fin n))
    (hv : ∀ j,Measurable (v j)) (hu : ∀ j h,v j h=0 ∨ ⟪v j h,v j h⟫=1)
    (K : ℕ) (s : ColumnHistory (Fin n) K → (Fin n → Bool))
    (hs : Measurable (fun h ↦ adaptiveOffset (spinVector n) v K h (s h))) :
    (∫ h,adaptiveOffset (spinVector n) v K h (s h) ∂columnHistoryLaw (Fin n) K)/
      ((n : ℝ)*Real.sqrt (n : ℝ))≤groundStateSequence n := by
  have hh := adaptive_spin_lower (spinVector n) v hv hu (Real.sqrt (n : ℝ))
    (fun s ↦ (spinVector_norm n s).le) K s hs
  rw [quadraticValue_spin hn] at hh
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  have pro : (0 : ℝ)<(n : ℝ)*Real.sqrt (n : ℝ) := mul_pos hn' (Real.sqrt_pos.mpr hn')
  apply (div_le_div_of_nonneg_right hh pro.le).trans_eq
  rw [groundStateSequence_eq]
  field_simp

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma orthogonalRemainder_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (w : E) (j : ℕ) (c : ℝ) :
    orthogonalRemainder v (c • w) j=c • orthogonalRemainder v w j := by
  simp only [orthogonalRemainder,smul_sub,Finset.smul_sum,real_inner_smul_right,smul_smul]

lemma columnVector_smul {κ : Type*} [Fintype κ]
    (v w : EuclideanSpace ℝ κ) (c : ℝ) : columnVector v (c • w)=c^2 • columnVector v w := by
  simp only [columnVector,columnResidual,real_inner_smul_right,smul_sub,smul_add,smul_smul]
  module

lemma empiricalVector_scale {Ω : Type*} (f : Ω → ℝ) (x : ℕ → Ω) {n : ℕ} (hn : 0<n) :
    Real.sqrt (n : ℝ) • empiricalVector f x n=WithLp.toLp 2 (fun i : Fin n ↦ f (x i)) := by
  rw [empiricalVector,smul_smul,mul_inv_cancel₀,one_smul]
  exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)

variable (K n : ℕ) (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
  (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
  (x : ℕ → (Fin (K+1) → ℝ))

include ha in
lemma predictableResidual_rows {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin n)) (j : ℕ) (s : ι) :
    adaptiveResidual w (predictableDirection K n f) (j+1)
      (rowHistory K n (fun i ↦ x i) (j+1)) s=
    orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n)) (w s) j := by
  induction j with
  | zero => simp [adaptiveResidual,predictableDirection,columnResidual,orthogonalRemainder]
  | succ j ih =>
    change columnResidual (predictableDirection K n f (j+1)
      (rowHistory K n (fun i ↦ x i) (j+1)))
      (adaptiveResidual w (predictableDirection K n f) (j+1)
        (rowHistory K n (fun i ↦ x i) (j+1)) s)=_
    rw [predictableDirection_rows K n f ha x j,ih]
    apply columnResidual_orthogonalRemainder
    intro i hi
    exact gramSchmidtNormed_pairwise_orthogonal _ (Ne.symm (Nat.ne_of_lt hi))

include ha in
lemma predictableOffset_rows {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin n)) (J : ℕ) (s : ι) :
    adaptiveOffset w (predictableDirection K n f) (J+1)
      (rowHistory K n (fun i ↦ x i) (J+1)) s=
      ∑ j∈Finset.range J,
        ⟪columnVector (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j)
          (orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n)) (w s) j),
          WithLp.toLp 2 (rowColumn K n (fun i ↦ x i) (j+1))⟫ := by
  induction J with
  | zero => simp [adaptiveOffset,predictableDirection,columnVector,columnResidual,linearProcess]
  | succ J ih =>
    change adaptiveOffset w (predictableDirection K n f) (J+1)
      (rowHistory K n (fun i ↦ x i) (J+1)) s+
      linearProcess (fun i k ↦ columnVector
        (predictableDirection K n f (J+1) (rowHistory K n (fun i ↦ x i) (J+1)))
        (adaptiveResidual w (predictableDirection K n f) (J+1)
          (rowHistory K n (fun i ↦ x i) (J+1)) i) k)
        (rowColumn K n (fun i ↦ x i) (J+1)) s=_
    rw [ih,Finset.sum_range_succ,predictableDirection_rows K n f ha x J]
    congr 1
    unfold linearProcess
    dsimp only
    rw [predictableResidual_rows K n f ha x w J s]
    rw [euclidean_inner_sum]

include ha in
lemma normalizedOffset_rows (hn : 0<n) (F : (Fin (K+1) → ℝ) → Bool) :
    adaptiveOffset (spinVector n) (predictableDirection K n f) (K+1)
      (rowHistory K n (fun i ↦ x i) (K+1)) (fun i ↦ F (x i))/
      ((n : ℝ)*Real.sqrt (n : ℝ))=
      ∑ j∈Finset.range K,empiricalColumnEnergy K n f x (fun y ↦ spin (F y)) j := by
  rw [predictableOffset_rows K n f ha x (spinVector n) K]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hw : spinVector n (fun i ↦ F (x i))=
      Real.sqrt (n : ℝ) • empiricalVector (fun y ↦ spin (F y)) x n :=
    (empiricalVector_scale (fun y ↦ spin (F y)) x hn).symm
  have hz : WithLp.toLp 2 (rowColumn K n (fun i ↦ x i) (j+1))=
      Real.sqrt (n : ℝ) • empiricalVector
        (fun y ↦ if hj : j+1<K+1 then y ⟨j+1,hj⟩ else 0) x n :=
    by
    change (WithLp.toLp 2 (fun i : Fin n ↦ if hj : j+1<K+1 then x i ⟨j+1,hj⟩ else 0)) = _
    exact (empiricalVector_scale (fun y : Fin (K+1) → ℝ ↦ if hj : j+1<K+1 then y ⟨j+1,hj⟩ else 0) x hn).symm
  rw [hw,hz,orthogonalRemainder_smul,columnVector_smul,real_inner_smul_left,real_inner_smul_right,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  unfold empiricalColumnEnergy
  have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have hs : Real.sqrt (n : ℝ)≠0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  field_simp

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalCalculus
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {Ω : Type*} [MeasurableSpace Ω]

lemma empiricalVector_measurable (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (fun x : ℕ → Ω ↦ empiricalVector f x n) := by
  have hm : Measurable (fun x : ℕ → Ω ↦ WithLp.toLp 2 (fun i : Fin n ↦ f (x i))) := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply Measurable.of_eval
    intro i
    exact hf.comp (measurable_pi_apply i.val)
  exact hm.const_smul (Real.sqrt (n : ℝ))⁻¹

lemma iid_average_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x : ℕ → Ω ↦ (∑ i∈Finset.range n,f (x i))/(n : ℝ))
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i hi
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).integrable_comp_of_integrable hf

lemma iid_average_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) {n : ℕ} (hn : 0<n) :
    (∫ x : ℕ → Ω,(∑ i∈Finset.range n,f (x i))/(n : ℝ)
      ∂Measure.infinitePi (fun _ : ℕ ↦ μ))=∫ y,f y ∂μ := by
  have hh (i : ℕ) : (∫ x : ℕ → Ω,f (x i) ∂Measure.infinitePi (fun _ : ℕ ↦ μ))=∫ y,f y ∂μ :=
    (iid_sample_law μ i).integral_comp hf.aestronglyMeasurable
  rw [integral_div,integral_finsetSum]
  · simp only [hh,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')
  · intro i hi
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).integrable_comp_of_integrable hf

omit [MeasurableSpace Ω] in
lemma empiricalVector_norm_sq (f : Ω → ℝ) (x : ℕ → Ω) (n : ℕ) :
    ‖empiricalVector f x n‖^2=(∑ i∈Finset.range n,(f (x i))^2)/(n : ℝ) := by
  rw [←real_inner_self_eq_norm_sq,empiricalVector_inner]
  simp only [sq]

lemma empirical_norm_sq_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable (fun y ↦ (f y)^2) μ) (n : ℕ) :
    Integrable (fun x : ℕ → Ω ↦ ‖empiricalVector f x n‖^2)
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  simpa only [empiricalVector_norm_sq] using iid_average_integrable μ _ hf n

lemma empirical_norm_sq_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable (fun y ↦ (f y)^2) μ) {n : ℕ} (hn : 0<n) :
    (∫ x : ℕ → Ω,‖empiricalVector f x n‖^2
      ∂Measure.infinitePi (fun _ : ℕ ↦ μ))=∫ y,(f y)^2 ∂μ := by
  simpa only [empiricalVector_norm_sq] using iid_average_integral μ _ hf hn

omit [MeasurableSpace Ω] in
lemma empiricalVector_norm_unit (f : Ω → ℝ) (hf : ∀ y,(f y)^2=1)
    (x : ℕ → Ω) {n : ℕ} (hn : 0<n) : ‖empiricalVector f x n‖=1 := by
  have he : ‖empiricalVector f x n‖^2=1 := by
    rw [empiricalVector_norm_sq]
    simp only [hf,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    exact div_self (by exact_mod_cast hn.ne')
  nlinarith [norm_nonneg (empiricalVector f x n)]

omit [MeasurableSpace Ω] in
lemma empiricalVector_norm_le_one (f : Ω → ℝ) (hf : ∀ y,(f y)^2=1)
    (x : ℕ → Ω) (n : ℕ) : ‖empiricalVector f x n‖≤1 := by
  rcases n.eq_zero_or_pos with rfl|hn
  · simp [empiricalVector]
  · exact (empiricalVector_norm_unit f hf x hn).le

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma orthogonalRemainder_gramSchmidt_norm_le {κ : Type*} [Fintype κ]
    (a : ℕ → EuclideanSpace ℝ κ) (w : EuclideanSpace ℝ κ) (j : ℕ) :
    ‖orthogonalRemainder (gramSchmidtNormed ℝ a) w j‖≤‖w‖ := by
  induction j with
  | zero => simp [orthogonalRemainder]
  | succ j ih =>
    rw [←columnResidual_orthogonalRemainder _ _ _ (fun i hi ↦
      gramSchmidtNormed_pairwise_orthogonal _ (Ne.symm (Nat.ne_of_lt hi)))]
    exact (columnResidual_norm_le (gramSchmidtNormed_unitOrZero a j) _).trans ih

lemma measurable_orthogonalRemainder {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (v : Ω → ℕ → EuclideanSpace ℝ κ) (w : Ω → EuclideanSpace ℝ κ)
    (hv : ∀ i,Measurable (fun x ↦ v x i)) (hw : Measurable w) (j : ℕ) :
    Measurable (fun x ↦ orthogonalRemainder (v x) (w x) j) := by
  unfold orthogonalRemainder
  apply hw.sub
  apply Finset.measurable_sum
  intro i hi
  have hi : Measurable (fun x ↦ (⟪v x i,w x⟫ : ℝ)) := (hv i).inner hw
  exact hi.smul (hv i)

lemma empiricalColumnEnergy_measurable (K n : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → ℝ)
    (hm : ∀ i,Measurable (f i)) (hF : Measurable F) (j : ℕ) :
    Measurable (fun x ↦ empiricalColumnEnergy K n f x F j) := by
  have ha (i : ℕ) := measurable_gramSchmidtNormed
    (fun x l ↦ empiricalVector (f l) x n) (fun l ↦ empiricalVector_measurable (f l) (hm l) n) i
  have hw := empiricalVector_measurable F hF n
  apply (measurable_columnVector (ha j)
    (measurable_orthogonalRemainder _ _ ha hw j)).inner
  apply empiricalVector_measurable
  split_ifs <;> fun_prop

lemma empiricalColumnEnergy_bound (K n : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → ℝ)
    (hF : ∀ y,(F y)^2=1) (x : ℕ → (Fin (K+1) → ℝ)) {j : ℕ} (hj : j<K) :
    |empiricalColumnEnergy K n f x F j|≤
      1+‖empiricalVector (fun y ↦ y ⟨j+1,by omega⟩) x n‖^2 := by
  let a := fun l ↦ empiricalVector (f l) x n
  let w := empiricalVector F x n
  let z := empiricalVector (fun y ↦ y ⟨j+1,by omega⟩) x n
  have hw : ‖orthogonalRemainder (gramSchmidtNormed ℝ a) w j‖≤1 :=
    (orthogonalRemainder_gramSchmidt_norm_le a w j).trans
      (empiricalVector_norm_le_one F hF x n)
  have hc : ‖columnVector (gramSchmidtNormed ℝ a j)
      (orthogonalRemainder (gramSchmidtNormed ℝ a) w j)‖≤1 :=
    (columnVector_norm_le (gramSchmidtNormed_unitOrZero a j) _).trans
      (by nlinarith [norm_nonneg (orthogonalRemainder (gramSchmidtNormed ℝ a) w j)])
  unfold empiricalColumnEnergy
  simp only [dite_eq_left (show j+1<K+1 by omega)]
  calc
    _ ≤ ‖columnVector (gramSchmidtNormed ℝ a j)
        (orthogonalRemainder (gramSchmidtNormed ℝ a) w j)‖*‖z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖z‖ := by nlinarith [norm_nonneg z]
    _ ≤ 1+‖z‖^2 := by nlinarith [sq_nonneg (‖z‖-1)]

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalEnergyLimit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma gaussian_coordinate_memLp {κ : Type*} [Fintype κ] (i : κ) :
    MemLp (fun x : κ → ℝ ↦ x i) 2 (gaussianProduct κ) :=
  SKValue.gaussian_memLp (measurePreserving_eval (fun _ : κ ↦ standardGaussian) i).hasLaw 2 (by norm_num)

lemma gaussian_coordinate_sq_mean {κ : Type*} [Fintype κ] (i : κ) :
    (∫ x : κ → ℝ,(x i)^2 ∂gaussianProduct κ)=1 :=
  SKValue.gaussian_second_moment (measurePreserving_eval (fun _ : κ ↦ standardGaussian) i).hasLaw

lemma predictable_coordinate_mean_zero (K : ℕ) (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    {i j : ℕ} (hij : i≤j) (hj : j<K) :
    (∫ y,f i y*y ⟨j+1,by omega⟩ ∂gaussianProduct (Fin (K+1)))=0 := by
  have hd : SKValue.DependsBefore (j+1) (f i) := by
    intro x y he
    exact ha i x y (fun k hk ↦ he k (by omega))
  have hh := (hd.independent (by omega) (hm i)).integral_mul_eq_mul_integral
    (hm i).aestronglyMeasurable (SKValue.measurable_coordinate K (j+1)).aestronglyMeasurable
  rw [SKValue.gaussian_mean (SKValue.coordinate_hasLaw K (j+1)),mul_zero] at hh
  simpa only [Pi.mul_apply,SKValue.gaussianProduct,gaussianProduct,SKValue.standardGaussian,standardGaussian,SKValue.coordinate_eq_apply (show j+1<K+1 by omega)] using hh

lemma unit_function_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) (hm : Measurable F) (hF : ∀ x,(F x)^2=1) :
    MemLp F 2 μ := by
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  have hh := hF x
  nlinarith [sq_abs (F x),abs_nonneg (F x)]

theorem empiricalColumnEnergy_ae_tendsto (K : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → ℝ)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (hL : ∀ i<K,MemLp (f i) 2 (gaussianProduct (Fin (K+1))))
    (hu : ∀ i<K,(∫ y,(f i y)^2 ∂gaussianProduct (Fin (K+1)))=1)
    (ho : ∀ i j,i<j → j<K →(∫ y,f i y*f j y ∂gaussianProduct (Fin (K+1)))=0)
    (hFm : Measurable F) (hF : ∀ y,(F y)^2=1) {j : ℕ} (hj : j<K) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ gaussianProduct (Fin (K+1))),
      Tendsto (fun n ↦ empiricalColumnEnergy K n f x F j) atTop
        (𝓝 ((∫ y,f j y*F y ∂gaussianProduct (Fin (K+1)))*
          (∫ y,F y*y ⟨j+1,by omega⟩ ∂gaussianProduct (Fin (K+1))))) := by
  let μ := gaussianProduct (Fin (K+1))
  let Z : (Fin (K+1) → ℝ) → ℝ := fun y ↦ y ⟨j+1,by omega⟩
  have hF2 := unit_function_memLp μ F hFm hF
  have hZ2 : MemLp Z 2 μ := gaussian_coordinate_memLp _
  have hZi : Integrable (fun y ↦ (Z y)^2) μ := by
    simpa only [sq,Pi.mul_def] using hZ2.integrable_mul hZ2
  have hFi : Integrable (fun y ↦ (F y)^2) μ := by
    simpa only [sq,Pi.mul_def] using hF2.integrable_mul hF2
  have hn : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i≤j,
      Tendsto (fun n ↦ ‖empiricalVector (f i) x n‖) atTop (𝓝 1) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro hi
    apply empirical_norm_tendsto_one μ (f i) (hm i)
    · simpa only [sq,Pi.mul_def] using (hL i (by omega)).integrable_mul (hL i (by omega))
    · exact hu i (by omega)
  have hi : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i l,i<l → l≤j →
      Tendsto (fun n ↦ ⟪empiricalVector (f i) x n,empiricalVector (f l) x n⟫) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro l
    apply ae_all_iff.mpr
    intro hil
    apply ae_all_iff.mpr
    intro hl
    simpa only [μ,ho i l hil (by omega)] using empirical_inner_tendsto μ (f i) (f l)
      ((hm i).mul (hm l)) ((hL i (by omega)).integrable_mul (hL l (by omega)))
  have haf : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i≤j,
      Tendsto (fun n ↦ ⟪empiricalVector (f i) x n,empiricalVector F x n⟫) atTop
        (𝓝 (∫ y,f i y*F y ∂μ)) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro hi
    exact empirical_inner_tendsto μ (f i) F ((hm i).mul hFm)
      ((hL i (by omega)).integrable_mul hF2)
  have haz : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i≤j,
      Tendsto (fun n ↦ ⟪empiricalVector (f i) x n,empiricalVector Z x n⟫) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro hi
    simpa only [Z,μ,predictable_coordinate_mean_zero K f hm ha hi hj] using
      empirical_inner_tendsto μ (f i) Z ((hm i).mul (measurable_pi_apply _))
        ((hL i (by omega)).integrable_mul hZ2)
  filter_upwards [hn,hi,haf,haz,
    empirical_norm_tendsto_one μ F hFm hFi (by simp only [hF]; simp),
    empirical_norm_tendsto_one μ Z (measurable_pi_apply _) hZi (gaussian_coordinate_sq_mean _),
    empirical_inner_tendsto μ F Z (hFm.mul (measurable_pi_apply _)) (hF2.integrable_mul hZ2)]
    with x hn hi haf haz hFn hZn hb
  have he (n : ℕ) : empiricalColumnEnergy K n f x F j=
      ⟪gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j,empiricalVector F x n⟫*
        ⟪orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n))
          (empiricalVector F x n) (j+1),empiricalVector Z x n⟫+
      (⟪gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j,empiricalVector F x n⟫^2/
        Real.sqrt 2)*⟪gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j,
          empiricalVector Z x n⟫ := by
    unfold empiricalColumnEnergy
    simp only [dite_eq_left (show j+1<K+1 by omega)]
    exact column_revealed_energy _ _ _ _ (fun i hi ↦
      gramSchmidtNormed_pairwise_orthogonal _ (Ne.symm (Nat.ne_of_lt hi)))
  simpa only [he] using normalized_column_energy_tendsto
    (fun n l ↦ empiricalVector (f l) x n) (fun n ↦ empiricalVector F x n)
    (fun n ↦ empiricalVector Z x n) j (fun i ↦ ∫ y,f i y*F y ∂μ)
    (∫ y,F y*Z y ∂μ) hn hi hFn hZn haf haz hb

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GaussianTranspose
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable (κ ν : Type*) [Fintype κ] [Fintype ν]

lemma uncurryGaussian_preserving :
    MeasurePreserving (uncurryGaussian κ ν) (Measure.pi (fun _ : κ ↦ gaussianProduct ν))
      (gaussianProduct (κ×ν)) := by
  refine ⟨(uncurryGaussian κ ν).measurable,?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (uncurryGaussian κ ν).measurable (MeasurableSet.univ_pi hs)]
  have he : (uncurryGaussian κ ν) ⁻¹' univ.pi s=
      univ.pi (fun i : κ ↦ univ.pi (fun j : ν ↦ s (i,j))) := by
    ext f
    simp only [mem_preimage,mem_univ_pi,uncurryGaussian,MeasurableEquiv.coe_mk]
    exact ⟨fun h i j ↦ h (i,j),fun h k ↦ h k.1 k.2⟩
  rw [he,Measure.pi_pi]
  simp only [gaussianProduct,Measure.pi_pi,Fintype.prod_prod_type]

lemma transposeGaussian_preserving :
    MeasurePreserving (transposeGaussian κ ν) (Measure.pi (fun _ : κ ↦ gaussianProduct ν))
      (Measure.pi (fun _ : ν ↦ gaussianProduct κ)) := by
  exact (uncurryGaussian_preserving ν κ).symm.comp
    ((measurePreserving_piCongrLeft (fun _ : ν×κ ↦ standardGaussian) (Equiv.prodComm κ ν)).comp
      (uncurryGaussian_preserving κ ν))

lemma iid_gaussian_columns_law (K n : ℕ) :
    HasLaw (fun x : ℕ → (Fin K → ℝ) ↦ fun j : Fin K ↦ fun i : Fin n ↦ x i j)
      (columnHistoryLaw (Fin n) K)
      (Measure.infinitePi (fun _ : ℕ ↦ gaussianProduct (Fin K))) := by
  exact (transposeGaussian_preserving (Fin n) (Fin K)).hasLaw.comp
    (iid_prefix_law (gaussianProduct (Fin K)) n)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma measurable_finite_eval {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (d : Ω → ι → ℝ) (hd : ∀ i,Measurable (fun x ↦ d x i)) (s : Ω → ι)
    (hs : Measurable s) : Measurable (fun x ↦ d x (s x)) := by
  classical
  have he : (fun x ↦ d x (s x))=fun x ↦ ∑ i : ι,if s x=i then d x i else 0 := by
    funext x
    simp
  rw [he]
  apply Finset.measurable_sum
  intro i hi
  exact (hd i).ite (hs (measurableSet_singleton i)) measurable_const

lemma rowSpin_measurable (K n : ℕ) (F : (Fin (K+1) → ℝ) → Bool) (hF : Measurable F) :
    Measurable (rowSpin K n F) := by
  apply Measurable.of_eval
  intro i
  exact hF.comp (paddedRow_measurable K n (K+1) i)

lemma rowSpin_rows (K n : ℕ) (F : (Fin (K+1) → ℝ) → Bool)
    (x : ℕ → (Fin (K+1) → ℝ)) :
    rowSpin K n F (rowHistory K n (fun i ↦ x i) (K+1))=fun i : Fin n ↦ F (x i) := by
  funext i
  change F (paddedRow K n (rowHistory K n (fun i ↦ x i) (K+1)) i)=F (x i)
  apply congrArg F
  funext j
  simp [paddedRow,rowHistory,rowColumn,j.isLt]

lemma rowHistory_full (K n : ℕ) (x : ℕ → (Fin (K+1) → ℝ)) :
    rowHistory K n (fun i ↦ x i) (K+1)=fun j (i : Fin n) ↦ x i j := by
  funext j i
  simp [rowHistory,rowColumn,j.isLt]

theorem empirical_finite_spin_lower (K : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → Bool)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (hF : Measurable F) {n : ℕ} (hn : 0<n) :
    (∫ x,∑ j∈Finset.range K,empiricalColumnEnergy K n f x (fun y ↦ spin (F y)) j
      ∂Measure.infinitePi (fun _ : ℕ ↦ gaussianProduct (Fin (K+1))))≤groundStateSequence n := by
  let v := predictableDirection K n f
  let s := rowSpin K n F
  have hs : Measurable (fun h ↦ adaptiveOffset (spinVector n) v (K+1) h (s h)) :=
    measurable_finite_eval _
      (adaptiveOffset_measurable (spinVector n) v (predictableDirection_measurable K n f hm) (K+1))
      s (rowSpin_measurable K n F hF)
  have hb := finite_adaptive_SK_lower hn v (predictableDirection_measurable K n f hm)
    (predictableDirection_unitOrZero K n f) (K+1) s hs
  let d := fun h ↦ adaptiveOffset (spinVector n) v (K+1) h (s h)/
    ((n : ℝ)*Real.sqrt (n : ℝ))
  have hd : Measurable d := hs.div_const _
  have he := (iid_gaussian_columns_law (K+1) n).integral_comp hd.aestronglyMeasurable
  have heq : (fun x : ℕ → (Fin (K+1) → ℝ) ↦ d (fun j i ↦ x i j))=
      fun x ↦ ∑ j∈Finset.range K,empiricalColumnEnergy K n f x (fun y ↦ spin (F y)) j := by
    funext x
    dsimp [d,v,s]
    rw [←rowHistory_full K n x,rowSpin_rows K n F x]
    exact normalizedOffset_rows K n f ha x hn F
  dsimp only [Function.comp_def] at he
  rw [heq] at he
  rw [he]
  simpa only [d,integral_div] using hb

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_ConstantFatou
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Set
open scoped Topology
namespace SKValueG

theorem constant_limit_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (C : ℕ → ℝ) (L M : ℝ)
    (hi : ∀ n,Integrable (f n) μ) (hn : ∀ n,∀ᵐ ω ∂μ,0≤f n ω)
    (ht : ∀ᵐ ω ∂μ,Tendsto (fun n ↦ f n ω) atTop (𝓝 L))
    (hC : ∀ n,(∫ ω,f n ω ∂μ)≤C n) (hCt : Tendsto C atTop (𝓝 M)) : L≤M := by
  have ha : ∀ᵐ ω ∂μ,(∀ n,0≤f n ω) ∧ Tendsto (fun n ↦ f n ω) atTop (𝓝 L) :=
    (ae_all_iff.mpr hn).and ht
  obtain ⟨ω,hω⟩ := ha.exists
  have hL : 0≤L := ge_of_tendsto hω.2 (Eventually.of_forall hω.1)
  have hlim : Tendsto (fun n ↦ ∫ ω,min (f n ω) L ∂μ) atTop (𝓝 L) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ ↦ L)
      (fun n ↦ (hi n).aestronglyMeasurable.inf (aestronglyMeasurable_const (b:=L)))
      (integrable_const L) (fun n ↦ (hn n).mono (fun ω hω ↦ by
        change |min (f n ω) L|≤L
        rw [abs_of_nonneg (le_min hω hL)]
        exact min_le_right _ _))
      (ht.mono (fun ω hω ↦ by simpa using hω.min tendsto_const_nhds))
    simpa using h
  apply le_of_tendsto_of_tendsto hlim hCt
  apply Eventually.of_forall
  intro n
  apply (integral_mono ((hi n).inf (integrable_const L)) (hi n) (fun _ ↦ min_le_left _ _)).trans
  exact hC n

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

theorem predictable_coefficients_le_groundState (K : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → Bool)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (hL : ∀ i<K,MemLp (f i) 2 (gaussianProduct (Fin (K+1))))
    (hu : ∀ i<K,(∫ y,(f i y)^2 ∂gaussianProduct (Fin (K+1)))=1)
    (ho : ∀ i j,i<j → j<K →(∫ y,f i y*f j y ∂gaussianProduct (Fin (K+1)))=0)
    (hFm : Measurable F) :
    (∑ j : Fin K,(∫ y,f j y*spin (F y) ∂gaussianProduct (Fin (K+1)))*
      (∫ y,spin (F y)*y ⟨j.val+1,by omega⟩ ∂gaussianProduct (Fin (K+1))))≤groundStateValue := by
  let μ := gaussianProduct (Fin (K+1))
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let S := fun y ↦ spin (F y)
  let Z := fun (j : Fin K) (y : Fin (K+1) → ℝ) ↦ y ⟨j.val+1,by omega⟩
  let e := fun n x ↦ ∑ j : Fin K,empiricalColumnEnergy K n f x S j
  let c := fun n (x : ℕ → (Fin (K+1) → ℝ)) ↦
    ∑ j : Fin K,(1+‖empiricalVector (Z j) x n‖^2)
  let L := ∑ j : Fin K,(∫ y,f j y*S y ∂μ)*(∫ y,S y*Z j y ∂μ)
  have hSm : Measurable S := (measurable_of_finite spin).comp hFm
  have hS : ∀ y,(S y)^2=1 := fun y ↦ spin_sq (F y)
  have hZ (j : Fin K) : Integrable (fun y ↦ (Z j y)^2) μ := by
    simpa only [sq,Pi.mul_def] using (gaussian_coordinate_memLp (⟨j.val+1,by omega⟩ : Fin (K+1))).integrable_mul
      (gaussian_coordinate_memLp (⟨j.val+1,by omega⟩ : Fin (K+1)))
  have hci (n : ℕ) : Integrable (c n) P :=
    integrable_finsetSum _ (fun j _ ↦ (integrable_const 1).add
      (empirical_norm_sq_integrable μ (Z j) (hZ j) n))
  have hei (n : ℕ) : Integrable (e n) P := by
    apply integrable_finsetSum
    intro j hj
    apply ((integrable_const 1).add (empirical_norm_sq_integrable μ (Z j) (hZ j) n)).mono'
      (empiricalColumnEnergy_measurable K n f S hm hSm j).aestronglyMeasurable
    exact Eventually.of_forall (fun x ↦ empiricalColumnEnergy_bound K n f S hS x j.isLt)
  have hen (n : ℕ) (x) : 0≤e n x+c n x := by
    change 0≤(∑ j : Fin K,empiricalColumnEnergy K n f x S j)+
      ∑ j : Fin K,(1+‖empiricalVector (Z j) x n‖^2)
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro j hj
    have hh := (abs_le.mp (empiricalColumnEnergy_bound K n f S hS x j.isLt)).1
    linarith
  have hct (n : ℕ) (hn : 0<n) : (∫ x,c n x ∂P)=2*(K : ℝ) := by
    rw [show c n=(fun x ↦ ∑ j : Fin K,(1+‖empiricalVector (Z j) x n‖^2)) from rfl,
      integral_finsetSum]
    · have hh (j : Fin K) : (∫ x,(1+‖empiricalVector (Z j) x n‖^2) ∂P)=2 := by
        rw [integral_add (integrable_const 1) (empirical_norm_sq_integrable μ (Z j) (hZ j) n)]
        rw [empirical_norm_sq_integral μ (Z j) (hZ j) hn]
        rw [gaussian_coordinate_sq_mean]
        norm_num [P]
      simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    · intro j hj
      exact (integrable_const 1).add (empirical_norm_sq_integrable μ (Z j) (hZ j) n)
  have heL : ∀ᵐ x ∂P,Tendsto (fun n ↦ e n x) atTop (𝓝 L) := by
    have hh : ∀ᵐ x ∂P,∀ j : Fin K,Tendsto
        (fun n ↦ empiricalColumnEnergy K n f x S j) atTop
        (𝓝 ((∫ y,f j y*S y ∂μ)*(∫ y,S y*Z j y ∂μ))) := by
      apply ae_all_iff.mpr
      intro j
      exact empiricalColumnEnergy_ae_tendsto K f S hm ha hL hu ho hSm hS j.isLt
    exact hh.mono (fun x hx ↦ tendsto_finsetSum (s:=Finset.univ) (fun j _ ↦ hx j))
  have hcL : ∀ᵐ x ∂P,Tendsto (fun n ↦ c n x) atTop (𝓝 (2*(K : ℝ))) := by
    have hh : ∀ᵐ x ∂P,∀ j : Fin K,Tendsto
        (fun n ↦ ‖empiricalVector (Z j) x n‖) atTop (𝓝 1) := by
      apply ae_all_iff.mpr
      intro j
      exact empirical_norm_tendsto_one μ (Z j) (measurable_pi_apply _) (hZ j)
        (gaussian_coordinate_sq_mean _)
    filter_upwards [hh] with x hx
    have ht := tendsto_finsetSum (s:=Finset.univ)
      (fun j _ ↦ (tendsto_const_nhds (x:=(1 : ℝ))).add ((hx j).pow 2))
    simpa [c,two_mul] using ht
  have hb := constant_limit_integral_le (μ:=P)
    (fun n x ↦ e (n+1) x+c (n+1) x)
    (fun n ↦ groundStateSequence (n+1)+2*(K : ℝ)) (L+2*(K : ℝ))
    (groundStateValue+2*(K : ℝ))
    (fun n ↦ (hei (n+1)).add (hci (n+1)))
    (fun n ↦ Eventually.of_forall (hen (n+1)))
    ((heL.and hcL).mono (fun x hx ↦ (hx.1.add hx.2).comp (tendsto_add_atTop_nat 1)))
    (fun n ↦ by
      rw [integral_add (hei (n+1)) (hci (n+1)),hct (n+1) (by omega)]
      apply add_le_add_left
      convert empirical_finite_spin_lower K f F hm ha hFm (show 0<n+1 by omega) using 1
      all_goals try with_reducible_and_instances rfl
      apply integral_congr_ae
      filter_upwards [] with x
      exact Fin.sum_univ_eq_sum_range (fun j ↦ empiricalColumnEnergy K (n+1) f x S j) K)
    ((groundStateSequence_tendsto.comp (tendsto_add_atTop_nat 1)).add_const _)
  exact (add_le_add_iff_right (2*(K : ℝ))).mp hb

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RoundingSpin
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma measurable_boolSign : Measurable boolSign :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma spin_boolSign_eq {x : ℝ} (hx : x≠0) : SKValueG.spin (boolSign x)=Real.sign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [boolSign,SKValueG.spin,not_le.mpr h,Real.sign_of_neg h]
  · simp [boolSign,SKValueG.spin,h.le,Real.sign_of_pos h]

lemma gaussian_rounding_nonzero (a : ℝ) :
    ∀ᵐ z ∂standardGaussian,a+2*cdf standardGaussian z-1≠0 := by
  have hh : ∀ᵐ z ∂standardGaussian,cdf standardGaussian z≠(1-a)/2 :=
    (standardGaussian_cdf_hasLaw_uniform.ae_iff (measurableSet_setOfPred.mp ((measurableSet_eq_fun measurable_id measurable_const).compl))).mpr
      ((volume.restrict (Ioc (0 : ℝ) 1)).ae_ne ((1-a)/2))
  filter_upwards [hh] with z hz
  intro h
  apply hz
  linarith

lemma independent_rounding_nonzero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U Z : Ω → ℝ}
    (hU : Measurable U) (hZ : HasLaw Z standardGaussian μ) (hind : IndepFun U Z μ) :
    ∀ᵐ ω ∂μ,U ω+2*cdf standardGaussian (Z ω)-1≠0 := by
  have hLaw : HasLaw U (μ.map U) μ := ⟨hU.aemeasurable,rfl⟩
  have hJoint := hind.hasLaw_prod hLaw hZ
  have hm : Measurable (fun p : ℝ×ℝ ↦ p.1+2*cdf standardGaussian p.2-1) :=
    (measurable_fst.add (((monotone_cdf _).measurable.comp measurable_snd).const_mul 2)).sub_const 1
  apply (hJoint.ae_iff (measurableSet_setOfPred.mp ((measurableSet_eq_fun hm measurable_const).compl))).mpr
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun hm measurable_const).compl)).mpr
  exact Eventually.of_forall gaussian_rounding_nonzero

lemma finite_rounding_signed_spin {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) (hUp : DependsBefore N U) :
    (fun z ↦ SKValueG.spin (boolSign (U z+2*cdf standardGaussian (coordinate N N z)-1)))
      =ᵐ[gaussianProduct (Fin (N+1))]
    (fun z ↦ Real.sign (U z+2*cdf standardGaussian (coordinate N N z)-1)) := by
  have := gaussianProduct_probability (Fin (N+1))
  exact (independent_rounding_nonzero hU (coordinate_hasLaw N N)
    (hUp.independent (by omega) hU)).mono (fun _ ↦ spin_boolSign_eq)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

theorem normalized_shifted_sum_le_groundState {N : ℕ}
    (H : Fin N → (Fin (N+1) → ℝ) → ℝ) (U : (Fin (N+1) → ℝ) → ℝ)
    (hm : ∀ j,Measurable (H j)) (hp : ∀ j : Fin N,DependsBefore j (H j))
    (hL : ∀ j,MemLp (H j) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ j,0<∫ z,(H j z)^2 ∂gaussianProduct (Fin (N+1)))
    (hU : Measurable U) (hUp : DependsBefore N U) :
    (∑ j : Fin N,(∫ z,finiteRounded U z*
      normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1)))*
      (∫ z,finiteRounded U z*coordinate N (j+1) z ∂gaussianProduct (Fin (N+1))))≤groundStateValue := by
  let f := fun j : ℕ ↦ if hj : j<N then
    normalizedIncrement (H ⟨j,hj⟩) (coordinate N j) (gaussianProduct (Fin (N+1))) else fun _ ↦ 0
  let F := fun z ↦ boolSign (U z+2*cdf standardGaussian (coordinate N N z)-1)
  have hfm (j : ℕ) : Measurable (f j) := by
    dsimp only [f]
    split_ifs with hj
    · exact measurable_normalizedIncrement (hm ⟨j,hj⟩)
    · exact measurable_const
  have hfa (l : ℕ) (x y : Fin (N+1) → ℝ)
      (he : ∀ i : Fin (N+1),i.val≤l → x i=y i) : f l x=f l y := by
    dsimp only [f]
    split_ifs with hl
    · apply normalizedIncrement_dependsBefore (by omega) (hp ⟨l,hl⟩)
      intro i hi
      change i.val<l+1 at hi
      exact he i (by omega)
    · rfl
  have hfL (j : ℕ) (hj : j<N) : MemLp (f j) 2 (SKValueG.gaussianProduct (Fin (N+1))) := by
    simp only [f,dite_eq_left hj]
    exact normalizedIncrement_memLp_two (hL ⟨j,hj⟩) (coordinate_hasLaw N j)
      ((hp ⟨j,hj⟩).independent (by omega) (hm ⟨j,hj⟩))
  have hfu (j : ℕ) (hj : j<N) : (∫ z,(f j z)^2 ∂SKValueG.gaussianProduct (Fin (N+1)))=1 := by
    simp only [f,dite_eq_left hj]
    exact normalizedIncrement_second_moment (hm ⟨j,hj⟩).aestronglyMeasurable (coordinate_hasLaw N j)
      ((hp ⟨j,hj⟩).independent (by omega) (hm ⟨j,hj⟩)) (hpos ⟨j,hj⟩)
  have hfo (i j : ℕ) (hij : i<j) (hj : j<N) :
      (∫ z,f i z*f j z ∂SKValueG.gaussianProduct (Fin (N+1)))=0 := by
    have hi : i<N := hij.trans hj
    simp only [f,dite_eq_left hi,dite_eq_left hj]
    exact normalizedIncrements_orthogonal hij (by omega) (hm ⟨i,hi⟩) (hm ⟨j,hj⟩)
      (hp ⟨i,hi⟩) (hp ⟨j,hj⟩)
  have hFm : Measurable F := measurable_boolSign.comp
    ((hU.add (((monotone_cdf _).measurable.comp (measurable_coordinate N N)).const_mul 2)).sub_const 1)
  have he : (fun z ↦ SKValueG.spin (F z))=ᵐ[gaussianProduct (Fin (N+1))] finiteRounded U :=
    finite_rounding_signed_spin hU hUp
  have hb := SKValueG.predictable_coefficients_le_groundState N f F hfm hfa hfL hfu hfo hFm
  change _≤SKValueG.groundStateValue
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  · apply integral_congr_ae
    filter_upwards [he] with z hz
    simp only [f,dite_eq_left j.isLt,hz]
    exact mul_comm _ _
  · apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz,coordinate_eq_apply (by omega)]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_LiteralLower
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

theorem shiftedCoefficientSum_le_groundState_oai (W : BrownianSpace) (γ : OrderParameter)
    {T : ℝ} (hT : 0≤T) (hT1 : T<1) {N : ℕ} (hN : 0<N)
    (hpos : ∀ j<N,0<∫ z,(rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1))) :
    shiftedCoefficientSum W γ T N≤groundStateValue := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT,hT1⟩
  rw [literal_shiftedCoefficientSum]
  exact normalized_shifted_sum_le_groundState
    (fun j : Fin N ↦ meshRaw T N γ.coeff (gradient W γ) j)
    (meshTerminal T N γ.coeff (gradient W γ))
    (fun j ↦ mesh_raw_measurable hT hG hN j.isLt.le)
    (fun j ↦ mesh_raw_depends T j.isLt.le γ.coeff (gradient W γ))
    (fun j ↦ mesh_raw_memLp hT hG hDb hN j.isLt.le)
    (fun j ↦ hpos j j.isLt)
    (mesh_terminal_measurable hT hG hN) (mesh_terminal_depends T N γ.coeff (gradient W γ))

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.shiftedCoefficientSum_le_groundState_oai := @OAI.SKValue.shiftedCoefficientSum_le_groundState_oai
