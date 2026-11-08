-- Prove2me | solution 1 for HedgePSNV.degenerate_simple_integrals_attainable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T22:37:35.087466+00:00
-- url     : https://prove2.me/submissions/0e4ecc50-8517-43b5-80c0-5f569c2e3cca

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model

set_option maxHeartbeats 2000000

set_option linter.all false
set_option Elab.async false
-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

/-- The coordinates of a standard `d`-dimensional Brownian motion form one real Gaussian
process indexed by `time × coordinate`. -/
theorem stdBrownian_isGaussianProcess {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) :
    IsGaussianProcess (fun (p : ℝ≥0 × Fin d) ω => W p.1 ω p.2) P := by
  obtain ⟨_, _, hBM, hind⟩ := hW
  refine ⟨fun I => ?_⟩
  classical
  let I' : Finset ℝ≥0 := I.image Prod.fst
  let V : Fin d → Ω → (I' → ℝ) := fun i ω => fun t => W t ω i
  have hV : ∀ i, HasGaussianLaw (V i) P := fun i =>
    (hBM i).isGaussianProcess.hasGaussianLaw I'
  have hVind : iIndepFun V P :=
    hind.comp (fun _ (f : ℝ≥0 → ℝ) => fun t : I' => f t) (fun _ => by fun_prop)
  have hjoint := hVind.hasGaussianLaw hV
  let L0 : (Fin d → (I' → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x p => x p.1.2 ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have := hjoint.map (LinearMap.toContinuousLinearMap L0)
  have heq : (fun ω => I.restrict (fun p : ℝ≥0 × Fin d => W p.1 ω p.2)) =
      (LinearMap.toContinuousLinearMap L0) ∘ (fun ω x => V x ω) := by
    funext ω p; rfl
  rw [heq]; exact this

/-- The covariance of two coordinates of a standard Brownian motion. -/
theorem stdBrownian_cov {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s t : ℝ≥0) (i j : Fin d) :
    cov[fun ω => W s ω i, fun ω => W t ω j; P] = if i = j then ((min s t : ℝ≥0) : ℝ) else 0 := by
  obtain ⟨hm, _, hBM, hind⟩ := hW
  split_ifs with hij
  · subst hij
    exact (hBM i).covariance_fun_eval s t
  · have h2 : IndepFun (fun ω => W s ω i) (fun ω => W t ω j) P := by
      have := hind.indepFun hij
      exact this.comp (φ := fun f : ℝ≥0 → ℝ => f s) (ψ := fun f : ℝ≥0 → ℝ => f t)
        (by fun_prop) (by fun_prop)
    have hP : IsProbabilityMeasure P := (hBM i).isGaussianProcess.isProbabilityMeasure
    exact h2.covariance_eq_zero ((hBM i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      ((hBM j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem stdBrownian_coord_measurable {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : Measurable (fun ω => W t ω i) := by
  have := hW.1 t
  fun_prop

theorem stdBrownian_memLp_two {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : MemLp (fun ω => W t ω i) 2 P :=
  ((hW.2.2.1 i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

/-- Weak Markov property of a standard `d`-dimensional Brownian motion: all future increments
after `t₀` are independent of the whole past up to `t₀`. -/
theorem stdBrownian_indep_shift {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) :
    IndepFun (fun ω (p : ℝ≥0 × Fin d) => W (t₀ + p.1) ω p.2 - W t₀ ω p.2)
      (fun ω (q : Set.Iic t₀ × Fin d) => W q.1 ω q.2) P := by
  have hG := stdBrownian_isGaussianProcess hW
  have hP : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (X := fun (p : ℝ≥0 × Fin d) ω => W (t₀ + p.1) ω p.2 - W t₀ ω p.2)
    (Y := fun (q : Set.Iic t₀ × Fin d) ω => W q.1 ω q.2)
  · apply hG.of_isGaussianProcess
    rintro (⟨t, i⟩ | ⟨⟨t, ht⟩, i⟩)
    · exact ⟨{(t₀ + t, i), (t₀, i)},
        { toFun x := x ⟨(t₀ + t, i), by simp⟩ - x ⟨(t₀, i), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(t, i)},
        { toFun x := x ⟨(t, i), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro p; exact ((hm (t₀ + p.1) p.2).sub (hm t₀ p.2)).aemeasurable
  · intro q; exact (hm _ _).aemeasurable
  · rintro ⟨s, i⟩ ⟨⟨t, ht⟩, j⟩
    have ht' : t ≤ t₀ := ht
    simp only
    rw [covariance_fun_sub_left (stdBrownian_memLp_two hW _ _) (stdBrownian_memLp_two hW _ _)
      (stdBrownian_memLp_two hW _ _), stdBrownian_cov hW, stdBrownian_cov hW]
    split_ifs
    · rw [min_eq_right (ht'.trans (le_add_right le_rfl)), min_eq_right ht', sub_self]
    · simp

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

/-- The `P`-a.e. closure of a σ-algebra `G`: sets a.e. equal to a `G`-set (null sets taken
for the outer measure, so arbitrary subsets of null sets qualify). -/
@[instance_reducible]
def aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B, MeasurableSet[G] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ G, EventuallyEq.rfl⟩
  measurableSet_compl A := fun ⟨B, hB, h⟩ => ⟨Bᶜ, hB.compl, h.compl⟩
  measurableSet_iUnion f hf := by
    choose B hB h using hf
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, Filter.EventuallyEq.countable_iUnion h⟩

theorem le_aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : G ≤ aeClosure P G :=
  fun A hA => ⟨A, hA, EventuallyEq.rfl⟩

/-- Independence passes to the a.e. closure. -/
theorem indep_aeClosure {P : Measure Ω} {G H : MeasurableSpace Ω} (h : Indep G H P) :
    Indep (aeClosure P G) H P := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨B, hB, hAB⟩ hC
  rw [measure_congr (hAB.inter (EventuallyEq.refl _ C)), measure_congr hAB]
  exact h B C hB hC

end AEC

section CP
variable [MeasurableSpace Ω]

/-- With a constant initial value, the completed Brownian past lies in the a.e. closure of the
natural Brownian past. -/
theorem completedBrownianPast_const_le (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : ℝ≥0) :
    completedBrownianPast P W (fun _ => x₀) s ≤
      aeClosure P (⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance) := by
  set G : MeasurableSpace Ω := ⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance
  refine sup_le (sup_le (le_aeClosure _ _) ?_) ?_
  · rintro A ⟨T, -, rfl⟩
    by_cases hx : x₀ ∈ T
    · refine ⟨Set.univ, @MeasurableSet.univ Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = Set.univ := Set.preimage_const_of_mem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
    · refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = ∅ := Set.preimage_const_of_notMem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨N, -, hN, hAN⟩
    refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
    rw [ae_eq_empty]
    exact measure_mono_null hAN hN

/-- The future increments of a standard Brownian motion after `s` are independent of the
completed Brownian past at `s` (constant initial value). -/
theorem stdBrownian_indep_completedPast {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) :
    Indep (completedBrownianPast P W (fun _ => x₀) s)
      (MeasurableSpace.comap (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2)
        inferInstance) P := by
  refine indep_of_indep_of_le_left (indep_aeClosure ?_) (completedBrownianPast_const_le P W x₀ s)
  have h := ((IndepFun_iff_Indep _ _ _).1 (stdBrownian_indep_shift hW s)).symm
  refine indep_of_indep_of_le_left h ?_
  refine iSup_le fun r => ?_
  have hg : Measurable (fun f : Set.Iic s × Fin d → ℝ =>
      (WithLp.toLp 2 (fun i => f (r, i)) : SDEState d)) := by
    refine (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp ?_
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (r, i))
  have hc : Measurable[MeasurableSpace.comap (fun ω (q : Set.Iic s × Fin d) => W q.1 ω q.2)
      inferInstance] (W r.val) :=
    hg.comp (comap_measurable _)
  exact hc.comap_le

end CP

section M2

theorem nullMeasurable_of_aeClosure {G : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (hG : G ≤ mΩ) {f : Ω → ℝ} (hf : Measurable[aeClosure P G] f) :
    NullMeasurable f P := by
  intro A hA
  obtain ⟨B, hB, h⟩ := hf hA
  exact (hG _ hB).nullMeasurableSet.congr h.symm

variable [MeasurableSpace Ω]

theorem naturalPast_le {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s : ℝ≥0) :
    (⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance) ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun r => (hW.1 r.val).comap_le

/-- A function measurable for the completed Brownian past (constant initial value) is
a.e.-strongly measurable for the ambient σ-algebra. -/
theorem aestronglyMeasurable_of_completedPast {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    AEStronglyMeasurable a P :=
  (nullMeasurable_of_aeClosure (naturalPast_le hW s)
    (ha.mono (completedBrownianPast_const_le P W x₀ s) le_rfl)).aemeasurable.aestronglyMeasurable

/-- A completed-past-measurable function is independent of each later increment. -/
theorem indepFun_completedPast_increment {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    IndepFun a (fun ω => W (s + h) ω j - W s ω j) P := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (stdBrownian_indep_completedPast hW x₀ s) ha.comap_le) ?_
  have hm : Measurable[MeasurableSpace.comap
      (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) inferInstance]
      (fun ω => W (s + h) ω j - W s ω j) := by
    have := (measurable_pi_apply (h, j) : Measurable fun f : ℝ≥0 × Fin d → ℝ => f (h, j)).comp
      (comap_measurable (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2))
    exact this
  exact hm.comap_le

theorem stdBrownian_integral_increment {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    ∫ ω, (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hB := hW.2.2.1 j
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
    hB.integral_eval, sub_self]

theorem stdBrownian_integral_increment_sq {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    ∫ ω, (W (s + h) ω j - W s ω j) ^ 2 ∂P = h := by
  have hB := hW.2.2.1 j
  have hL := hB.hasLaw_sub (s + h) s
  have h1 : ∫ ω, (W (s + h) ω j - W s ω j) ^ 2 ∂P =
      ∫ x, x ^ 2 ∂(gaussianReal 0 (nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))) :=
    hL.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [h1]
  have h2 := variance_fun_id_gaussianReal (μ := (0 : ℝ))
    (v := nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))
  rw [variance_eq_integral (X := fun x : ℝ => x) aemeasurable_id'] at h2
  simp only [integral_id_gaussianReal, sub_zero] at h2
  rw [h2, coe_nndist, Real.dist_eq]
  push_cast
  rw [add_sub_cancel_left]
  exact abs_of_nonneg h.2

end M2

section M3
variable [MeasurableSpace Ω]

theorem completedBrownianPast_mono (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

theorem coord_measurable_completedPast (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {r t : ℝ≥0} (hrt : r ≤ t) (j : Fin d) :
    Measurable[completedBrownianPast P W ξ t] (fun ω => W r ω j) := by
  have h1 : Measurable[MeasurableSpace.comap (W r) inferInstance] (W r) := comap_measurable _
  have h0 : MeasurableSpace.comap (W r) inferInstance ≤
      ⨆ q : Set.Iic t, MeasurableSpace.comap (W q.val) inferInstance :=
    le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r, hrt⟩
  have h2 : MeasurableSpace.comap (W r) inferInstance ≤ completedBrownianPast P W ξ t := by
    unfold completedBrownianPast
    exact le_sup_of_le_left (le_sup_of_le_left h0)
  have h3 : Measurable[completedBrownianPast P W ξ t] (W r) := Measurable.mono h1 h2 le_rfl
  have h4 : Measurable fun x : SDEState d => x j := by fun_prop
  exact h4.comp h3

/-- `E[a · ΔW] = 0` for any completed-past-measurable `a` (no integrability needed). -/
theorem integral_mul_increment_eq_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    ∫ ω, a ω * (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hm := stdBrownian_coord_measurable hW
  rw [(indepFun_completedPast_increment hW x₀ s h j ha).integral_fun_mul_eq_mul_integral
    (aestronglyMeasurable_of_completedPast hW x₀ s ha)
    ((hm _ j).sub (hm _ j)).aestronglyMeasurable, stdBrownian_integral_increment hW, mul_zero]

/-- `E[a² · ΔW²] = E[a²] · h` for any completed-past-measurable `a`. -/
theorem integral_sq_mul_increment_sq {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    ∫ ω, (a ω * (W (s + h) ω j - W s ω j)) ^ 2 ∂P = (∫ ω, a ω ^ 2 ∂P) * h := by
  have hm := stdBrownian_coord_measurable hW
  have hi := (indepFun_completedPast_increment hW x₀ s h j ha).comp
    (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
  have key := hi.integral_fun_mul_eq_mul_integral
    ((aestronglyMeasurable_of_completedPast hW x₀ s ha).pow 2)
    (((hm _ j).sub (hm _ j)).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  simp_rw [mul_pow]
  rw [key, stdBrownian_integral_increment_sq hW]

end M3

section M4
variable [MeasurableSpace Ω]

/-- Discrete Itô isometry for the dyadic step sums of `HasBrownianItoIntegral`: bounded
coefficients measurable for the completed Brownian past at the left endpoints. -/
theorem itoStepSum_isometry {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (n : ℕ) (j : Fin d)
    (a : ℕ → Ω → ℝ)
    (ha : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (a k))
    (C₁ : ℝ) (hC₁ : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |a k ω| ≤ C₁) :
    ∫ ω, (itoStepSum (fun s ω => W s ω j) t n a ω) ^ 2 ∂P =
      ∑ k ∈ Finset.range (2 ^ n), (∫ ω, a k ω ^ 2 ∂P) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  set C : ℝ := max C₁ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |a k ω| ≤ C := fun k hk ω =>
    (hC₁ k hk ω).trans (le_max_left _ _)
  set h : ℝ≥0 := t / (2 : ℝ≥0) ^ n with hh
  let τ : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * t / (2 : ℝ≥0) ^ n
  have hstep : ∀ k : ℕ, ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n = τ k + h := by
    intro k; simp only [τ, hh]; ring
  have hτmono : ∀ l k : ℕ, l ≤ k → τ l ≤ τ k := by
    intro l k hlk; simp only [τ]; gcongr
  have hτsucc : ∀ l k : ℕ, l < k → τ l + h ≤ τ k := by
    intro l k hlk
    rw [← hstep]; simp only [τ]; gcongr
    exact_mod_cast Nat.succ_le_of_lt hlk
  let Δ : ℕ → Ω → ℝ := fun k ω => W (τ k + h) ω j - W (τ k) ω j
  let X : ℕ → Ω → ℝ := fun k ω => a k ω * Δ k ω
  have hsum : ∀ ω, itoStepSum (fun s ω => W s ω j) t n a ω =
      ∑ k ∈ Finset.range (2 ^ n), X k ω := by
    intro ω; unfold itoStepSum
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [X, Δ]; rw [hstep k]
  have hΔL2 : ∀ k, MemLp (Δ k) 2 P := fun k =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have haesm : ∀ k, k < 2 ^ n → AEStronglyMeasurable (a k) P := fun k hk =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (ha k hk)
  have hint : ∀ k, k < 2 ^ n → ∀ l, l < 2 ^ n → Integrable (fun ω => X k ω * X l ω) P := by
    intro k hk l hl
    have hg : Integrable (fun ω => (C * C) * |Δ k ω * Δ l ω|) P :=
      ((hΔL2 k).integrable_mul (hΔL2 l)).abs.const_mul _
    refine hg.mono' (((haesm k hk).mul (hΔL2 k).1).mul ((haesm l hl).mul (hΔL2 l).1)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    calc |X k ω * X l ω| = (|a k ω| * |a l ω|) * |Δ k ω * Δ l ω| := by
          simp only [X, abs_mul]; ring
      _ ≤ (C * C) * |Δ k ω * Δ l ω| :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hC k hk ω) (hC l hl ω) (abs_nonneg _) hC0)
            (abs_nonneg _)
  have off : ∀ l k, l < k → k < 2 ^ n → ∫ ω, X l ω * X k ω ∂P = 0 := by
    intro l k hlk hk
    have hl : l < 2 ^ n := hlk.trans hk
    have hb : Measurable[completedBrownianPast P W (fun _ => x₀) (τ k)]
        (fun ω => a l ω * Δ l ω * a k ω) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (ha k hk)
      · exact (ha l hl).mono (completedBrownianPast_mono P W _ (hτmono l k hlk.le)) le_rfl
      · exact (coord_measurable_completedPast P W _ (hτsucc l k hlk) j).sub
          (coord_measurable_completedPast P W _ (hτmono l k hlk.le) j)
    have := integral_mul_increment_eq_zero hW x₀ (τ k) h j hb
    rw [← this]
    congr 1; funext ω; simp only [X, Δ]; ring
  have hkey : ∀ ω, (itoStepSum (fun s ω => W s ω j) t n a ω) ^ 2 =
      ∑ k ∈ Finset.range (2 ^ n), ∑ l ∈ Finset.range (2 ^ n), X k ω * X l ω := by
    intro ω; rw [hsum ω, sq, Finset.sum_mul_sum]
  simp_rw [hkey]
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _
    (fun l hl => hint k (Finset.mem_range.1 hk) l (Finset.mem_range.1 hl)))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [integral_finsetSum _ (fun l hl => hint k hk' l (Finset.mem_range.1 hl))]
  rw [Finset.sum_eq_single k]
  · calc ∫ ω, X k ω * X k ω ∂P
          = ∫ ω, (a k ω * (W (τ k + h) ω j - W (τ k) ω j)) ^ 2 ∂P := by
            congr 1; funext ω; simp only [X, Δ]; ring
      _ = _ := integral_sq_mul_increment_sq hW x₀ (τ k) h j (ha k hk')
  · intro l hl hlk
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · rw [← off l k hlt hk']
      congr 1; funext ω; ring
    · exact off k l hgt (Finset.mem_range.1 hl)
  · intro hnot; exact absurd hk hnot

end M4


section StopCoef

/-- Coefficients stopped once the running discrete quadratic variation exceeds `δ`. -/
noncomputable def stopCoef (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if (∑ i ∈ Finset.range (k + 1), c i ω ^ 2) * h ≤ δ then c k ω else 0

theorem stopCoef_eq_of_le (c : ℕ → Ω → ℝ) {h δ : ℝ} (hh : 0 ≤ h) {N : ℕ} {ω : Ω}
    (hN : (∑ i ∈ Finset.range N, c i ω ^ 2) * h ≤ δ) {k : ℕ} (hk : k < N) :
    stopCoef c h δ k ω = c k ω := by
  unfold stopCoef
  rw [if_pos]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hh) hN
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hk))
    (fun i _ _ => sq_nonneg _)

theorem stopCoef_sum_le (c : ℕ → Ω → ℝ) {h δ : ℝ} (hh : 0 ≤ h) (hδ : 0 ≤ δ) (N : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range N, stopCoef c h δ k ω ^ 2) * h ≤ δ := by
  induction N with
  | zero => simpa using hδ
  | succ N ih =>
    by_cases hN : (∑ i ∈ Finset.range (N + 1), c i ω ^ 2) * h ≤ δ
    · have : ∑ k ∈ Finset.range (N + 1), stopCoef c h δ k ω ^ 2 =
          ∑ k ∈ Finset.range (N + 1), c k ω ^ 2 :=
        Finset.sum_congr rfl fun k hk => by
          rw [stopCoef_eq_of_le c hh hN (Finset.mem_range.1 hk)]
      rw [this]; exact hN
    · rw [Finset.sum_range_succ]
      have : stopCoef c h δ N ω = 0 := by unfold stopCoef; rw [if_neg hN]
      rw [this]; simpa using ih

theorem abs_stopCoef_le (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ) (ω : Ω) :
    |stopCoef c h δ k ω| ≤ |c k ω| := by
  unfold stopCoef; split_ifs <;> simp

theorem stopCoef_measurable [m : MeasurableSpace Ω] (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ)
    (hc : ∀ i, i ≤ k → Measurable (c i)) : Measurable (stopCoef c h δ k) := by
  unfold stopCoef
  refine Measurable.ite ?_ (hc k le_rfl) measurable_const
  refine measurableSet_le ?_ measurable_const
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun i hi =>
    (hc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).pow_const 2

end StopCoef

section M5
variable [MeasurableSpace Ω]

theorem itoStepSum_memLp {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (n : ℕ) (j : Fin d) (a : ℕ → Ω → ℝ)
    (ha : ∀ k, k < 2 ^ n → AEStronglyMeasurable (a k) P)
    (C : ℝ) (hC : ∀ k, k < 2 ^ n → ∀ ω, |a k ω| ≤ C) :
    MemLp (itoStepSum (fun s ω => W s ω j) t n a) 2 P := by
  have heq : itoStepSum (fun s ω => W s ω j) t n a = ∑ k ∈ Finset.range (2 ^ n),
      fun ω => a k ω * (W (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) ω j -
        W ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) ω j) := by
    funext ω; simp [itoStepSum, Finset.sum_apply]
  rw [heq]
  refine memLp_finsetSum' _ fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hΔ := (stdBrownian_memLp_two hW (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) j).sub
    (stdBrownian_memLp_two hW ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) j)
  refine hΔ.of_le_mul (c := C) ((ha k hk').mul hΔ.1) (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC k hk' ω) (abs_nonneg _)

/-- Localized Chebyshev bound for discrete Ito sums: the sum is large only if the discrete
quadratic variation of the integrand exceeds `δ`, or with probability at most `δ / ε²`. -/
theorem itoStepSum_local_chebyshev {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (n : ℕ) (j : Fin d)
    (c : ℕ → Ω → ℝ)
    (hc : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c k))
    (C : ℝ) (hC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c k ω| ≤ C) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) :
    P {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|} ≤
      ENNReal.ofReal (δ / ε ^ 2) +
      P {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) *
        ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)} := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  set h : ℝ := ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) with hhdef
  have hh : 0 ≤ h := NNReal.coe_nonneg _
  have hsm : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (stopCoef c h δ k) := by
    intro k hk
    exact stopCoef_measurable (m := completedBrownianPast P W (fun _ => x₀) _) c h δ k
      (fun i hi => (hc i (lt_of_le_of_lt hi hk)).mono
        (completedBrownianPast_mono P W _ (by gcongr)) le_rfl)
  have hsC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |stopCoef c h δ k ω| ≤ C := fun k hk ω =>
    (abs_stopCoef_le c h δ k ω).trans (hC k hk ω)
  have hiso := itoStepSum_isometry hW x₀ t n j (stopCoef c h δ) hsm C hsC
  have hL2 := itoStepSum_memLp hW t n j (stopCoef c h δ)
    (fun k hk => aestronglyMeasurable_of_completedPast hW x₀ _ (hsm k hk)) C hsC
  have hint : ∀ k ∈ Finset.range (2 ^ n), Integrable (fun ω => stopCoef c h δ k ω ^ 2) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine Integrable.of_bound
      ((aestronglyMeasurable_of_completedPast hW x₀ _ (hsm k hk')).pow 2) (C ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hsC k hk' ω) 2
  have hE : ∫ ω, (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2 ∂P ≤ δ := by
    rw [hiso]
    calc ∑ k ∈ Finset.range (2 ^ n), (∫ ω, stopCoef c h δ k ω ^ 2 ∂P) * h
        = (∫ ω, ∑ k ∈ Finset.range (2 ^ n), stopCoef c h δ k ω ^ 2 ∂P) * h := by
          rw [integral_finsetSum _ hint, Finset.sum_mul]
      _ = ∫ ω, (∑ k ∈ Finset.range (2 ^ n), stopCoef c h δ k ω ^ 2) * h ∂P := by
          rw [integral_mul_const]
      _ ≤ ∫ _ω, δ ∂P := integral_mono ((integrable_finsetSum _ hint).mul_const h)
          (integrable_const δ) (fun ω => stopCoef_sum_le c hh hδ _ ω)
      _ = δ := by simp
  have hsub : {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|} ⊆
      {ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ∪
      {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h} := by
    intro ω hω
    by_cases hq : (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h ≤ δ
    · left
      have heq : itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω =
          itoStepSum (fun s ω => W s ω j) t n c ω := by
        unfold itoStepSum
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [stopCoef_eq_of_le c hh hq (Finset.mem_range.1 hk)]
      show ε ^ 2 ≤ _
      rw [heq]
      calc ε ^ 2 ≤ |itoStepSum (fun s ω => W s ω j) t n c ω| ^ 2 :=
            pow_le_pow_left₀ hε.le hω 2
        _ = _ := sq_abs _
    · right; exact lt_of_not_ge hq
  have hA : P {ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ≤
      ENNReal.ofReal (δ / ε ^ 2) := by
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun ω => sq_nonneg
        (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω)) hL2.integrable_sq (ε ^ 2)
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hε2, mul_comm]
    exact hm.trans hE
  calc P {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|}
      ≤ P ({ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ∪
          {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add_left hA _

/-- Discrete Ito sums whose integrands have discrete quadratic variation tending to zero in
probability tend to zero in probability. -/
theorem itoStepSum_tendstoInMeasure_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (j : Fin d)
    (c : ℕ → ℕ → Ω → ℝ)
    (hc : ∀ n k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c n k))
    (hC : ∀ n, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C)
    (hq : TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n => itoStepSum (fun s ω => W s ω j) t n (c n)) atTop
      (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hq ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall fun _ => le_top
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have he2top : e / 2 ≠ ⊤ := ENNReal.div_ne_top hetop (by norm_num)
  set δ : ℝ := (e / 2).toReal * ε ^ 2 with hδdef
  have hδpos : 0 < δ := mul_pos (ENNReal.toReal_pos he2.ne' he2top) (by positivity)
  have hδe : ENNReal.ofReal (δ / ε ^ 2) = e / 2 := by
    rw [hδdef, mul_div_cancel_right₀ _ (by positivity), ENNReal.ofReal_toReal he2top]
  have h2 := (ENNReal.tendsto_nhds_zero.1 (hq δ hδpos)) (e / 2) he2
  filter_upwards [h2] with n hn
  obtain ⟨C, hCn⟩ := hC n
  have hset : {ω | ε ≤ dist (itoStepSum (fun s ω => W s ω j) t n (c n) ω) 0} =
      {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n (c n) ω|} := by
    ext ω; simp
  rw [hset]
  calc _ ≤ ENNReal.ofReal (δ / ε ^ 2) +
        P {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
          ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)} :=
        itoStepSum_local_chebyshev hW x₀ t n j (c n) (hc n) C hCn hε hδpos.le
    _ ≤ e / 2 + e / 2 := by
        rw [hδe]
        refine add_le_add le_rfl (le_trans (measure_mono fun ω hω => ?_) hn)
        simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
        exact hω.le.trans (le_abs_self _)
    _ = e := ENNReal.add_halves e

end M5


section M5b

theorem tendstoInMeasure_zero_of_abs_le [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {F A B : ι → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hA : TendstoInMeasure P A l (fun _ => 0)) (hB : TendstoInMeasure P B l (fun _ => 0))
    (hF : ∀ i ω, |F i ω| ≤ K * (|A i ω| + |B i ω|)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hA hB ⊢
  intro ε hε
  have hε' : 0 < ε / (2 * K) := by positivity
  have hsum := (hA _ hε').add (hB _ hε')
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hF i ω
  have h2 : K * (|A i ω| + |B i ω|) < K * (ε / (2 * K) + ε / (2 * K)) :=
    mul_lt_mul_of_pos_left (add_lt_add hcon.1 hcon.2) hK
  have h3 : K * (ε / (2 * K) + ε / (2 * K)) = ε := by field_simp; ring
  linarith only [hω, h1, h2, h3]

theorem tendstoInMeasure_real_iff_sub [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f : ι → Ω → ℝ} {g : Ω → ℝ} :
    TendstoInMeasure P f l g ↔ TendstoInMeasure P (fun i ω => f i ω - g ω) l (fun _ => 0) := by
  simp only [tendstoInMeasure_iff_dist, Real.dist_eq, sub_zero]

theorem tendstoInMeasure_sub_real [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω - f' i ω) l (fun ω => g ω - g' ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf hf' ⊢
  refine tendstoInMeasure_zero_of_abs_le one_pos hf hf' fun i ω => ?_
  rw [one_mul, abs_le]
  constructor <;> linarith only [le_abs_self (f i ω - g ω), neg_abs_le (f i ω - g ω),
    le_abs_self (f' i ω - g' ω), neg_abs_le (f' i ω - g' ω)]

theorem itoStepValue_sub (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n a u ω - itoStepValue t n b u ω =
      itoStepValue t n (fun k ω => a k ω - b k ω) u ω := by
  unfold itoStepValue
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

theorem itoStepSum_sub (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t n a ω - itoStepSum W t n b ω =
      itoStepSum W t n (fun k ω => a k ω - b k ω) ω := by
  unfold itoStepSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]

theorem itoStepValue_sq (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    (itoStepValue t n c u ω) ^ 2 = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key : ∀ p q : ℕ, p < q →
      ((p : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ (q : ℝ) * t.val / (2 : ℝ) ^ n := by
    intro p q hpq
    have : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hT) h2.le
  unfold itoStepValue
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single k]
  · simp only [Set.indicator_apply, Set.mem_Ioc]; split_ifs <;> ring
  · intro l _ hlk
    split_ifs with h1 h2 <;> try ring
    exfalso
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · linarith only [key l k hlt, h1.1, h2.2]
    · linarith only [key k l hgt, h1.2, h2.1]
  · intro hk'; exact absurd hk hk'

theorem intervalIntegrable_indicator_Ioc_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ioc a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ioc

theorem itoStepValue_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => itoStepValue t n c u ω) volume 0 t.val := by
  have heq : (fun u => itoStepValue t n c u ω) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_eq_sum_indicator]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

theorem itoStepValue_sq_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue t n c u ω) ^ 2) volume 0 t.val := by
  have heq : (fun u => (itoStepValue t n c u ω) ^ 2) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_sq]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

theorem itoStepValue_sq_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω) ^ 2 =
      (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_sq]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith only [this]
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

end M5b

section M5c
variable [MeasurableSpace Ω]

/-- The local Ito integral of `HasBrownianItoIntegral` is unique up to null sets at each time,
for integrands with continuous paths. -/
theorem hasBrownianItoIntegral_ae_unique {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J J' : ℝ≥0 → Ω → ℝ}
    (hH : ∀ ω, Continuous (fun u : ℝ => H u.toNNReal ω))
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J')
    (t : ℝ≥0) : J t =ᵐ[P] J' t := by
  obtain ⟨a, ham, haC, haH, haJ⟩ := hJ.2 t
  obtain ⟨b, hbm, hbC, hbH, hbJ⟩ := hJ'.2 t
  have hT : (0 : ℝ) ≤ t.val := t.2
  let c : ℕ → ℕ → Ω → ℝ := fun n k ω => a n k ω - b n k ω
  have hcm : ∀ n k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c n k) := fun n k hk =>
    (ham n k hk).sub (hbm n k hk)
  have hcC : ∀ n, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C := by
    intro n
    obtain ⟨C1, h1⟩ := haC n
    obtain ⟨C2, h2⟩ := hbC n
    refine ⟨C1 + C2, fun k hk ω => ?_⟩
    have h1' := abs_le.1 (h1 k hk ω)
    have h2' := abs_le.1 (h2 k hk ω)
    exact abs_le.2 ⟨by simp only [c]; linarith only [h1'.1, h2'.2],
      by simp only [c]; linarith only [h1'.2, h2'.1]⟩
  -- integrability of the squared errors
  have hfi : ∀ (n : ℕ) (e : ℕ → Ω → ℝ) ω, IntervalIntegrable
      (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) volume 0 t.val := by
    intro n e ω
    have h1 := itoStepValue_sq_intervalIntegrable t n e ω
    have h2 := (itoStepValue_intervalIntegrable t n e ω).mul_continuousOn (hH ω).continuousOn
    have h3 := ((hH ω).pow 2).intervalIntegrable (μ := volume) 0 t.val
    have h4 := (h1.sub (h2.const_mul 2)).add h3
    have heq : (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) = fun u =>
        (itoStepValue t n e u ω) ^ 2 - 2 * (itoStepValue t n e u ω * H u.toNNReal ω) +
          H u.toNNReal ω ^ 2 := by
      funext u; ring
    rw [heq]; exact h4
  have hq : TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_zero_of_abs_le (K := 2) two_pos haH hbH (fun n ω => ?_)
    rw [← itoStepValue_sq_integral]
    have hfa := hfi n (a n) ω
    have hfb := hfi n (b n) ω
    have hnn : ∀ e : ℕ → Ω → ℝ, 0 ≤ ∫ u in (0 : ℝ)..t.val,
        (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2 :=
      fun e => intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)),
      abs_of_nonneg (hnn (a n)), abs_of_nonneg (hnn (b n))]
    calc ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (c n) u ω) ^ 2
        ≤ ∫ u in (0 : ℝ)..t.val, (2 * (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2 +
            2 * (itoStepValue t n (b n) u ω - H u.toNNReal ω) ^ 2) := by
          refine intervalIntegral.integral_mono_on hT
            (itoStepValue_sq_intervalIntegrable t n (c n) ω)
            ((hfa.const_mul 2).add (hfb.const_mul 2)) (fun u _ => ?_)
          rw [← itoStepValue_sub]
          linarith only [sq_nonneg (itoStepValue t n (a n) u ω - H u.toNNReal ω +
            (itoStepValue t n (b n) u ω - H u.toNNReal ω))]
      _ = 2 * ((∫ u in (0 : ℝ)..t.val, (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2) +
            ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (b n) u ω - H u.toNNReal ω) ^ 2) := by
          rw [intervalIntegral.integral_add (hfa.const_mul 2) (hfb.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
          ring
  have hS := itoStepSum_tendstoInMeasure_zero hW x₀ t j c hcm hcC hq
  have hsub := tendstoInMeasure_sub_real haJ hbJ
  have hsub' : TendstoInMeasure P (fun n => itoStepSum (fun s ω => W s ω j) t n (c n)) atTop
      (fun ω => J t ω - J' t ω) := by
    convert hsub using 2 with n
    funext ω
    exact (itoStepSum_sub _ t n (a n) (b n) ω).symm
  have hae := tendstoInMeasure_ae_unique hsub' hS
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.1 hω

end M5c


section M6refine

theorem sum_range_mul_block {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N K : ℕ) :
    ∑ j ∈ Finset.range (N * K), f j =
      ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range K, f (k * K + r) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A step sum on the grid of mesh `t / 2^n` is the step sum on the finer grid `t / 2^(n+m)`
with the coefficients held constant on each coarse cell. -/
theorem itoStepSum_refine (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n m : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t n a ω = itoStepSum W t (n + m) (fun k => a (k / 2 ^ m)) ω := by
  unfold itoStepSum
  rw [show (2 : ℕ) ^ (n + m) = 2 ^ n * 2 ^ m from pow_add 2 n m, sum_range_mul_block]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdiv : ∀ r ∈ Finset.range (2 ^ m), (k * 2 ^ m + r) / 2 ^ m = k := by
    intro r hr
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt (Finset.mem_range.1 hr), zero_add]
  set g : ℕ → ℝ := fun r => W (((k * 2 ^ m + r : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m)) ω
    with hg
  have hterm : ∀ r ∈ Finset.range (2 ^ m),
      a ((k * 2 ^ m + r) / 2 ^ m) ω *
        (W ((((k * 2 ^ m + r : ℕ) : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ (n + m)) ω -
          W (((k * 2 ^ m + r : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m)) ω) =
      a k ω * (g (r + 1) - g r) := by
    intro r hr
    have ht : ((k * 2 ^ m + r : ℕ) : ℝ≥0) + 1 = ((k * 2 ^ m + (r + 1) : ℕ) : ℝ≥0) := by
      push_cast; ring
    rw [hdiv r hr, ht]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_range_sub]
  have h1 : ((k * 2 ^ m + 2 ^ m : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m) =
      ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n := by
    push_cast; rw [pow_add]; field_simp; try ring
  have h0 : ((k * 2 ^ m + 0 : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m) =
      (k : ℝ≥0) * t / (2 : ℝ≥0) ^ n := by
    push_cast; rw [pow_add]; field_simp; try ring
  simp only [hg, h1, h0]

end M6refine


section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

/-- Left-point coefficients of a process on the dyadic grid of mesh `t / 2^n`. -/
noncomputable def leftCoef (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  H (dyTime t n k) ω

/-- Oscillation event: two dyadic times in `[0,t]` at distance at most `δ` at which `H` differs
by more than `η`. -/
def oscSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (δ η : ℝ) : Set Ω :=
  ⋃ p : (ℕ × ℕ) × (ℕ × ℕ), {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
    |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
    η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|}

theorem dyTime_le (t : ℝ≥0) {N j : ℕ} (h : j ≤ 2 ^ N) : dyTime t N j ≤ t := by
  unfold dyTime
  rw [div_le_iff₀ (by positivity)]
  calc (j : ℝ≥0) * t ≤ (2 : ℝ≥0) ^ N * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
    _ = t * 2 ^ N := mul_comm _ _

theorem dyTime_coarse (t : ℝ≥0) (n m k : ℕ) :
    dyTime t n (k / 2 ^ m) ≤ dyTime t (n + m) k ∧
    (dyTime t (n + m) k : ℝ) - dyTime t n (k / 2 ^ m) ≤ (t : ℝ) / 2 ^ n := by
  have hk := Nat.div_add_mod k (2 ^ m)
  have hr := Nat.mod_lt k (show 0 < 2 ^ m by positivity)
  set q := k / 2 ^ m
  set r := k % 2 ^ m
  have hkR : (k : ℝ) = 2 ^ m * q + r := by exact_mod_cast hk.symm
  have hrR : (r : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast hr
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have e1 : (dyTime t (n + m) k : ℝ) = (k : ℝ) * t / (2 ^ n * 2 ^ m) := by
    simp [dyTime, pow_add]
  have e2 : (dyTime t n q : ℝ) = (q : ℝ) * t / 2 ^ n := by simp [dyTime]
  have key : (dyTime t (n + m) k : ℝ) - dyTime t n q = (r : ℝ) * t / (2 ^ n * 2 ^ m) := by
    rw [e1, e2, hkR]; field_simp; try ring
  constructor
  · rw [← NNReal.coe_le_coe, ← sub_nonneg, key]; positivity
  · rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right (show (r : ℝ) ≤ 2 ^ m by linarith) ht
    calc (r : ℝ) * t * 2 ^ n ≤ 2 ^ m * t * 2 ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = t * (2 ^ n * 2 ^ m) := by ring

theorem oscSet_mono (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (η : ℝ) :
    oscSet H t δ η ⊆ oscSet H t δ' η := by
  intro ω hω
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
  exact Set.mem_iUnion.2 ⟨p, hp.1, hp.2.1, hp.2.2.1.trans hδ, hp.2.2.2⟩

theorem oscSet_nullMeasurable [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (t : ℝ≥0) (δ η : ℝ) :
    NullMeasurableSet (oscSet H t δ η) P := by
  refine NullMeasurableSet.iUnion fun p => ?_
  by_cases hc : p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
      |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ
  · have heq : {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
        |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
        η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} =
        {ω | η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} := by
      ext ω
      exact ⟨fun h => h.2.2.2, fun h => ⟨hc.1, hc.2.1, hc.2.2, h⟩⟩
    rw [heq]
    exact AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
      (continuous_abs.comp_aestronglyMeasurable ((hHm _).sub (hHm _)))
  · have heq : {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
        |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
        η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} = ∅ := by
      ext ω
      exact ⟨fun h => absurd ⟨h.1, h.2.1, h.2.2.1⟩ hc, fun h => h.elim⟩
    rw [heq]
    exact nullMeasurableSet_empty

theorem iInter_oscSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  have huc : UniformContinuousOn (fun s => H s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hHc ω).continuousOn
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / δ)
  have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have htn : (t : ℝ) / 2 ^ n < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    have hnδ := mul_lt_mul_of_pos_right h2n hδ
    linarith only [hn, hnδ]
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  exact absurd hp4 (not_lt.2 this.le)

theorem oscSet_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => P (oscSet H t ((t : ℝ) / 2 ^ n) η)) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => oscSet H t ((t : ℝ) / 2 ^ n) η) := by
    intro n n' hnn'
    exact oscSet_mono H t (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hnn')) η
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun n => oscSet_nullMeasurable hHm t ((t : ℝ) / 2 ^ n) η) hanti ⟨0, measure_ne_top _ _⟩
  rw [iInter_oscSet_eq_empty hHc t hη, measure_empty] at this
  exact this

end M6osc


section M6cauchy
variable [MeasurableSpace Ω]

/-- L² Cauchy estimate for left-point Ito sums of a bounded adapted process: refining the grid
from `t/2^n` to `t/2^(n+m)` changes the sum by at most `η² t + 4K² t P(osc)` in mean square. -/
theorem leftPoint_cauchy_bound {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ s ω, |H s ω| ≤ K) (t : ℝ≥0) (n m : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    ∫ ω, (itoStepSum (fun s ω => W s ω j) t (n + m) (leftCoef H t (n + m)) ω -
        itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω) ^ 2 ∂P ≤
      η ^ 2 * t + 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  let D : ℕ → Ω → ℝ := fun k ω => leftCoef H t (n + m) k ω - leftCoef H t n (k / 2 ^ m) ω
  have hdiff : ∀ ω, itoStepSum (fun s ω => W s ω j) t (n + m) (leftCoef H t (n + m)) ω -
      itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω =
      itoStepSum (fun s ω => W s ω j) t (n + m) D ω := by
    intro ω
    rw [itoStepSum_refine _ t n m (leftCoef H t n) ω, itoStepSum_sub]
  simp_rw [hdiff]
  have hDm : ∀ k : ℕ, k < 2 ^ (n + m) → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m))] (D k) := by
    intro k _
    exact (hHm (dyTime t (n + m) k)).sub ((hHm (dyTime t n (k / 2 ^ m))).mono
      (completedBrownianPast_mono P W _ (dyTime_coarse t n m k).1) le_rfl)
  have hDb : ∀ k : ℕ, k < 2 ^ (n + m) → ∀ ω, |D k ω| ≤ 2 * K := by
    intro k _ ω
    have h1 := abs_le.1 (hHb (dyTime t (n + m) k) ω)
    have h2 := abs_le.1 (hHb (dyTime t n (k / 2 ^ m)) ω)
    exact abs_le.2 ⟨by simp only [D, leftCoef]; linarith only [h1.1, h2.2],
      by simp only [D, leftCoef]; linarith only [h1.2, h2.1]⟩
  rw [itoStepSum_isometry hW x₀ t (n + m) j D hDm (2 * K) hDb]
  have hint : ∀ k ∈ Finset.range (2 ^ (n + m)), Integrable (fun ω => D k ω ^ 2) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine Integrable.of_bound
      ((aestronglyMeasurable_of_completedPast hW x₀ _ (hDm k hk')).pow 2) ((2 * K) ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDb k hk' ω) 2
  set h : ℝ := ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ) with hhdef
  have hh : 0 ≤ h := NNReal.coe_nonneg _
  have hNh : ((2 ^ (n + m) : ℕ) : ℝ) * h = t := by
    rw [hhdef]; push_cast; field_simp
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  set O := toMeasurable P (oscSet H t ((t : ℝ) / 2 ^ n) η) with hO
  have hOm : MeasurableSet O := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h ≤
      η ^ 2 * t + 4 * K ^ 2 * t * O.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ O
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have hs : ∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2 ≤
          (Finset.range (2 ^ (n + m))).card • ((2 * K) ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        have := hDb k (Finset.mem_range.1 hk) ω
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      have := mul_le_mul_of_nonneg_right hs hh
      calc (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h
          ≤ ((2 ^ (n + m) : ℕ) : ℝ) * (2 * K) ^ 2 * h := this
        _ = 4 * K ^ 2 * (((2 ^ (n + m) : ℕ) : ℝ) * h) := by ring
        _ = 4 * K ^ 2 * t := by rw [hNh]
        _ ≤ η ^ 2 * t + 4 * K ^ 2 * t := le_add_of_nonneg_left (by positivity)
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hno : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h' => hω (subset_toMeasurable _ _ h')
      have hs : ∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2 ≤
          (Finset.range (2 ^ (n + m))).card • (η ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        have hDk : |D k ω| ≤ η := by
          by_contra hcon
          push Not at hcon
          refine hno (Set.mem_iUnion.2 ⟨((n + m, k), (n, k / 2 ^ m)), hk'.le, ?_, ?_, hcon⟩)
          · show k / 2 ^ m ≤ 2 ^ n
            rw [pow_add] at hk'
            exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hk' |>.le
          · show |(dyTime t (n + m) k : ℝ) - dyTime t n (k / 2 ^ m)| ≤ (t : ℝ) / 2 ^ n
            have hc := dyTime_coarse t n m k
            rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hc.1))]
            exact hc.2
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hDk 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      calc (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h
          ≤ ((2 ^ (n + m) : ℕ) : ℝ) * η ^ 2 * h := mul_le_mul_of_nonneg_right hs hh
        _ = η ^ 2 * (((2 ^ (n + m) : ℕ) : ℝ) * h) := by ring
        _ = η ^ 2 * t := by rw [hNh]
  have hOreal : P.real O = P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
    simp only [measureReal_def, hO, measure_toMeasurable]
  have hIi : Integrable (fun ω => 4 * K ^ 2 * (t : ℝ) * O.indicator 1 ω) P :=
    ((integrable_indicator_iff hOm).2 (integrable_const (1 : ℝ)).integrableOn).const_mul _
  calc ∑ k ∈ Finset.range (2 ^ (n + m)), (∫ ω, D k ω ^ 2 ∂P) * h
      = ∫ ω, (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h ∂P := by
        rw [integral_mul_const, integral_finsetSum _ hint, Finset.sum_mul]
    _ ≤ ∫ ω, (η ^ 2 * t + 4 * K ^ 2 * t * O.indicator 1 ω) ∂P :=
        integral_mono ((integrable_finsetSum _ hint).mul_const h)
          ((integrable_const _).add hIi) hpt
    _ = η ^ 2 * t + 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
        rw [integral_add (integrable_const _) hIi, integral_const, integral_const_mul,
          integral_indicator_one hOm, hOreal]
        simp

end M6cauchy


section M6limit
variable [MeasurableSpace Ω]

theorem dist_toLp_lt_of_integral_sq {P : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) {ε : ℝ} (hε : 0 < ε) (h : ∫ ω, (f ω - g ω) ^ 2 ∂P < ε ^ 2) :
    dist (hf.toLp f) (hg.toLp g) < ε := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp,
    (hf.sub hg).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hA : ∫ ω, ‖(f - g) ω‖ ^ (ENNReal.toReal 2) ∂P = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
    congr 1; funext ω; simp [Real.norm_eq_abs, sq_abs]
  rw [hA]
  have hnn : 0 ≤ ∫ ω, (f ω - g ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  have h2 : (ENNReal.toReal 2)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [h2, ← Real.sqrt_eq_rpow, Real.sqrt_lt' hε]
  exact h

/-- Left-point Ito sums of a bounded adapted process with continuous paths converge in
probability (indeed in `L²`). -/
theorem leftPoint_tendstoInMeasure {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ s ω, |H s ω| ≤ K) (t : ℝ≥0) :
    ∃ J : Ω → ℝ, TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n)) atTop J := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hS : ∀ n, MemLp (itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n)) 2 P := fun n =>
    itoStepSum_memLp hW t n j _
      (fun k _ => aestronglyMeasurable_of_completedPast hW x₀ _ (hHm (dyTime t n k))) K
      (fun k _ ω => hHb _ ω)
  let f : ℕ → Lp ℝ 2 P := fun n => (hS n).toLp _
  have hcau : CauchySeq f := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hε2 : 0 < ε ^ 2 := by positivity
    have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
    set η : ℝ := min 1 (ε ^ 2 / 2 / ((t : ℝ) + 1)) with hηdef
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    have hηt : η ^ 2 * t < ε ^ 2 / 2 := by
      have h1 : η ≤ 1 := min_le_left _ _
      have h2 : η ≤ ε ^ 2 / 2 / ((t : ℝ) + 1) := min_le_right _ _
      have h3 : η ^ 2 ≤ η := by linarith only [mul_le_mul_of_nonneg_right h1 hηpos.le]
      have h4 : η * ((t : ℝ) + 1) ≤ ε ^ 2 / 2 := by rwa [le_div_iff₀ (by positivity)] at h2
      linarith only [mul_le_mul_of_nonneg_right h3 ht, h4, hηpos]
    have hosc := oscSet_tendsto
      (fun s => aestronglyMeasurable_of_completedPast hW x₀ s (hHm s)) hHc t hηpos
    have hosc' : Tendsto (fun n : ℕ => P.real (oscSet H t ((t : ℝ) / 2 ^ n) η)) atTop
        (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hosc
      simpa [measureReal_def, Function.comp_def] using this
    have hev := hosc'.eventually (gt_mem_nhds
      (show (0 : ℝ) < (ε ^ 2 / 2) / (4 * K ^ 2 * t + 1) by positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine dist_toLp_lt_of_integral_sq (hS _) (hS _) hε ?_
    have hb := leftPoint_cauchy_bound hW x₀ j hHm hK hHb t N m hηpos.le
    have hpN := hN N le_rfl
    have hq : 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ N) η) < ε ^ 2 / 2 := by
      have hc : 0 ≤ 4 * K ^ 2 * (t : ℝ) := by positivity
      have hr : 0 ≤ P.real (oscSet H t ((t : ℝ) / 2 ^ N) η) := measureReal_nonneg
      rw [lt_div_iff₀ (by positivity)] at hpN
      linarith only [hpN, hr]
    linarith only [hb, hηt, hq]
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcau
  exact ⟨F, (tendstoInMeasure_of_tendsto_Lp hF).congr_left (fun n => (hS n).coeFn_toLp)⟩

end M6limit


section M6trunc

/-- Truncation of a process at level `R`. -/
noncomputable def clampH (H : ℝ≥0 → Ω → ℝ) (R : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  max (-R) (min (H s ω) R)

theorem abs_clampH_le (H : ℝ≥0 → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (s : ℝ≥0) (ω : Ω) :
    |clampH H R s ω| ≤ R := by
  unfold clampH
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith only [hR]) (min_le_right _ _)⟩

theorem clampH_eq_of_abs_le (H : ℝ≥0 → Ω → ℝ) {R : ℝ} {s : ℝ≥0} {ω : Ω} (h : |H s ω| ≤ R) :
    clampH H R s ω = H s ω := by
  unfold clampH
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem clampH_continuous {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω) (R : ℝ)
    (ω : Ω) : Continuous fun s => clampH H R s ω := by
  unfold clampH
  exact continuous_const.max ((hHc ω).min continuous_const)

theorem clampH_measurable {m : MeasurableSpace Ω} {H : ℝ≥0 → Ω → ℝ} {s : ℝ≥0}
    (h : Measurable[m] (H s)) (R : ℝ) : Measurable[m] (clampH H R s) := by
  unfold clampH
  exact measurable_const.max (h.min measurable_const)

/-- Event that `|H|` exceeds `R` at some dyadic time of `[0,t]`. -/
def bigSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (R : ℝ) : Set Ω :=
  ⋃ p : ℕ × ℕ, {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|}

theorem abs_le_of_not_mem_bigSet {H : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {R : ℝ} {ω : Ω}
    (h : ω ∉ bigSet H t R) {N i : ℕ} (hi : i ≤ 2 ^ N) : |H (dyTime t N i) ω| ≤ R := by
  by_contra hc
  exact h (Set.mem_iUnion.2 ⟨(N, i), hi, lt_of_not_ge hc⟩)

theorem bigSet_nullMeasurable [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (t : ℝ≥0) (R : ℝ) :
    NullMeasurableSet (bigSet H t R) P := by
  refine NullMeasurableSet.iUnion fun p => ?_
  by_cases hc : p.2 ≤ 2 ^ p.1
  · have heq : {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|} =
        {ω | R < |H (dyTime t p.1 p.2) ω|} := by
      ext ω; exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
    rw [heq]
    exact AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
      (continuous_abs.comp_aestronglyMeasurable (hHm _))
  · have heq : {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|} = ∅ := by
      ext ω; exact ⟨fun h => absurd h.1 hc, fun h => h.elim⟩
    rw [heq]
    exact nullMeasurableSet_empty

theorem iInter_bigSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) : (⋂ R : ℕ, bigSet H t R) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hHc ω).continuousOn
  obtain ⟨R, hR⟩ := exists_nat_gt C
  obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.1 (hall R)
  have := hC _ ⟨zero_le, dyTime_le t hp1⟩
  rw [Real.norm_eq_abs] at this
  linarith

theorem bigSet_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) :
    Tendsto (fun R : ℕ => P (bigSet H t R)) atTop (𝓝 0) := by
  have hanti : Antitone (fun R : ℕ => bigSet H t R) := by
    intro R R' hRR' ω hω
    obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.1 hω
    exact Set.mem_iUnion.2 ⟨p, hp1, lt_of_le_of_lt (by exact_mod_cast hRR') hp2⟩
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun R : ℕ => bigSet_nullMeasurable hHm t (R : ℝ)) hanti ⟨0, measure_ne_top _ _⟩
  rw [iInter_bigSet_eq_empty hHc t, measure_empty] at this
  exact this

/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht, mul_comm (2 ^ n : ℝ)]; exact mul_le_mul_of_nonneg_right hu.2 h2.le
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith only [this, hkR]
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith only [hlt]
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith only [hge]
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1', this, hlo]
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1, this, hhi]
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'

/-- Off the oscillation event of mesh `t/2^n`, `H` at the left grid point `t_k` is within `η` of
`H u` for every `u ∈ [t_k, t_{k+1}]` (dyadic approximation of `u` from the left + continuity). -/
theorem abs_H_sub_le_of_not_mem_oscSet {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n k : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω}
    (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η) (hk : k < 2 ^ n) {u : ℝ} (hu0 : 0 ≤ u)
    (hlo : (k : ℝ) * t.val / 2 ^ n ≤ u) (hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n)
    (hut : u ≤ t.val) :
    |H (dyTime t n k) ω - H u.toNNReal ω| ≤ η := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · have hu : u = 0 := le_antisymm (h0 ▸ hut) hu0
    have hd : dyTime t n k = 0 := by
      have : t = 0 := NNReal.coe_eq_zero.1 h0.symm
      simp [dyTime, this]
    rw [hu, hd, Real.toNNReal_zero, sub_self, abs_zero]
    exact hη
  set y : ℕ → ℝ := fun m => u * 2 ^ (m + n) / t.val with hy
  set s : ℕ → ℝ≥0 := fun m => dyTime t (m + n) ⌊y m⌋₊ with hs
  have hsR : ∀ m, (s m : ℝ) = (⌊y m⌋₊ : ℝ) * t.val / 2 ^ (m + n) := fun m => by
    simp [hs, dyTime]
  have hy0 : ∀ m, 0 ≤ y m := fun m => by simp only [hy]; positivity
  have hyt : ∀ m, y m * t.val / 2 ^ (m + n) = u := fun m => by
    simp only [hy]; field_simp
  have hs_le : ∀ m, (s m : ℝ) ≤ u := fun m => by
    rw [hsR, ← hyt m]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le (hy0 m)) ht)
      (by positivity)
  have hs_gt : ∀ m, u - t.val / 2 ^ (m + n) ≤ (s m : ℝ) := fun m => by
    have h1 := Nat.lt_floor_add_one (y m)
    have h3 : u - t.val / 2 ^ (m + n) = (y m - 1) * t.val / 2 ^ (m + n) := by
      rw [← hyt m]; field_simp; try ring
    rw [hsR, h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [h1]) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      have h2m := mul_le_mul_of_nonneg_left hlo (pow_pos (two_pos (α := ℝ)) m).le
      linarith only [h2m]
    have hfl : ((k * 2 ^ m : ℕ) : ℝ) ≤ (⌊y m⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor hkm
    have e : (dyTime t n k : ℝ) = ((k * 2 ^ m : ℕ) : ℝ) * t.val / 2 ^ (m + n) := by
      simp only [dyTime]; push_cast; rw [pow_add]; field_simp; try rfl
    rw [e, hsR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfl ht) (by positivity)
  have hdk : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by simp [dyTime]
  have hbound : ∀ m, |H (dyTime t n k) ω - H (s m) ω| ≤ η := fun m => by
    by_contra hc
    refine hω (Set.mem_iUnion.2 ⟨((n, k), (m + n, ⌊y m⌋₊)), hk.le, ?_, ?_, lt_of_not_ge hc⟩)
    · refine Nat.floor_le_of_le ?_
      simp only [hy]
      rw [div_le_iff₀ hpos]; push_cast
      exact (mul_le_mul_of_nonneg_right hut (by positivity)).trans_eq (mul_comm _ _)
    · show |(dyTime t n k : ℝ) - (s m : ℝ)| ≤ (t : ℝ) / 2 ^ n
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hs_ge m])]
      have hcell : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by
        ring
      have hsm := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith only [hcell, hsm, hhi]
  have hreal : Tendsto (fun m => (s m : ℝ)) atTop (𝓝 u) := by
    have hpow : Tendsto (fun m : ℕ => t.val / 2 ^ (m + n)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))).comp
        (tendsto_add_atTop_nat n)
      exact Tendsto.div_atTop tendsto_const_nhds h
    have hlow : Tendsto (fun m : ℕ => u - t.val / 2 ^ (m + n)) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_gt hs_le
  have hnn : Tendsto s atTop (𝓝 u.toNNReal) := by
    have := (continuous_real_toNNReal.tendsto u).comp hreal
    simpa [Function.comp_def] using this
  have hcont : Continuous fun x : ℝ≥0 => |H (dyTime t n k) ω - H x ω| :=
    (continuous_const.sub (hHc ω)).abs
  exact le_of_tendsto' ((hcont.tendsto u.toNNReal).comp hnn) (fun m => hbound m)

/-- Pathwise approximation: off the oscillation event, a step process with the left-point values
of `H` is uniformly `η`-close to `H` on `(0,t]`, so its integrated squared error is at most
`η² t`. -/
theorem integral_stepValue_sub_sq_le {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω} (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η)
    {c : ℕ → Ω → ℝ} (hc : ∀ k < 2 ^ n, c k ω = H (dyTime t n k) ω) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω - H u.toNNReal ω) ^ 2 ≤ η ^ 2 * t.val := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖(itoStepValue t n c u ω - H u.toNNReal ω) ^ 2‖ ≤ η ^ 2 := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ := itoStepValue_eq_cell t n c hu ω
    rw [hval, hc k hk, Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_H_sub_le_of_not_mem_oscSet hHc t n k hη hω hk hu.1.le hlo.le hhi hu.2) 2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- The approximation clause of `HasBrownianItoIntegral` for the truncated left-point
coefficients `clamp_n (H t_k)` of a continuous process. -/
theorem clampLeft_approx [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) :
    TendstoInMeasure P (fun (n : ℕ) ω => ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (leftCoef (clampH H n) t n) u ω - H u.toNNReal ω) ^ 2)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have ht : (0 : ℝ) ≤ t.val := t.2
  set η : ℝ := min 1 (ε / (2 * (t.val + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hηt : η ^ 2 * t.val < ε := by
    have h1 : η ≤ 1 := min_le_left _ _
    have h2 : η ≤ ε / (2 * (t.val + 1)) := min_le_right _ _
    have h3 : η ^ 2 * t.val ≤ η * t.val := by
      have : η ^ 2 ≤ η := by linarith only [mul_le_mul_of_nonneg_right h1 hη.le]
      exact mul_le_mul_of_nonneg_right this ht
    have h4 : η * t.val ≤ ε / (2 * (t.val + 1)) * t.val := mul_le_mul_of_nonneg_right h2 ht
    have h5 : ε / (2 * (t.val + 1)) * t.val < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; linarith only [mul_nonneg hε.le ht, hε]
    linarith only [h3, h4, h5]
  have hsum := (oscSet_tendsto hHm hHc t hη).add (bigSet_tendsto hHm hHc t)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  have hc : ∀ k < 2 ^ n, leftCoef (clampH H n) t n k ω = H (dyTime t n k) ω := fun k hk =>
    clampH_eq_of_abs_le H (abs_le_of_not_mem_bigSet hcon.2 hk.le)
  have hle := integral_stepValue_sub_sq_le hHc t n hη.le hcon.1 hc
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (leftCoef (clampH H n) t n) u ω - H u.toNNReal ω) ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun u _ => sq_nonneg _)
  rw [abs_of_nonneg hnn] at hω
  linarith only [hω, hle, hηt]

/-- Limits in probability of two sequences that agree on a set `A` agree a.e. on `A`. -/
theorem tendstoInMeasure_ae_eq_on [MeasurableSpace Ω] {P : Measure Ω} {f f' : ℕ → Ω → ℝ}
    {g g' : Ω → ℝ} {A : Set Ω} (hf : TendstoInMeasure P f atTop g)
    (hf' : TendstoInMeasure P f' atTop g') (hA : ∀ n, ∀ ω ∈ A, f n ω = f' n ω) :
    ∀ᵐ ω ∂P, ω ∈ A → g ω = g' ω := by
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_sub_real hf hf').exists_seq_tendsto_ae
  filter_upwards [hns] with ω hω hωA
  have h0 : Tendsto (fun i => f (ns i) ω - f' (ns i) ω) atTop (𝓝 0) := by
    simp only [hA _ ω hωA, sub_self]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hω h0
  linarith

/-- Localization: `f n → J` in probability if, off sets of arbitrarily small measure, `f n`
eventually coincides with a sequence converging to a limit that equals `J` a.e. there. -/
theorem tendstoInMeasure_of_local [MeasurableSpace Ω] {P : Measure Ω} {f : ℕ → Ω → ℝ}
    {J : Ω → ℝ}
    (h : ∀ δ : ℝ≥0∞, 0 < δ → ∃ B : Set Ω, P B ≤ δ ∧ ∃ g : ℕ → Ω → ℝ, ∃ G : Ω → ℝ,
      TendstoInMeasure P g atTop G ∧ (∀ᶠ n in atTop, ∀ ω ∉ B, f n ω = g n ω) ∧
      (∀ᵐ ω ∂P, ω ∉ B → J ω = G ω)) :
    TendstoInMeasure P f atTop J := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨B, hB, g, G, hg, hfg, hJG⟩ := h (δ / 2) hδ2
  rw [tendstoInMeasure_iff_dist] at hg
  have hg' := (ENNReal.tendsto_nhds_zero.1 (hg ε hε)) (δ / 2) hδ2
  rw [ae_iff] at hJG
  filter_upwards [hg', hfg] with n hn hfn
  calc P {ω | ε ≤ dist (f n ω) (J ω)}
      ≤ P (B ∪ {ω | ε ≤ dist (g n ω) (G ω)} ∪ {ω | ¬(ω ∉ B → J ω = G ω)}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωB : ω ∈ B
        · exact Or.inl (Or.inl hωB)
        by_cases hJ : J ω = G ω
        · refine Or.inl (Or.inr ?_)
          simp only [Set.mem_setOf_eq] at hω ⊢
          rwa [← hfn ω hωB, ← hJ]
        · exact Or.inr (fun h => hJ (h hωB))
    _ ≤ P B + P {ω | ε ≤ dist (g n ω) (G ω)} + P {ω | ¬(ω ∉ B → J ω = G ω)} :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 + 0 := by rw [hJG]; gcongr
    _ = δ := by rw [add_zero, ENNReal.add_halves]

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate, in the sense of `HasBrownianItoIntegral` (truncated left-point
sums; localization by truncation `clamp_R H` on the events `{sup |H| ≤ R}`). -/
theorem exists_hasBrownianItoIntegral_clamp {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J ∧ ∀ t, TendstoInMeasure P
        (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop (J t) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  have key : ∀ t : ℝ≥0, ∃ J : Ω → ℝ, TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop J := by
    intro t
    have hJR : ∀ R : ℕ, ∃ JR : Ω → ℝ, TendstoInMeasure P
        (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R) t n)) atTop JR :=
      fun R => leftPoint_tendstoInMeasure hW x₀ j (fun s => clampH_measurable (hHm s) (R : ℝ))
        (clampH_continuous hHc (R : ℝ)) (Nat.cast_nonneg R)
        (abs_clampH_le H (Nat.cast_nonneg R)) t
    choose JR hJR using hJR
    have hagree : ∀ R R' : ℕ, R ≤ R' → ∀ n, ∀ ω ∉ bigSet H t R,
        itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R) t n) ω =
          itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R') t n) ω := by
      intro R R' hRR' n ω hω
      unfold itoStepSum
      refine Finset.sum_congr rfl fun k hk => ?_
      have hb := abs_le_of_not_mem_bigSet hω (N := n) (i := k) (Finset.mem_range.1 hk).le
      have hb' : |H (dyTime t n k) ω| ≤ (R' : ℝ) := hb.trans (by exact_mod_cast hRR')
      simp only [leftCoef, clampH_eq_of_abs_le H hb, clampH_eq_of_abs_le H hb']
    have hae : ∀ᵐ ω ∂P, ∀ R R' : ℕ, R ≤ R' → ω ∉ bigSet H t R → JR R ω = JR R' ω := by
      rw [ae_all_iff]; intro R; rw [ae_all_iff]; intro R'
      by_cases hRR : R ≤ R'
      · filter_upwards [tendstoInMeasure_ae_eq_on (A := (bigSet H t R)ᶜ) (hJR R) (hJR R')
          (fun n ω hω => hagree R R' hRR n ω hω)] with ω hω _ h2 using hω h2
      · exact Eventually.of_forall fun ω h => absurd h hRR
    have hex : ∀ ω, ∃ R : ℕ, ω ∉ bigSet H t R := by
      intro ω
      by_contra hc
      push Not at hc
      have hmem : ω ∈ ⋂ R : ℕ, bigSet H t R := Set.mem_iInter.2 hc
      rw [iInter_bigSet_eq_empty hHc t] at hmem
      exact hmem
    classical
    refine ⟨fun ω => JR (Nat.find (hex ω)) ω, tendstoInMeasure_of_local fun δ hδ => ?_⟩
    obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHae hHc t)) δ hδ).exists
    refine ⟨bigSet H t R, hR, _, JR R, hJR R, ?_, ?_⟩
    · filter_upwards [eventually_ge_atTop R] with n hn ω hω
      exact (hagree R n hn n ω hω).symm
    · filter_upwards [hae] with ω hω hωB
      exact hω _ _ (Nat.find_min' _ hωB) (Nat.find_spec (hex ω))
  choose J hJ using key
  refine ⟨J, ⟨fun t ω => ?_, fun t => ⟨fun n k => leftCoef (clampH H n) t n k, ?_, ?_, ?_, hJ t⟩⟩, hJ⟩
  · exact (((hHc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _
  · intro n k _
    exact clampH_measurable (hHm (dyTime t n k)) (n : ℝ)
  · intro n
    exact ⟨n, fun k _ ω => abs_clampH_le H (Nat.cast_nonneg n) _ ω⟩
  · exact clampLeft_approx hHae hHc t

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate. -/
theorem exists_hasBrownianItoIntegral {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J :=
  (exists_hasBrownianItoIntegral_clamp hW x₀ j hHm hHc).imp fun _ h => h.1

/-- Any Ito integral of a continuous adapted integrand is the limit in probability of the
truncated left-point sums. -/
theorem clampLeft_tendsto_of_hasBrownianItoIntegral {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop (J t) := by
  obtain ⟨J', hJ', hconv⟩ := exists_hasBrownianItoIntegral_clamp hW x₀ j hHm hHc
  exact (hconv t).congr_right (hasBrownianItoIntegral_ae_unique hW x₀ j
    (fun ω => (hHc ω).comp continuous_real_toNNReal) hJ' hJ t)

end M6exist


section M7grid

theorem abs_clampH_sub_le (H : ℝ≥0 → Ω → ℝ) (R : ℝ) (s s' : ℝ≥0) (ω : Ω) :
    |clampH H R s ω - clampH H R s' ω| ≤ |H s ω - H s' ω| := by
  unfold clampH
  rw [max_comm (-R), max_comm (-R)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  simp

theorem dyTime_mono (t : ℝ≥0) (N : ℕ) {i l : ℕ} (h : i ≤ l) : dyTime t N i ≤ dyTime t N l := by
  unfold dyTime; gcongr

theorem abs_dyTime_sub_le (t : ℝ≥0) (N i l q : ℕ) (hil : i ≤ l) (hlq : l ≤ i + q) :
    |(dyTime t N i : ℝ) - dyTime t N l| ≤ (q : ℝ) * t / 2 ^ N := by
  have ht : (0 : ℝ) ≤ t := t.2
  have e : ∀ x : ℕ, (dyTime t N x : ℝ) = (x : ℝ) * t / 2 ^ N := fun x => by simp [dyTime]
  have h1 : (i : ℝ) ≤ l := by exact_mod_cast hil
  have h2 : (l : ℝ) ≤ i + q := by exact_mod_cast hlq
  rw [e, e, abs_sub_comm, abs_of_nonneg, ← sub_div, ← sub_mul]
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht)
      (by positivity)
  · rw [← sub_div, ← sub_mul]
    exact div_nonneg (mul_nonneg (by linarith) ht) (by positivity)

theorem dyTime_dyTime (t : ℝ≥0) (n m k i : ℕ) :
    dyTime (dyTime t n k) m i = dyTime t (n + m) (i * k) := by
  unfold dyTime
  rw [← NNReal.coe_inj]
  push_cast
  rw [pow_add]
  field_simp

/-- Masked sums over a finite range. -/
theorem sum_range_ite_lt {M : Type*} [AddCommMonoid M] (F : ℕ → M) {a b : ℕ} (hab : a ≤ b) :
    ∑ l ∈ Finset.range b, (if l < a then F l else 0) = ∑ l ∈ Finset.range a, F l := by
  rw [← Finset.sum_range_add_sum_Ico _ hab]
  have h1 : ∑ l ∈ Finset.range a, (if l < a then F l else 0) = ∑ l ∈ Finset.range a, F l :=
    Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_range.1 hl)
  have h2 : ∑ l ∈ Finset.Ico a b, (if l < a then F l else 0) = 0 :=
    Finset.sum_eq_zero fun l hl => if_neg (not_lt.2 (Finset.mem_Ico.1 hl).1)
  rw [h1, h2, add_zero]

/-- The dyadic step sum on `[0, s]`, `s = k t / 2^n`, at level `m` is the step sum on the
`t`-grid at level `n + m`, restricted to its first `2^m k` cells, with each coarse coefficient
repeated on the `k` fine cells it covers. -/
theorem itoStepSum_sub_grid (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n m k : ℕ) (hk : k ≤ 2 ^ n)
    (a : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W (dyTime t n k) m a ω =
      itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * k then a (l / k) ω else 0) ω := by
  set G : ℕ → ℝ := fun l => W (dyTime t (n + m) l) ω with hG
  have hle : 2 ^ m * k ≤ 2 ^ (n + m) := by
    rw [pow_add, mul_comm (2 ^ n)]; exact Nat.mul_le_mul_left _ hk
  have lhs : itoStepSum W (dyTime t n k) m a ω =
      ∑ i ∈ Finset.range (2 ^ m), a i ω * (G ((i + 1) * k) - G (i * k)) := by
    unfold itoStepSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : ((i : ℝ≥0) + 1) * dyTime t n k / (2 : ℝ≥0) ^ m =
        dyTime t (n + m) ((i + 1) * k) := by
      rw [← dyTime_dyTime]; unfold dyTime; push_cast; ring
    have e0 : (i : ℝ≥0) * dyTime t n k / (2 : ℝ≥0) ^ m = dyTime t (n + m) (i * k) := by
      rw [← dyTime_dyTime]; rfl
    rw [e1, e0]
  have rhs : itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * k then a (l / k) ω else 0) ω =
      ∑ l ∈ Finset.range (2 ^ (n + m)),
        (if l < 2 ^ m * k then a (l / k) ω * (G (l + 1) - G l) else 0) := by
    unfold itoStepSum
    refine Finset.sum_congr rfl fun l _ => ?_
    have e1 : ((l : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ (n + m) = dyTime t (n + m) (l + 1) := by
      unfold dyTime; push_cast; ring
    rw [e1]
    by_cases hl : l < 2 ^ m * k
    · simp only [hl, if_true]; rfl
    · simp only [hl, if_false, zero_mul]
  rw [lhs, rhs, sum_range_ite_lt _ hle, sum_range_mul_block]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiv : ∀ r ∈ Finset.range k, (i * k + r) / k = i := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le r) hr'
    rw [add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt hr', zero_add]
  symm
  calc ∑ r ∈ Finset.range k, a ((i * k + r) / k) ω * (G (i * k + r + 1) - G (i * k + r))
      = ∑ r ∈ Finset.range k, a i ω * (G (i * k + (r + 1)) - G (i * k + r)) :=
        Finset.sum_congr rfl fun r hr => by rw [hdiv r hr]; rfl
    _ = a i ω * (G ((i + 1) * k) - G (i * k)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun r => G (i * k + r)), add_zero,
          add_mul, one_mul]

end M7grid

section M7zero
variable [MeasurableSpace Ω]

/-- Step sums whose (adapted, bounded) coefficients are uniformly small off events of vanishing
probability tend to zero in probability (along any sequence of grid levels `L m`). -/
theorem itoStepSum_tendstoInMeasure_zero_of_small {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (j : Fin d) (L : ℕ → ℕ)
    (c : ℕ → ℕ → Ω → ℝ)
    (hc : ∀ m k : ℕ, k < 2 ^ L m → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ L m)] (c m k))
    (hC : ∀ m, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ L m → ∀ ω, |c m k ω| ≤ C)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ A : ℕ → Set Ω, Tendsto (fun m => P (A m)) atTop (𝓝 0) ∧
      ∀ m ω, ω ∉ A m → ∀ k < 2 ^ L m, |c m k ω| ≤ η) :
    TendstoInMeasure P (fun m => itoStepSum (fun s ω => W s ω j) t (L m) (c m)) atTop
      (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  simp only [Real.dist_eq, sub_zero]
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Eventually.of_forall fun _ => le_top
  have hr : 0 < e.toReal := ENNReal.toReal_pos he.ne' hetop
  have ht : (0 : ℝ) ≤ t := t.2
  set η : ℝ := min 1 (ε ^ 2 * e.toReal / (2 * (t + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨A, hA, hcA⟩ := hsmall η hη
  have hA' := (ENNReal.tendsto_nhds_zero.1 hA) (e / 2) (ENNReal.half_pos he.ne')
  filter_upwards [hA'] with m hm
  obtain ⟨C, hC'⟩ := hC m
  have hδ : (0 : ℝ) ≤ η ^ 2 * t := by positivity
  have hcheb := itoStepSum_local_chebyshev hW x₀ t (L m) j (c m) (hc m) C hC' hε hδ
  have hsub : {ω | η ^ 2 * t < (∑ k ∈ Finset.range (2 ^ L m), c m k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ L m : ℝ≥0) : ℝ)} ⊆ A m := by
    intro ω hω
    by_contra hωA
    have hsum : ∑ k ∈ Finset.range (2 ^ L m), c m k ω ^ 2 ≤ (2 : ℝ) ^ L m * η ^ 2 := by
      have := Finset.sum_le_sum (s := Finset.range (2 ^ L m)) (fun k hk =>
        (show c m k ω ^ 2 ≤ η ^ 2 from by
          have h1 := hcA m ω hωA k (Finset.mem_range.1 hk)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2))
      simpa [Finset.sum_const, Finset.card_range] using this
    have hh : ((t / (2 : ℝ≥0) ^ L m : ℝ≥0) : ℝ) = t / 2 ^ L m := by push_cast; ring
    have hQ : (∑ k ∈ Finset.range (2 ^ L m), c m k ω ^ 2) *
        ((t / (2 : ℝ≥0) ^ L m : ℝ≥0) : ℝ) ≤ η ^ 2 * t := by
      rw [hh]
      calc _ ≤ ((2 : ℝ) ^ L m * η ^ 2) * (t / 2 ^ L m) :=
            mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = η ^ 2 * t := by field_simp
    exact absurd hω (not_lt.2 hQ)
  have hηb : η ^ 2 * t / ε ^ 2 ≤ e.toReal / 2 := by
    have h1 : η ≤ 1 := min_le_left _ _
    have h2 : η ≤ ε ^ 2 * e.toReal / (2 * (t + 1)) := min_le_right _ _
    have h3 : η ^ 2 ≤ η := by linarith only [mul_le_mul_of_nonneg_right h1 hη.le]
    have h4 : η ^ 2 * t ≤ ε ^ 2 * e.toReal / (2 * (t + 1)) * t :=
      mul_le_mul_of_nonneg_right (h3.trans h2) ht
    have h5 : ε ^ 2 * e.toReal / (2 * (t + 1)) * t ≤ ε ^ 2 * (e.toReal / 2) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : 0 ≤ ε ^ 2 * e.toReal := by positivity
      linarith only [this]
    rw [div_le_iff₀ (by positivity)]
    linarith only [h4, h5]
  calc P {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t (L m) (c m) ω|}
      ≤ ENNReal.ofReal (η ^ 2 * t / ε ^ 2) + P {ω | η ^ 2 * t <
          (∑ k ∈ Finset.range (2 ^ L m), c m k ω ^ 2) * ((t / (2 : ℝ≥0) ^ L m : ℝ≥0) : ℝ)} :=
        hcheb
    _ ≤ e / 2 + e / 2 := by
        gcongr
        · calc ENNReal.ofReal (η ^ 2 * t / ε ^ 2) ≤ ENNReal.ofReal (e.toReal / 2) :=
                ENNReal.ofReal_le_ofReal hηb
            _ = e / 2 := by
                rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hetop,
                  ENNReal.ofReal_ofNat]
        · exact (measure_mono hsub).trans hm
    _ = e := ENNReal.add_halves e

/-- M7a: the Ito integral at an intermediate grid time `s = k t / 2^n` is the limit of the
truncated left-point sums of the fine `t`-grid (level `n + m`) over its first `2^m k` cells. -/
theorem partialSum_tendsto_of_hasBrownianItoIntegral {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 ^ n) :
    TendstoInMeasure P (fun m => itoStepSum (fun s ω => W s ω j) t (n + m)
      (fun l ω => if l < 2 ^ m * k then clampH H m (dyTime t (n + m) l) ω else 0)) atTop
      (J (dyTime t n k)) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  have hcoarse := clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ (dyTime t n k)
  let D : ℕ → ℕ → Ω → ℝ := fun m l ω => if l < 2 ^ m * k then
      clampH H m (dyTime t (n + m) (l / k * k)) ω - clampH H m (dyTime t (n + m) l) ω else 0
  have hD : TendstoInMeasure P
      (fun m => itoStepSum (fun s ω => W s ω j) t (n + m) (D m)) atTop (fun _ => 0) := by
    refine itoStepSum_tendstoInMeasure_zero_of_small hW x₀ t j (fun m => n + m) D ?_ ?_ ?_
    · intro m l _
      by_cases hlt : l < 2 ^ m * k
      · simp only [D, hlt, if_true]
        refine Measurable.sub ?_ (clampH_measurable (hHm _) _)
        exact (clampH_measurable (hHm _) _).mono
          (completedBrownianPast_mono P W _ (dyTime_mono t (n + m) (Nat.div_mul_le_self l k)))
          le_rfl
      · simp only [D, hlt, if_false]
        exact measurable_const
    · intro m
      refine ⟨2 * m, fun l _ ω => ?_⟩
      simp only [D]
      split_ifs
      · have h1 := abs_clampH_le H (Nat.cast_nonneg m) (dyTime t (n + m) (l / k * k)) ω
        have h2 := abs_clampH_le H (Nat.cast_nonneg m) (dyTime t (n + m) l) ω
        exact (abs_sub _ _).trans (by linarith only [h1, h2])
      · simp only [abs_zero]; positivity
    · intro η hη
      refine ⟨fun m => oscSet H t ((t : ℝ) / 2 ^ m) η, oscSet_tendsto hHae hHc t hη, ?_⟩
      intro m ω hω l hl
      simp only [D]
      split_ifs with hlt
      · refine (abs_clampH_sub_le H _ _ _ ω).trans ?_
        by_contra hc
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · simp [h0] at hlt
          · exact h0
        have hmod := Nat.div_add_mod' l k
        have hlt' := Nat.mod_lt l hk0
        refine hω (Set.mem_iUnion.2 ⟨((n + m, l / k * k), (n + m, l)),
          ((Nat.div_mul_le_self l k).trans hl.le), hl.le, ?_, lt_of_not_ge hc⟩)
        show |(dyTime t (n + m) (l / k * k) : ℝ) - dyTime t (n + m) l| ≤ (t : ℝ) / 2 ^ m
        refine (abs_dyTime_sub_le t (n + m) (l / k * k) l (2 ^ n) (Nat.div_mul_le_self l k)
          ((le_of_eq hmod.symm).trans (Nat.add_le_add_left (hlt'.le.trans hk) _))).trans
          (le_of_eq ?_)
        push_cast
        rw [pow_add]
        field_simp
      · simp [hη.le]
  have hsub := tendstoInMeasure_sub_real hcoarse hD
  simp only [sub_zero] at hsub
  refine hsub.congr_left (fun m => Eventually.of_forall fun ω => ?_)
  simp only
  rw [itoStepSum_sub_grid _ t n m k hk, itoStepSum_sub]
  unfold itoStepSum
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [D, leftCoef, dyTime_dyTime]
  split_ifs <;> ring

end M7zero


section M7qv
variable [MeasurableSpace Ω]

/-- Fourth moment of the standard Gaussian. -/
noncomputable def gaussFour : ℝ := ∫ x, x ^ 4 ∂(gaussianReal 0 1)

theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = gaussFour * (v : ℝ) ^ 2 := by
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
  have hv : gaussianReal (0 : ℝ) v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [hmap, mul_zero]; congr 1; ext; simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [hv, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, gaussFour]
  have : Real.sqrt v ^ 4 = (v : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [this, mul_comm]

theorem integrable_pow_four_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) := by
  have := (memLp_id_gaussianReal' (μ := 0) (v := v) ((4 : ℕ) : ℝ≥0∞)
    (ENNReal.natCast_ne_top 4)).integrable_norm_pow (by norm_num)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [id, Real.norm_eq_abs]
  exact Even.pow_abs ⟨2, rfl⟩ x

theorem stdBrownian_increment_four {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    Integrable (fun ω => (W (s + h) ω j - W s ω j) ^ 4) P ∧
      ∫ ω, (W (s + h) ω j - W s ω j) ^ 4 ∂P = gaussFour * (h : ℝ) ^ 2 := by
  have hB := hW.2.2.1 j
  have hL := hB.hasLaw_sub (s + h) s
  have hd : ((nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ) : ℝ≥0) : ℝ) = h := by
    rw [coe_nndist, Real.dist_eq]; push_cast; rw [add_sub_cancel_left]; exact abs_of_nonneg h.2
  constructor
  · have hi := integrable_pow_four_gaussianReal (nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))
    refine (integrable_map_measure (μ := P) (g := fun x : ℝ => x ^ 4)
      (by fun_prop : Continuous fun x : ℝ => x ^ 4).aestronglyMeasurable hL.aemeasurable).1 ?_
    rw [hL.map_eq]; exact hi
  · have h1 : ∫ ω, (W (s + h) ω j - W s ω j) ^ 4 ∂P =
        ∫ x, x ^ 4 ∂(gaussianReal 0 (nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))) :=
      hL.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [h1, integral_pow_four_gaussianReal, hd]

/-- The centred increment product `ΔW^j ΔW^{j'} - δ_{jj'} h`. -/
theorem incrProd_sq_le (a b κ : ℝ) : (a * b - κ) ^ 2 ≤ a ^ 4 + b ^ 4 + 2 * κ ^ 2 := by
  linarith only [sq_nonneg (a * b + κ), sq_nonneg (a ^ 2 - b ^ 2)]

theorem incrProd_memLp_and_bound {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j j' : Fin d) :
    MemLp (fun ω => (W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') -
        (if j = j' then (h : ℝ) else 0)) 2 P ∧
      ∫ ω, ((W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') -
        (if j = j' then (h : ℝ) else 0)) ^ 2 ∂P ≤ (2 * gaussFour + 2) * (h : ℝ) ^ 2 := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  set κ : ℝ := if j = j' then (h : ℝ) else 0 with hκ
  have hκ2 : κ ^ 2 ≤ (h : ℝ) ^ 2 := by
    simp only [hκ]; split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  obtain ⟨i1, e1⟩ := stdBrownian_increment_four hW s h j
  obtain ⟨i2, e2⟩ := stdBrownian_increment_four hW s h j'
  have hmeas : AEStronglyMeasurable (fun ω => (W (s + h) ω j - W s ω j) *
      (W (s + h) ω j' - W s ω j') - κ) P :=
    ((((hm _ j).sub (hm _ j)).mul ((hm _ j').sub (hm _ j'))).sub_const κ).aestronglyMeasurable
  have hbnd : Integrable (fun ω => (W (s + h) ω j - W s ω j) ^ 4 +
      (W (s + h) ω j' - W s ω j') ^ 4 + 2 * κ ^ 2) P :=
    (i1.add i2).add (integrable_const _)
  have hsq : Integrable (fun ω => ((W (s + h) ω j - W s ω j) *
      (W (s + h) ω j' - W s ω j') - κ) ^ 2) P := by
    refine hbnd.mono' (hmeas.pow 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact incrProd_sq_le _ _ _
  refine ⟨(memLp_two_iff_integrable_sq hmeas).2 hsq, ?_⟩
  calc ∫ ω, ((W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') - κ) ^ 2 ∂P
      ≤ ∫ ω, ((W (s + h) ω j - W s ω j) ^ 4 + (W (s + h) ω j' - W s ω j') ^ 4 + 2 * κ ^ 2) ∂P :=
        integral_mono hsq hbnd fun ω => incrProd_sq_le _ _ _
    _ = gaussFour * (h : ℝ) ^ 2 + gaussFour * (h : ℝ) ^ 2 + 2 * κ ^ 2 := by
        have e3 : ∫ ω, ((W (s + h) ω j - W s ω j) ^ 4 + (W (s + h) ω j' - W s ω j') ^ 4 + 2 * κ ^ 2) ∂P =
            ∫ ω, ((W (s + h) ω j - W s ω j) ^ 4 + (W (s + h) ω j' - W s ω j') ^ 4) ∂P + ∫ _ω, (2 * κ ^ 2) ∂P :=
          integral_add (i1.add i2) (integrable_const _)
        have e4 : ∫ ω, ((W (s + h) ω j - W s ω j) ^ 4 + (W (s + h) ω j' - W s ω j') ^ 4) ∂P = ∫ ω, (W (s + h) ω j - W s ω j) ^ 4 ∂P + ∫ ω, (W (s + h) ω j' - W s ω j') ^ 4 ∂P :=
          integral_add i1 i2
        rw [e3, e4, e1, e2]
        simp
    _ ≤ (2 * gaussFour + 2) * (h : ℝ) ^ 2 := by linarith only [hκ2]

theorem incrProd_integral_eq_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j j' : Fin d) :
    ∫ ω, ((W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') -
        (if j = j' then (h : ℝ) else 0)) ∂P = 0 := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  have hL2 : ∀ i, MemLp (fun ω => W (s + h) ω i - W s ω i) 2 P := fun i =>
    (stdBrownian_memLp_two hW _ i).sub (stdBrownian_memLp_two hW _ i)
  have e : ∫ ω, ((W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') - (if j = j' then (h : ℝ) else 0)) ∂P =
      ∫ ω, (W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') ∂P - ∫ _ω, (if j = j' then (h : ℝ) else 0) ∂P :=
    integral_sub ((hL2 j).integrable_mul (hL2 j')) (integrable_const _)
  rw [e, integral_const]
  by_cases hjj : j = j'
  · subst hjj
    have := stdBrownian_integral_increment_sq hW s h j
    simp only [if_true, ← sq, this]
    simp
  · simp only [hjj, if_false]
    have hind := (hW.2.2.2.indepFun hjj).comp
      (φ := fun f : ℝ≥0 → ℝ => f (s + h) - f s) (ψ := fun f : ℝ≥0 → ℝ => f (s + h) - f s)
      (by fun_prop) (by fun_prop)
    have key := hind.integral_fun_mul_eq_mul_integral
      ((hm _ j).sub (hm _ j)).aestronglyMeasurable ((hm _ j').sub (hm _ j')).aestronglyMeasurable
    simp only [Function.comp_apply] at key
    rw [key, stdBrownian_integral_increment hW]
    simp

theorem indepFun_completedPast_incrProd {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j j' : Fin d) (κ : ℝ)
    {a : Ω → ℝ} (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    IndepFun a (fun ω => (W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') - κ) P := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (stdBrownian_indep_completedPast hW x₀ s) ha.comap_le) ?_
  have hm : Measurable[MeasurableSpace.comap
      (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) inferInstance]
      (fun ω => (W (s + h) ω j - W s ω j) * (W (s + h) ω j' - W s ω j') - κ) := by
    have h1 := (measurable_pi_apply (h, j) : Measurable fun f : ℝ≥0 × Fin d → ℝ => f (h, j))
    have h2 := (measurable_pi_apply (h, j') : Measurable fun f : ℝ≥0 × Fin d → ℝ => f (h, j'))
    exact ((h1.mul h2).sub_const κ).comp
      (comap_measurable (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2))
  exact hm.comap_le

/-- Discrete (co)quadratic-variation sums on the dyadic `t`-grid, weighted by `c`. -/
noncomputable def qvSum (W : ℝ≥0 → Ω → SDEState d) (j j' : Fin d) (t : ℝ≥0) (N : ℕ)
    (c : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range (2 ^ N), c l ω *
    ((W (((l : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ N) ω j - W ((l : ℝ≥0) * t / (2 : ℝ≥0) ^ N) ω j) *
      (W (((l : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ N) ω j' - W ((l : ℝ≥0) * t / (2 : ℝ≥0) ^ N) ω j') -
      if j = j' then ((t / (2 : ℝ≥0) ^ N : ℝ≥0) : ℝ) else 0)

/-- M7b: `L²` bound for weighted quadratic-variation sums of Brownian coordinates. -/
theorem qvSum_sq_integral_le {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j j' : Fin d) (t : ℝ≥0) (N : ℕ)
    (c : ℕ → Ω → ℝ)
    (hc : ∀ k : ℕ, k < 2 ^ N → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ N)] (c k))
    {K : ℝ} (hK : 0 ≤ K) (hcK : ∀ k : ℕ, k < 2 ^ N → ∀ ω, |c k ω| ≤ K) :
    ∫ ω, qvSum W j j' t N c ω ^ 2 ∂P ≤ K ^ 2 * (2 * gaussFour + 2) * (t : ℝ) ^ 2 / 2 ^ N := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  set h : ℝ≥0 := t / (2 : ℝ≥0) ^ N with hh
  let τ : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * t / (2 : ℝ≥0) ^ N
  have hstep : ∀ k : ℕ, ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ N = τ k + h := by
    intro k; simp only [τ, hh]; ring
  have hτmono : ∀ l k : ℕ, l ≤ k → τ l ≤ τ k := by
    intro l k hlk; simp only [τ]; gcongr
  have hτsucc : ∀ l k : ℕ, l < k → τ l + h ≤ τ k := by
    intro l k hlk
    rw [← hstep]; simp only [τ]; gcongr
    exact_mod_cast Nat.succ_le_of_lt hlk
  set κ : ℝ := if j = j' then (h : ℝ) else 0 with hκ
  let Y : ℕ → Ω → ℝ := fun k ω =>
    (W (τ k + h) ω j - W (τ k) ω j) * (W (τ k + h) ω j' - W (τ k) ω j') - κ
  let X : ℕ → Ω → ℝ := fun k ω => c k ω * Y k ω
  have hsum : ∀ ω, qvSum W j j' t N c ω = ∑ k ∈ Finset.range (2 ^ N), X k ω := by
    intro ω; unfold qvSum
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [X, Y, hκ, hh]; rw [hstep k]
  have hYL2 : ∀ k, MemLp (Y k) 2 P := fun k => (incrProd_memLp_and_bound hW (τ k) h j j').1
  have haesm : ∀ k, k < 2 ^ N → AEStronglyMeasurable (c k) P := fun k hk =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hc k hk)
  have hint : ∀ k, k < 2 ^ N → ∀ l, l < 2 ^ N → Integrable (fun ω => X k ω * X l ω) P := by
    intro k hk l hl
    have hg : Integrable (fun ω => (K * K) * |Y k ω * Y l ω|) P :=
      ((hYL2 k).integrable_mul (hYL2 l)).abs.const_mul _
    refine hg.mono' (((haesm k hk).mul (hYL2 k).1).mul ((haesm l hl).mul (hYL2 l).1)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    calc |X k ω * X l ω| = (|c k ω| * |c l ω|) * |Y k ω * Y l ω| := by
          simp only [X, abs_mul]; ring
      _ ≤ (K * K) * |Y k ω * Y l ω| :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hcK k hk ω) (hcK l hl ω) (abs_nonneg _) hK)
            (abs_nonneg _)
  have off : ∀ l k, l < k → k < 2 ^ N → ∫ ω, X l ω * X k ω ∂P = 0 := by
    intro l k hlk hk
    have hl : l < 2 ^ N := hlk.trans hk
    have hb : Measurable[completedBrownianPast P W (fun _ => x₀) (τ k)]
        (fun ω => c l ω * Y l ω * c k ω) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (hc k hk)
      · exact (hc l hl).mono (completedBrownianPast_mono P W _ (hτmono l k hlk.le)) le_rfl
      · refine Measurable.sub_const (Measurable.mul ?_ ?_) _
        · exact (coord_measurable_completedPast P W _ (hτsucc l k hlk) j).sub
            (coord_measurable_completedPast P W _ (hτmono l k hlk.le) j)
        · exact (coord_measurable_completedPast P W _ (hτsucc l k hlk) j').sub
            (coord_measurable_completedPast P W _ (hτmono l k hlk.le) j')
    have hind := indepFun_completedPast_incrProd hW x₀ (τ k) h j j' κ hb
    have hm := stdBrownian_coord_measurable hW
    have key := hind.integral_fun_mul_eq_mul_integral
      (aestronglyMeasurable_of_completedPast hW x₀ _ hb) (hYL2 k).1
    have h0 : ∫ ω, Y k ω ∂P = 0 := incrProd_integral_eq_zero hW (τ k) h j j'
    calc ∫ ω, X l ω * X k ω ∂P = ∫ ω, (c l ω * Y l ω * c k ω) * Y k ω ∂P := by
          congr 1; funext ω; simp only [X]; ring
      _ = 0 := by rw [key]; simp only [Y] at h0 ⊢; rw [h0, mul_zero]
  have hkey : ∀ ω, (qvSum W j j' t N c ω) ^ 2 =
      ∑ k ∈ Finset.range (2 ^ N), ∑ l ∈ Finset.range (2 ^ N), X k ω * X l ω := by
    intro ω; rw [hsum ω, sq, Finset.sum_mul_sum]
  simp_rw [hkey]
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _
    (fun l hl => hint k (Finset.mem_range.1 hk) l (Finset.mem_range.1 hl)))]
  have hdiag : ∀ k ∈ Finset.range (2 ^ N),
      ∫ ω, ∑ l ∈ Finset.range (2 ^ N), X k ω * X l ω ∂P ≤
        K ^ 2 * ((2 * gaussFour + 2) * (h : ℝ) ^ 2) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [integral_finsetSum _ (fun l hl => hint k hk' l (Finset.mem_range.1 hl))]
    rw [Finset.sum_eq_single k]
    · have hb := (incrProd_memLp_and_bound hW (τ k) h j j').2
      have hY2 : Integrable (fun ω => Y k ω ^ 2) P := (hYL2 k).integrable_sq
      calc ∫ ω, X k ω * X k ω ∂P ≤ ∫ ω, K ^ 2 * Y k ω ^ 2 ∂P := by
            refine integral_mono (hint k hk' k hk') (hY2.const_mul _) fun ω => ?_
            have h1 : |c k ω| ≤ K := hcK k hk' ω
            have h2 : c k ω ^ 2 ≤ K ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
            calc X k ω * X k ω = c k ω ^ 2 * Y k ω ^ 2 := by simp only [X]; ring
              _ ≤ K ^ 2 * Y k ω ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = K ^ 2 * ∫ ω, Y k ω ^ 2 ∂P := integral_const_mul _ _
        _ ≤ K ^ 2 * ((2 * gaussFour + 2) * (h : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    · intro l hl hlk
      rcases lt_or_gt_of_ne hlk with hlt | hgt
      · rw [← off l k hlt hk']
        congr 1; funext ω; ring
      · exact off k l hgt (Finset.mem_range.1 hl)
    · intro hnot; exact absurd hk hnot
  refine (Finset.sum_le_sum hdiag).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]
  push_cast
  field_simp

end M7qv

section M7c
variable [MeasurableSpace Ω]

theorem qvSum_memLp {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (j j' : Fin d) (t : ℝ≥0) (N : ℕ) (c : ℕ → Ω → ℝ)
    (hc : ∀ k : ℕ, k < 2 ^ N → AEStronglyMeasurable (c k) P)
    {K : ℝ} (hcK : ∀ k : ℕ, k < 2 ^ N → ∀ ω, |c k ω| ≤ K) :
    MemLp (qvSum W j j' t N c) 2 P := by
  unfold qvSum
  refine memLp_finsetSum _ fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have e : ((l : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ N =
      (l : ℝ≥0) * t / (2 : ℝ≥0) ^ N + t / (2 : ℝ≥0) ^ N := by ring
  rw [e]
  have hY := (incrProd_memLp_and_bound hW ((l : ℝ≥0) * t / (2 : ℝ≥0) ^ N)
    (t / (2 : ℝ≥0) ^ N) j j').1
  refine MemLp.of_le_mul (c := K) hY ((hc l hl').mul hY.1)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hcK l hl' ω) (norm_nonneg _)

/-- M7c: weighted quadratic-variation sums tend to `0` in probability. -/
theorem qvSum_tendstoInMeasure_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j j' : Fin d) (t : ℝ≥0)
    (c : ℕ → ℕ → Ω → ℝ)
    (hc : ∀ N k : ℕ, k < 2 ^ N → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ N)] (c N k))
    {K : ℝ} (hK : 0 ≤ K) (hcK : ∀ N k : ℕ, k < 2 ^ N → ∀ ω, |c N k ω| ≤ K) :
    TendstoInMeasure P (fun N => qvSum W j j' t N (c N)) atTop (fun _ => 0) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hbound : ∀ N : ℕ, P {ω | ε ≤ dist (qvSum W j j' t N (c N) ω) 0} ≤
      ENNReal.ofReal (K ^ 2 * (2 * gaussFour + 2) * (t : ℝ) ^ 2 / 2 ^ N / ε ^ 2) := by
    intro N
    have hL2 := qvSum_memLp hW j j' t N (c N)
      (fun k hk => aestronglyMeasurable_of_completedPast hW x₀ _ (hc N k hk)) (hcK N)
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun ω => sq_nonneg (qvSum W j j' t N (c N) ω))
      hL2.integrable_sq (ε ^ 2)
    have hI := qvSum_sq_integral_le hW x₀ j j' t N (c N) (hc N) hK (hcK N)
    have hsub : {ω | ε ≤ dist (qvSum W j j' t N (c N) ω) 0} ⊆
        {ω | ε ^ 2 ≤ qvSum W j j' t N (c N) ω ^ 2} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
      calc ε ^ 2 ≤ |qvSum W j j' t N (c N) ω| ^ 2 := pow_le_pow_left₀ hε.le hω 2
        _ = _ := sq_abs _
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hm.trans hI
  have htend : Tendsto (fun N : ℕ =>
      ENNReal.ofReal (K ^ 2 * (2 * gaussFour + 2) * (t : ℝ) ^ 2 / 2 ^ N / ε ^ 2))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h0 : Tendsto (fun N : ℕ => K ^ 2 * (2 * gaussFour + 2) * (t : ℝ) ^ 2 / ε ^ 2 *
        (1 / 2 : ℝ) ^ N) atTop (𝓝 (K ^ 2 * (2 * gaussFour + 2) * (t : ℝ) ^ 2 / ε ^ 2 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    rw [mul_zero] at h0
    refine h0.congr fun N => ?_
    rw [one_div, inv_pow]
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
    (fun _ => zero_le) hbound

end M7c

section M8a
variable [MeasurableSpace Ω]

theorem tendstoInMeasure_add_real {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω + f' i ω) l (fun ω => g ω + g' ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf hf' ⊢
  refine tendstoInMeasure_zero_of_abs_le one_pos hf hf' fun i ω => ?_
  rw [one_mul]
  calc |f i ω + f' i ω - (g ω + g' ω)| = |(f i ω - g ω) + (f' i ω - g' ω)| := by
        congr 1; ring
    _ ≤ _ := abs_add_le _ _

theorem tendstoInMeasure_zero_const {ι : Type*} {l : Filter ι} {P : Measure Ω} :
    TendstoInMeasure P (fun (_ : ι) (_ : Ω) => (0 : ℝ)) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have : {ω : Ω | ε ≤ dist (0 : ℝ) 0} = ∅ := by
    ext ω; simp only [dist_self, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  simp only [this, measure_empty]
  exact tendsto_const_nhds

theorem tendstoInMeasure_finsetSum_real {ι κ : Type*} {l : Filter ι} {P : Measure Ω}
    (s : Finset κ) {f : κ → ι → Ω → ℝ} {g : κ → Ω → ℝ}
    (hf : ∀ k ∈ s, TendstoInMeasure P (f k) l (g k)) :
    TendstoInMeasure P (fun i ω => ∑ k ∈ s, f k i ω) l (fun ω => ∑ k ∈ s, g k ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendstoInMeasure_zero_const (ι := ι) (l := l) (P := P))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact tendstoInMeasure_add_real (hf a (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem tendstoInMeasure_mul_left_real {ι : Type*} {l : Filter ι} {P : Measure Ω}
    {f : ι → Ω → ℝ} {g : Ω → ℝ} (a : Ω → ℝ) {R : ℝ} (hR : 0 < R) (ha : ∀ ω, |a ω| ≤ R)
    (hf : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω => a ω * f i ω) l (fun ω => a ω * g ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf ⊢
  refine tendstoInMeasure_zero_of_abs_le hR hf hf fun i ω => ?_
  rw [← mul_sub, abs_mul]
  nlinarith [ha ω, abs_nonneg (f i ω - g ω), abs_nonneg (a ω)]

/-- A uniform tail bound along a sequence passes to its limit in probability. -/
theorem meas_le_of_tendstoInMeasure {P : Measure Ω} {Y : ℕ → Ω → ℝ} {Y' : Ω → ℝ}
    (h : TendstoInMeasure P Y atTop Y') {ε : ℝ} (hε : 0 < ε) {b : ℝ≥0∞}
    (hb : ∀ᶠ m in atTop, P {ω | ε ≤ |Y m ω|} ≤ b) :
    P {ω | 2 * ε ≤ |Y' ω|} ≤ b := by
  rw [tendstoInMeasure_iff_dist] at h
  have hle : ∀ᶠ m in atTop, P {ω | 2 * ε ≤ |Y' ω|} ≤
      P {ω | ε ≤ dist (Y m ω) (Y' ω)} + b := by
    filter_upwards [hb] with m hm
    refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl hm))
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq] at hω ⊢
    by_contra hc
    push Not at hc
    have h1 := abs_sub_abs_le_abs_sub (Y' ω) (Y m ω)
    rw [abs_sub_comm (Y' ω)] at h1
    linarith [hc.1, hc.2]
  have ht : Tendsto (fun m => P {ω | ε ≤ dist (Y m ω) (Y' ω)} + b) atTop (𝓝 (0 + b)) :=
    (h ε hε).add tendsto_const_nhds
  rw [zero_add] at ht
  exact ge_of_tendsto ht hle

/-- Weighting the cell increments of masked fine sums by coarse weights gives the fine step
sum with coarse-held weights. -/
theorem weighted_masked_diff (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n m : ℕ) (A : ℕ → Ω → ℝ)
    (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∑ k ∈ Finset.range (2 ^ n), A k ω *
      (itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * (k + 1) then c l ω else 0) ω -
       itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * k then c l ω else 0) ω) =
    itoStepSum W t (n + m) (fun l ω => A (l / 2 ^ m) ω * c l ω) ω := by
  set f : ℕ → ℝ := fun l => c l ω * (W (((l : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ (n + m)) ω -
    W ((l : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m)) ω) with hf
  have hle : ∀ k, k ≤ 2 ^ n → 2 ^ m * k ≤ 2 ^ (n + m) := by
    intro k hk; rw [pow_add, mul_comm (2 ^ n)]; exact Nat.mul_le_mul_left _ hk
  have hmask : ∀ k, k ≤ 2 ^ n → itoStepSum W t (n + m)
      (fun l ω => if l < 2 ^ m * k then c l ω else 0) ω = ∑ l ∈ Finset.range (2 ^ m * k), f l := by
    intro k hk
    rw [← sum_range_ite_lt f (hle k hk)]
    unfold itoStepSum
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : l < 2 ^ m * k <;> simp [h, hf]
  have hcell : ∀ k ∈ Finset.range (2 ^ n), A k ω *
      (itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * (k + 1) then c l ω else 0) ω -
       itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * k then c l ω else 0) ω) =
      ∑ r ∈ Finset.range (2 ^ m), A k ω * f (k * 2 ^ m + r) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [hmask (k + 1) hk', hmask k hk'.le, show 2 ^ m * (k + 1) = 2 ^ m * k + 2 ^ m by ring,
      Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_comm (2 ^ m) k]
  rw [Finset.sum_congr rfl hcell]
  unfold itoStepSum
  rw [show (2 : ℕ) ^ (n + m) = 2 ^ n * 2 ^ m from pow_add 2 n m, sum_range_mul_block]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r hr => ?_
  have hdiv : (k * 2 ^ m + r) / 2 ^ m = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt (Finset.mem_range.1 hr), zero_add]
  simp only [hf, hdiv]
  push_cast
  ring

/-- Generic `L²` bound for a step sum whose coefficients are bounded by `K`, and by `η` off a
set `E`. -/
theorem itoStepSum_sq_integral_le_of_off {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) (t : ℝ≥0) (N : ℕ)
    (D : ℕ → Ω → ℝ)
    (hDm : ∀ k : ℕ, k < 2 ^ N → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ N)] (D k))
    {K η : ℝ} (hDb : ∀ k : ℕ, k < 2 ^ N → ∀ ω, |D k ω| ≤ K) (E : Set Ω)
    (hE : ∀ ω, ω ∉ E → ∀ k : ℕ, k < 2 ^ N → |D k ω| ≤ η) :
    ∫ ω, (itoStepSum (fun s ω => W s ω j) t N D ω) ^ 2 ∂P ≤
      η ^ 2 * t + K ^ 2 * t * P.real E := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  rw [itoStepSum_isometry hW x₀ t N j D hDm K hDb]
  have hint : ∀ k ∈ Finset.range (2 ^ N), Integrable (fun ω => D k ω ^ 2) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine Integrable.of_bound
      ((aestronglyMeasurable_of_completedPast hW x₀ _ (hDm k hk')).pow 2) (K ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDb k hk' ω) 2
  set h : ℝ := ((t / (2 : ℝ≥0) ^ N : ℝ≥0) : ℝ) with hhdef
  have hh : 0 ≤ h := NNReal.coe_nonneg _
  have hNh : ((2 ^ N : ℕ) : ℝ) * h = t := by
    rw [hhdef]; push_cast; field_simp
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  set O := toMeasurable P E with hO
  have hOm : MeasurableSet O := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, (∑ k ∈ Finset.range (2 ^ N), D k ω ^ 2) * h ≤
      η ^ 2 * t + K ^ 2 * t * O.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ O
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have hs : ∑ k ∈ Finset.range (2 ^ N), D k ω ^ 2 ≤
          (Finset.range (2 ^ N)).card • (K ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        have := hDb k (Finset.mem_range.1 hk) ω
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      have := mul_le_mul_of_nonneg_right hs hh
      calc (∑ k ∈ Finset.range (2 ^ N), D k ω ^ 2) * h
          ≤ ((2 ^ N : ℕ) : ℝ) * K ^ 2 * h := this
        _ = K ^ 2 * (((2 ^ N : ℕ) : ℝ) * h) := by ring
        _ = K ^ 2 * t := by rw [hNh]
        _ ≤ η ^ 2 * t + K ^ 2 * t := le_add_of_nonneg_left (by positivity)
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hno : ω ∉ E := fun h' => hω (subset_toMeasurable _ _ h')
      have hs : ∑ k ∈ Finset.range (2 ^ N), D k ω ^ 2 ≤
          (Finset.range (2 ^ N)).card • (η ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hE ω hno k (Finset.mem_range.1 hk)) 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      calc (∑ k ∈ Finset.range (2 ^ N), D k ω ^ 2) * h
          ≤ ((2 ^ N : ℕ) : ℝ) * η ^ 2 * h := mul_le_mul_of_nonneg_right hs hh
        _ = η ^ 2 * (((2 ^ N : ℕ) : ℝ) * h) := by ring
        _ = η ^ 2 * t := by rw [hNh]
  have hOreal : P.real O = P.real E := by
    simp only [measureReal_def, hO, measure_toMeasurable]
  have hIi : Integrable (fun ω => K ^ 2 * (t : ℝ) * O.indicator 1 ω) P :=
    ((integrable_indicator_iff hOm).2 (integrable_const (1 : ℝ)).integrableOn).const_mul _
  calc ∑ k ∈ Finset.range (2 ^ N), (∫ ω, D k ω ^ 2 ∂P) * h
      = ∫ ω, (∑ k ∈ Finset.range (2 ^ N), D k ω ^ 2) * h ∂P := by
        rw [integral_mul_const, integral_finsetSum _ hint, Finset.sum_mul]
    _ ≤ ∫ ω, (η ^ 2 * t + K ^ 2 * t * O.indicator 1 ω) ∂P :=
        integral_mono ((integrable_finsetSum _ hint).mul_const h)
          ((integrable_const _).add hIi) hpt
    _ = η ^ 2 * t + K ^ 2 * t * P.real E := by
        rw [integral_add (integrable_const _) hIi, integral_const, integral_const_mul,
          integral_indicator_one hOm, hOreal]
        simp

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

/-- Locality of the Ito integral: integrands agreeing on the dyadic grid of `[0, s]` on an event
give integrals agreeing a.e. on that event at time `s`. -/
theorem hasBrownianItoIntegral_eq_on {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H H' J J' : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s))
    (hH'c : ∀ ω, Continuous fun s => H' s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H' J') (s : ℝ≥0) (E : Set Ω)
    (hE : ∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N → H (dyTime s N i) ω = H' (dyTime s N i) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω := by
  refine tendstoInMeasure_ae_eq_on
    (clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ s)
    (clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hH'm hH'c hJ' s) fun n ω hω => ?_
  unfold itoStepSum
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  simp only [leftCoef]
  unfold clampH
  rw [hE ω hω n k (Finset.mem_range.1 hk).le]

end M8c

section M8d
variable [MeasurableSpace Ω]

/-- Tightness of one real random variable. -/
theorem tendsto_measure_abs_gt {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    Tendsto (fun M : ℕ => P {ω | (M : ℝ) < |f ω|}) atTop (𝓝 0) := by
  have hanti : Antitone (fun M : ℕ => {ω | (M : ℝ) < |f ω|}) := by
    intro M M' hMM' ω hω
    show (M : ℝ) < |f ω|
    exact lt_of_le_of_lt (by exact_mod_cast hMM') (show (M' : ℝ) < |f ω| from hω)
  have hnm : ∀ M : ℕ, NullMeasurableSet {ω | (M : ℝ) < |f ω|} P := fun M =>
    nullMeasurableSet_lt aemeasurable_const hf.aemeasurable.abs
  have := tendsto_measure_iInter_atTop (μ := P) hnm hanti ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ M : ℕ, {ω | (M : ℝ) < |f ω|}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    obtain ⟨M, hM⟩ := exists_nat_ge |f ω|
    exact ⟨M, hM⟩
  rw [hempty, measure_empty] at this
  exact this

theorem tendstoInMeasure_mul_zero {ι : Type*} {l : Filter ι} {P : Measure Ω}
    {a b : ι → Ω → ℝ} (ha : TendstoInMeasure P a l (fun _ => 0))
    (hb : TendstoInMeasure P b l (fun _ => 0)) :
    TendstoInMeasure P (fun i ω => a i ω * b i ω) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at ha hb ⊢
  intro ε hε
  have hsum := (ha 1 one_pos).add (hb ε hε)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  rw [abs_mul] at hω
  have : |a i ω| * |b i ω| < 1 * ε :=
    mul_lt_mul'' hcon.1 hcon.2 (abs_nonneg _) (abs_nonneg _)
  linarith only [hω, this]

/-- Products of sequences converging in probability (finite measure). -/
theorem tendstoInMeasure_mul_real {P : Measure Ω} [IsFiniteMeasure P] {f g : ℕ → Ω → ℝ}
    {f' g' : Ω → ℝ} (hf : TendstoInMeasure P f atTop f') (hg : TendstoInMeasure P g atTop g')
    (hf'm : AEStronglyMeasurable f' P) (hg'm : AEStronglyMeasurable g' P) :
    TendstoInMeasure P (fun n ω => f n ω * g n ω) atTop (fun ω => f' ω * g' ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf hg ⊢
  refine tendstoInMeasure_of_local fun δ hδ => ?_
  have hb := (tendsto_measure_abs_gt hf'm).add (tendsto_measure_abs_gt hg'm)
  rw [add_zero] at hb
  obtain ⟨M0, hMδ, hM1⟩ :=
    (((ENNReal.tendsto_nhds_zero.1 hb) δ hδ).and (eventually_ge_atTop 1)).exists
  set M : ℝ := (M0 : ℝ) with hMdef
  have hM : 0 < M := by rw [hMdef]; exact_mod_cast hM1
  let F' : Ω → ℝ := fun ω => max (-M) (min (f' ω) M)
  let G' : Ω → ℝ := fun ω => max (-M) (min (g' ω) M)
  have hF'b : ∀ ω, |F' ω| ≤ M := fun ω => by
    simp only [F']; rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_right _ _)
  have hG'b : ∀ ω, |G' ω| ≤ M := fun ω => by
    simp only [G']; rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_right _ _)
  set B : Set Ω := {ω | M < |f' ω|} ∪ {ω | M < |g' ω|} with hB
  have h1 := tendstoInMeasure_mul_zero hf hg
  have h2 := tendstoInMeasure_mul_left_real F' hM hF'b hg
  have h3 := tendstoInMeasure_mul_left_real G' hM hG'b hf
  simp only [mul_zero] at h2 h3
  have h123 := tendstoInMeasure_add_real (tendstoInMeasure_add_real h1 h2) h3
  simp only [add_zero] at h123
  refine ⟨B, (measure_union_le _ _).trans hMδ, _, _, h123, Eventually.of_forall
    fun n ω hω => ?_, Eventually.of_forall fun ω _ => rfl⟩
  have hf'ω : F' ω = f' ω := by
    have : |f' ω| ≤ M := not_lt.1 fun h => hω (Or.inl h)
    rw [abs_le] at this
    simp only [F']; rw [min_eq_left this.2, max_eq_right this.1]
  have hg'ω : G' ω = g' ω := by
    have : |g' ω| ≤ M := not_lt.1 fun h => hω (Or.inr h)
    rw [abs_le] at this
    simp only [G']; rw [min_eq_left this.2, max_eq_right this.1]
  rw [hf'ω, hg'ω]
  ring

end M8d

section M8e
variable [MeasurableSpace Ω]

/-- Coarse cell error of an Ito integral against its left-point approximation. -/
noncomputable def cellErr (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H J : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  (J (dyTime t n (k + 1)) ω - J (dyTime t n k) ω) -
    H (dyTime t n k) ω * (W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j)

theorem tendstoInMeasure_const_seq {ι : Type*} {l : Filter ι} {P : Measure Ω} (g : Ω → ℝ) :
    TendstoInMeasure P (fun (_ : ι) => g) l g := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have : {ω : Ω | ε ≤ dist (g ω) (g ω)} = ∅ := by
    ext ω; simp only [dist_self, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  simp only [this, measure_empty]
  exact tendsto_const_nhds

/-- One coarse cell of masked fine sums. -/
theorem cell_masked_diff (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n m k : ℕ) (hk : k < 2 ^ n)
    (c : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * (k + 1) then c l ω else 0) ω -
      itoStepSum W t (n + m) (fun l ω => if l < 2 ^ m * k then c l ω else 0) ω =
    itoStepSum W t (n + m) (fun l ω => if l / 2 ^ m = k then c l ω else 0) ω := by
  have h := weighted_masked_diff W t n m (fun k' _ => if k' = k then (1 : ℝ) else 0) c ω
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
    (fun h' => absurd (Finset.mem_range.2 hk) h')] at h
  simp only [↓reduceIte, one_mul] at h
  rw [h]
  unfold itoStepSum
  refine Finset.sum_congr rfl fun l _ => ?_
  beta_reduce
  split_ifs <;> simp

theorem coarse_incr_eq (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n m k : ℕ) (hk : k < 2 ^ n)
    (a : Ω → ℝ) (ω : Ω) :
    a ω * (W (dyTime t n (k + 1)) ω - W (dyTime t n k) ω) =
      itoStepSum W t (n + m) (fun l ω => if l / 2 ^ m = k then a ω else 0) ω := by
  have h := itoStepSum_refine W t n m (fun k' ω => if k' = k then a ω else 0) ω
  have h2 : itoStepSum W t (n + m) (fun l ω => if l / 2 ^ m = k then a ω else 0) ω =
      itoStepSum W t (n + m) (fun l => (fun k' ω => if k' = k then a ω else 0) (l / 2 ^ m)) ω :=
    rfl
  rw [h2, ← h]
  unfold itoStepSum
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
    (fun h' => absurd (Finset.mem_range.2 hk) h')]
  simp only [↓reduceIte, dyTime, Nat.cast_add, Nat.cast_one]

/-- M8e: the squared cell errors of a bounded continuous adapted Ito integral vanish in
probability. -/
theorem cellErr_sq_tendsto_bdd {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    {R : ℝ} (hR : 0 < R) (hHb : ∀ s ω, |H s ω| ≤ R)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), cellErr W j H J t n k ω ^ 2)
      atTop (fun _ => 0) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have step : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η →
      P {ω | 2 * ε ≤ |∑ k ∈ Finset.range (2 ^ n), cellErr W j H J t n k ω ^ 2|} ≤
      ENNReal.ofReal ((η ^ 2 * t + (2 * R) ^ 2 * t *
        P.real (oscSet H t ((t : ℝ) / 2 ^ n) η)) / ε) := by
    intro n ε hε η hη
    let F : ℕ → ℕ → Ω → ℝ := fun k m => itoStepSum (fun s ω => W s ω j) t (n + m)
      (fun l ω => if l < 2 ^ m * k then clampH H m (dyTime t (n + m) l) ω else 0)
    have hF : ∀ k, k ≤ 2 ^ n → TendstoInMeasure P (F k) atTop (J (dyTime t n k)) :=
      fun k hk => partialSum_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ t n k hk
    let ck : ℕ → ℕ → ℕ → Ω → ℝ := fun k m l ω => if l / 2 ^ m = k then
      H (dyTime t (n + m) l) ω - H (dyTime t n k) ω else 0
    let D : ℕ → ℕ → Ω → ℝ := fun k m => itoStepSum (fun s ω => W s ω j) t (n + m) (ck k m)
    have hckm : ∀ k m l : ℕ, l < 2 ^ (n + m) → Measurable[completedBrownianPast P W
        (fun _ => x₀) ((l : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m))] (ck k m l) := by
      intro k m l _
      by_cases h : l / 2 ^ m = k
      · simp only [ck, h, ↓reduceIte]
        rw [← h]
        exact (hHm (dyTime t (n + m) l)).sub ((hHm _).mono
          (completedBrownianPast_mono P W _ (dyTime_coarse t n m l).1) le_rfl)
      · simp only [ck, h, ↓reduceIte]
        exact measurable_const
    have hckb : ∀ k m l : ℕ, l < 2 ^ (n + m) → ∀ ω, |ck k m l ω| ≤ 2 * R := by
      intro k m l _ ω
      simp only [ck]
      split_ifs
      · have h1 := abs_le.1 (hHb (dyTime t (n + m) l) ω)
        have h2 := abs_le.1 (hHb (dyTime t n k) ω)
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · simp only [abs_zero]; linarith
    have hDL2 : ∀ k m, MemLp (D k m) 2 P := fun k m =>
      itoStepSum_memLp hW t (n + m) j (ck k m)
        (fun l hl => aestronglyMeasurable_of_completedPast hW x₀ _ (hckm k m l hl)) _ (hckb k m)
    have hD : ∀ k, k < 2 ^ n → TendstoInMeasure P (D k) atTop (cellErr W j H J t n k) := by
      intro k hk
      have h0 := tendstoInMeasure_sub_real
        (tendstoInMeasure_sub_real (hF (k + 1) hk) (hF k hk.le))
        (tendstoInMeasure_const_seq (l := atTop) (P := P) (fun ω => H (dyTime t n k) ω *
          (W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j)))
      refine h0.congr' ?_ (Eventually.of_forall fun ω => rfl)
      filter_upwards [eventually_ge_atTop ⌈R⌉₊] with m hm
      refine Eventually.of_forall fun ω => ?_
      have hRm : R ≤ (m : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hm)
      have e1 := cell_masked_diff (fun s ω => W s ω j) t n m k hk
        (fun l ω => clampH H m (dyTime t (n + m) l) ω) ω
      have e2 := coarse_incr_eq (fun s ω => W s ω j) t n m k hk
        (fun ω => H (dyTime t n k) ω) ω
      show (F (k + 1) m ω - F k m ω) - H (dyTime t n k) ω *
        (W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j) =
        itoStepSum (fun s ω => W s ω j) t (n + m) (ck k m) ω
      rw [show F (k + 1) m ω - F k m ω = _ from e1,
        show H (dyTime t n k) ω * (W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j) = _
          from e2, itoStepSum_sub]
      unfold itoStepSum
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      simp only [ck]
      split_ifs
      · rw [clampH_eq_of_abs_le H ((hHb _ _).trans hRm)]
      · simp
    have hEae : ∀ k, k < 2 ^ n → AEStronglyMeasurable (cellErr W j H J t n k) P :=
      fun k hk => TendstoInMeasure.aestronglyMeasurable (fun m => (hDL2 k m).1) (hD k hk)
    have hsq : TendstoInMeasure P (fun m ω => ∑ k ∈ Finset.range (2 ^ n), D k m ω * D k m ω)
        atTop (fun ω => ∑ k ∈ Finset.range (2 ^ n),
          cellErr W j H J t n k ω * cellErr W j H J t n k ω) :=
      tendstoInMeasure_finsetSum_real _ fun k hk =>
        tendstoInMeasure_mul_real (hD k (Finset.mem_range.1 hk)) (hD k (Finset.mem_range.1 hk))
          (hEae k (Finset.mem_range.1 hk)) (hEae k (Finset.mem_range.1 hk))
    simp only [← sq] at hsq
    refine meas_le_of_tendstoInMeasure hsq hε (Eventually.of_forall fun m => ?_)
    -- the fine coefficient with coarse-held subtrahend
    let c : ℕ → Ω → ℝ := fun l ω => H (dyTime t (n + m) l) ω - H (dyTime t n (l / 2 ^ m)) ω
    have hcm : ∀ l : ℕ, l < 2 ^ (n + m) → Measurable[completedBrownianPast P W
        (fun _ => x₀) ((l : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m))] (c l) := by
      intro l hl
      have := hckm (l / 2 ^ m) m l hl
      simpa only [ck, ↓reduceIte] using this
    have hcb : ∀ l : ℕ, l < 2 ^ (n + m) → ∀ ω, |c l ω| ≤ 2 * R := by
      intro l hl ω
      have := hckb (l / 2 ^ m) m l hl ω
      simpa only [ck, ↓reduceIte] using this
    have hco : ∀ ω, ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η →
        ∀ l : ℕ, l < 2 ^ (n + m) → |c l ω| ≤ η := by
      intro ω hno l hl
      by_contra hcon
      push Not at hcon
      refine hno (Set.mem_iUnion.2 ⟨((n + m, l), (n, l / 2 ^ m)), hl.le, ?_, ?_, hcon⟩)
      · show l / 2 ^ m ≤ 2 ^ n
        rw [pow_add] at hl
        exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hl |>.le
      · show |(dyTime t (n + m) l : ℝ) - dyTime t n (l / 2 ^ m)| ≤ (t : ℝ) / 2 ^ n
        have hc := dyTime_coarse t n m l
        rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hc.1))]
        exact hc.2
    have hI := itoStepSum_sq_integral_le_of_off hW x₀ j t (n + m) c hcm hcb _ hco
    have hiso := itoStepSum_isometry hW x₀ t (n + m) j c hcm (2 * R) hcb
    have hint : ∀ k ∈ Finset.range (2 ^ n), Integrable (fun ω => D k m ω ^ 2) P :=
      fun k _ => (hDL2 k m).integrable_sq
    have hsumint : ∫ ω, ∑ k ∈ Finset.range (2 ^ n), D k m ω ^ 2 ∂P =
        ∫ ω, (itoStepSum (fun s ω => W s ω j) t (n + m) c ω) ^ 2 ∂P := by
      rw [integral_finsetSum _ hint, hiso]
      have hk : ∀ k ∈ Finset.range (2 ^ n), ∫ ω, D k m ω ^ 2 ∂P =
          ∑ l ∈ Finset.range (2 ^ (n + m)), (∫ ω, ck k m l ω ^ 2 ∂P) *
            ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ) :=
        fun k _ => itoStepSum_isometry hW x₀ t (n + m) j (ck k m) (hckm k m) (2 * R) (hckb k m)
      rw [Finset.sum_congr rfl hk, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l / 2 ^ m ∈ Finset.range (2 ^ n) := by
        have := Finset.mem_range.1 hl
        rw [pow_add] at this
        exact Finset.mem_range.2 ((Nat.div_lt_iff_lt_mul (by positivity)).2 this)
      rw [Finset.sum_eq_single (l / 2 ^ m)]
      · simp only [ck, c, ↓reduceIte]
      · intro b _ hb
        simp [ck, Ne.symm hb]
      · intro h; exact absurd hl' h
    have hnn : ∀ ω, 0 ≤ ∑ k ∈ Finset.range (2 ^ n), D k m ω ^ 2 :=
      fun ω => Finset.sum_nonneg fun k _ => sq_nonneg _
    have hm2 := mul_meas_ge_le_integral_of_nonneg (μ := P) (Eventually.of_forall hnn)
      (integrable_finsetSum _ hint) ε
    refine le_trans (measure_mono (t := {ω | ε ≤ ∑ k ∈ Finset.range (2 ^ n), D k m ω ^ 2})
      fun ω hω => ?_) ?_
    · show ε ≤ _
      have : ε ≤ |∑ k ∈ Finset.range (2 ^ n), D k m ω ^ 2| := hω
      rwa [abs_of_nonneg (hnn ω)] at this
    · rw [← ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ hε, mul_comm]
      calc ε * P.real {ω | ε ≤ ∑ k ∈ Finset.range (2 ^ n), D k m ω ^ 2}
          ≤ ∫ ω, ∑ k ∈ Finset.range (2 ^ n), D k m ω ^ 2 ∂P := hm2
        _ = _ := hsumint
        _ ≤ _ := hI
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Eventually.of_forall fun _ => le_top
  have he' : 0 < e.toReal := ENNReal.toReal_pos he.ne' hetop
  have hε' : 0 < ε / 2 := by positivity
  set c0 : ℝ := e.toReal * (ε / 2) / 2 with hc0
  have hc0pos : 0 < c0 := by positivity
  set η : ℝ := min 1 (c0 / (t + 1)) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ^ 2 * t ≤ c0 := by
    have h1 : η ≤ 1 := min_le_left _ _
    have h2 : η ≤ c0 / (t + 1) := min_le_right _ _
    have h3 : η * (t + 1) ≤ c0 := (le_div_iff₀ (by positivity)).1 h2
    calc η ^ 2 * t = η * (η * t) := by ring
      _ ≤ 1 * (η * (t + 1)) := by
          gcongr
          linarith
      _ ≤ c0 := by linarith only [h3]
  have hosc := oscSet_tendsto hHae hHc t hη
  set δ : ℝ := c0 / ((2 * R) ^ 2 * t + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδX : δ * ((2 * R) ^ 2 * t + 1) = c0 := div_mul_cancel₀ _ (by positivity)
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hosc) (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.2 hδ)] with n hn
  have hreal : P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) ≤ δ := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hδ.le hn
  refine le_trans (measure_mono fun ω hω => ?_) ((step n (ε / 2) hε' η hη.le).trans ?_)
  · simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
    linarith only [hω]
  · rw [← ENNReal.ofReal_toReal hetop]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hε']
    have hX : (2 * R) ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) ≤
        (2 * R) ^ 2 * t * δ := by gcongr
    have hX2 : (2 * R) ^ 2 * t * δ ≤ c0 := by linarith only [hδX, hδ]
    linarith only [hη1, hX, hX2, hc0]

end M8e


section M8f
variable [MeasurableSpace Ω]

/-- M8f: the squared cell errors of a continuous adapted Ito integral vanish in probability
(no boundedness; localized from `cellErr_sq_tendsto_bdd`). -/
theorem cellErr_sq_tendsto {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), cellErr W j H J t n k ω ^ 2)
      atTop (fun _ => 0) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  refine tendstoInMeasure_of_local fun δ hδ => ?_
  obtain ⟨R0, hR0δ, hR01⟩ :=
    (((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHae hHc t)) δ hδ).and
      (eventually_ge_atTop 1)).exists
  set R : ℝ := (R0 : ℝ) with hRdef
  have hR : 0 < R := by rw [hRdef]; exact_mod_cast hR01
  set H' : ℝ≥0 → Ω → ℝ := clampH H R with hH'
  have hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s) :=
    fun s => clampH_measurable (hHm s) R
  have hH'c : ∀ ω, Continuous fun s => H' s ω := clampH_continuous hHc R
  obtain ⟨J', hJ'⟩ := exists_hasBrownianItoIntegral hW x₀ j hH'm hH'c
  have hg := cellErr_sq_tendsto_bdd hW x₀ j hH'm hH'c hR (abs_clampH_le H hR.le) hJ' t
  set B : Set Ω := bigSet H t R with hB
  have hJJ : ∀ n k : ℕ, k ≤ 2 ^ n →
      ∀ᵐ ω ∂P, ω ∈ Bᶜ → J (dyTime t n k) ω = J' (dyTime t n k) ω := by
    intro n k hk
    refine hasBrownianItoIntegral_eq_on hW x₀ j hHm hHc hH'm hH'c hJ hJ' (dyTime t n k) Bᶜ
      fun ω hω N i hi => ?_
    have hik : i * k ≤ 2 ^ (n + N) := by
      rw [pow_add, mul_comm (2 ^ n)]; exact Nat.mul_le_mul hi hk
    rw [dyTime_dyTime]
    exact (clampH_eq_of_abs_le H (abs_le_of_not_mem_bigSet hω hik)).symm
  have hall : ∀ᵐ ω ∂P, ∀ n k : ℕ, k ≤ 2 ^ n → ω ∈ Bᶜ →
      J (dyTime t n k) ω = J' (dyTime t n k) ω := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    by_cases hk : k ≤ 2 ^ n
    · filter_upwards [hJJ n k hk] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hk
  set N : Set Ω := {ω | ¬ ∀ n k : ℕ, k ≤ 2 ^ n → ω ∈ Bᶜ →
      J (dyTime t n k) ω = J' (dyTime t n k) ω} with hN
  have hN0 : P N = 0 := by rw [hN, ← ae_iff]; exact hall
  refine ⟨B ∪ N, ?_, _, _, hg, ?_, Eventually.of_forall fun _ _ => rfl⟩
  · calc P (B ∪ N) ≤ P B + P N := measure_union_le _ _
      _ = P B := by rw [hN0, add_zero]
      _ ≤ δ := hR0δ
  · refine Eventually.of_forall fun n ω hω => Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hωB : ω ∈ Bᶜ := fun h => hω (Or.inl h)
    have hωN : ω ∉ N := fun h => hω (Or.inr h)
    simp only [hN, Set.mem_setOf_eq, not_not] at hωN
    unfold cellErr
    rw [hωN n k hk'.le hωB, hωN n (k + 1) hk' hωB, hH',
      clampH_eq_of_abs_le H (abs_le_of_not_mem_bigSet hωB hk'.le)]

end M8f


section M8f2
variable [MeasurableSpace Ω]

theorem itoStepValue_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, itoStepValue t n c u ω =
      (∑ k ∈ Finset.range (2 ^ n), c k ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith only [this]
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

/-- M8f: left-point Riemann sums of a pathwise continuous process converge pathwise. -/
theorem riemann_tendsto {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 (∫ u in (0 : ℝ)..t.val, H u.toNNReal ω)) := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (t.val + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hempty := iInter_oscSet_eq_empty hHc t hη
  have hex : ∃ n0 : ℕ, ω ∉ oscSet H t ((t : ℝ) / 2 ^ n0) η := by
    by_contra h
    push_neg at h
    have hmem : ω ∈ (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) := Set.mem_iInter.2 h
    rw [hempty] at hmem
    exact hmem
  obtain ⟨n0, hn0⟩ := hex
  refine ⟨n0, fun n hn => ?_⟩
  have hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h => hn0 (oscSet_mono H t
    (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hn)) η h)
  have hI := itoStepValue_integral t n (fun k ω => H (dyTime t n k) ω) ω
  have hHi : IntervalIntegrable (fun u : ℝ => H u.toNNReal ω) volume 0 t.val :=
    ((hHc ω).comp continuous_real_toNNReal).intervalIntegrable _ _
  rw [Real.dist_eq, ← hI, ← intervalIntegral.integral_sub
    (itoStepValue_intervalIntegrable _ _ _ _) hHi]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖itoStepValue t n (fun k ω => H (dyTime t n k) ω) u ω - H u.toNNReal ω‖ ≤ η := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ :=
      itoStepValue_eq_cell t n (fun k ω => H (dyTime t n k) ω) hu ω
    rw [hval, Real.norm_eq_abs]
    exact abs_H_sub_le_of_not_mem_oscSet hHc t n k hη.le hω hk hu.1.le hlo.le hhi hu.2
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at hle
  refine lt_of_le_of_lt hle ?_
  rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  linarith only [mul_nonneg hε.le ht, hε]

theorem riemann_tendstoInMeasure {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) :
    TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop
      (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω) :=
  tendstoInMeasure_of_tendsto_ae
    (fun n => ((Finset.aestronglyMeasurable_sum (Finset.range (2 ^ n))
      fun k _ => hHm (dyTime t n k)).mul_const (((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ))).congr
      (Eventually.of_forall fun ω => by simp only [Finset.sum_apply]))
    (Eventually.of_forall fun ω => riemann_tendsto hHc t ω)

/-- Localized QV: weighted QV sums with a continuous adapted (unbounded) weight vanish. -/
theorem qvSum_tendsto_loc {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j j' : Fin d) (t : ℝ≥0)
    {C : ℝ≥0 → Ω → ℝ}
    (hCm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (C s))
    (hCc : ∀ ω, Continuous fun s => C s ω) :
    TendstoInMeasure P (fun N => qvSum W j j' t N (fun k => C (dyTime t N k))) atTop
      (fun _ => 0) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hCae : ∀ s, AEStronglyMeasurable (C s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hCm s)
  refine tendstoInMeasure_of_local fun δ hδ => ?_
  obtain ⟨R0, hR0δ, hR01⟩ :=
    (((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hCae hCc t)) δ hδ).and
      (eventually_ge_atTop 1)).exists
  set R : ℝ := (R0 : ℝ) with hRdef
  have hR : 0 < R := by rw [hRdef]; exact_mod_cast hR01
  have hg := qvSum_tendstoInMeasure_zero hW x₀ j j' t
    (fun N k => clampH C R (dyTime t N k))
    (fun N k _ => clampH_measurable (hCm (dyTime t N k)) R) hR.le
    (fun N k _ ω => abs_clampH_le C hR.le _ ω)
  refine ⟨bigSet C t R, hR0δ, _, _, hg, Eventually.of_forall fun N ω hω => ?_,
    Eventually.of_forall fun _ _ => rfl⟩
  unfold qvSum
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [clampH_eq_of_abs_le C (abs_le_of_not_mem_bigSet hω (Finset.mem_range.1 hl).le)]

theorem wSum_eq_qvSum (W : ℝ≥0 → Ω → SDEState d) (j j' : Fin d) (t : ℝ≥0) (n : ℕ)
    (C : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ∑ k ∈ Finset.range (2 ^ n), C (dyTime t n k) ω *
      ((W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j) *
        (W (dyTime t n (k + 1)) ω j' - W (dyTime t n k) ω j')) =
    qvSum W j j' t n (fun k => C (dyTime t n k)) ω +
      (if j = j' then (∑ k ∈ Finset.range (2 ^ n), C (dyTime t n k) ω) *
        ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) else 0) := by
  unfold qvSum
  split_ifs with h
  · rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dyTime, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [add_zero, sub_zero, dyTime, Nat.cast_add, Nat.cast_one]

/-- M8f: `Σ_k C(t_k) ΔW^j_k ΔW^{j'}_k → [j = j'] ∫_0^t C du` in probability. -/
theorem wSum_tendsto {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j j' : Fin d) (t : ℝ≥0)
    {C : ℝ≥0 → Ω → ℝ}
    (hCm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (C s))
    (hCc : ∀ ω, Continuous fun s => C s ω) :
    TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), C (dyTime t n k) ω *
      ((W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j) *
        (W (dyTime t n (k + 1)) ω j' - W (dyTime t n k) ω j'))) atTop
      (fun ω => if j = j' then ∫ u in (0 : ℝ)..t.val, C u.toNNReal ω else 0) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hCae : ∀ s, AEStronglyMeasurable (C s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hCm s)
  have hq := qvSum_tendsto_loc hW x₀ j j' t hCm hCc
  have hr : TendstoInMeasure P (fun n ω => if j = j' then
      (∑ k ∈ Finset.range (2 ^ n), C (dyTime t n k) ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)
      else 0) atTop (fun ω => if j = j' then ∫ u in (0 : ℝ)..t.val, C u.toNNReal ω else 0) := by
    by_cases h : j = j'
    · subst h; simpa only [↓reduceIte] using riemann_tendstoInMeasure hCae hCc t
    · simpa only [h, ↓reduceIte] using
        (tendstoInMeasure_zero_const (ι := ℕ) (l := atTop) (P := P))
  exact TendstoInMeasure.congr'
    (Eventually.of_forall fun n => Eventually.of_forall fun ω =>
      (wSum_eq_qvSum W j j' t n C ω).symm)
    (Eventually.of_forall fun ω => zero_add _) (tendstoInMeasure_add_real hq hr)

end M8f2


section M8f3
variable [MeasurableSpace Ω]

theorem tendstoInMeasure_zero_of_sq_le {P : Measure Ω} {X Y : ℕ → Ω → ℝ}
    (hY : TendstoInMeasure P Y atTop (fun _ => 0)) (h : ∀ n ω, X n ω ^ 2 ≤ Y n ω) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY (ε ^ 2) (by positivity))
    (fun _ => bot_le) (fun n => measure_mono fun ω hω => ?_)
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
  calc ε ^ 2 ≤ |X n ω| ^ 2 := pow_le_pow_left₀ hε.le hω 2
    _ = X n ω ^ 2 := sq_abs _
    _ ≤ Y n ω := h n ω
    _ ≤ |Y n ω| := le_abs_self _

theorem riemann_aesm {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (fun ω => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) P :=
  ((Finset.aestronglyMeasurable_sum (Finset.range (2 ^ n))
      fun k _ => hHm (dyTime t n k)).mul_const (((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ))).congr
      (Eventually.of_forall fun ω => by simp only [Finset.sum_apply])

theorem integral_aesm {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) : AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω) P :=
  TendstoInMeasure.aestronglyMeasurable (fun n => riemann_aesm hHm t n)
    (riemann_tendstoInMeasure hHm hHc t)

/-- Cross terms `Σ C(t_k) ΔW^j_k E_k` vanish when `Σ E_k² → 0`. -/
theorem cross_tendsto_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) (t : ℝ≥0)
    {C : ℝ≥0 → Ω → ℝ}
    (hCm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (C s))
    (hCc : ∀ ω, Continuous fun s => C s ω) {E : ℕ → ℕ → Ω → ℝ}
    (hE : TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), E n k ω ^ 2) atTop
      (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), C (dyTime t n k) ω *
      ((W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j) * E n k ω)) atTop (fun _ => 0) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hA := wSum_tendsto hW x₀ j j t (C := fun s ω => C s ω ^ 2)
    (fun s => (hCm s).pow_const 2) (fun ω => (hCc ω).pow 2)
  simp only [eq_self_iff_true, ↓reduceIte] at hA
  have hm : AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..t.val, C u.toNNReal ω ^ 2) P :=
    integral_aesm (H := fun s ω => C s ω ^ 2)
      (fun s => (aestronglyMeasurable_of_completedPast hW x₀ _ (hCm s)).pow 2)
      (fun ω => (hCc ω).pow 2) t
  have hprod := tendstoInMeasure_mul_real hA hE hm aestronglyMeasurable_const
  simp only [mul_zero] at hprod
  refine tendstoInMeasure_zero_of_sq_le hprod fun n ω => ?_
  calc (∑ k ∈ Finset.range (2 ^ n), C (dyTime t n k) ω *
        ((W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j) * E n k ω)) ^ 2
      = (∑ k ∈ Finset.range (2 ^ n), (C (dyTime t n k) ω *
        (W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j)) * E n k ω) ^ 2 := by
        congr 1; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (∑ k ∈ Finset.range (2 ^ n), (C (dyTime t n k) ω *
        (W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j)) ^ 2) *
        ∑ k ∈ Finset.range (2 ^ n), E n k ω ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ k ∈ Finset.range (2 ^ n), C (dyTime t n k) ω ^ 2 *
        ((W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j) *
          (W (dyTime t n (k + 1)) ω j - W (dyTime t n k) ω j))) *
        ∑ k ∈ Finset.range (2 ^ n), E n k ω ^ 2 := by
        congr 1; exact Finset.sum_congr rfl fun k _ => by ring

/-- `Σ B(t_k) E1_k E2_k → 0` when `Σ E1² → 0` and `Σ E2² → 0` (localized in `B`). -/
theorem errProd_tendsto_zero {P : Measure Ω} [IsFiniteMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (B s))
    (hBc : ∀ ω, Continuous fun s => B s ω) {E1 E2 : ℕ → ℕ → Ω → ℝ}
    (h1 : TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), E1 n k ω ^ 2) atTop
      (fun _ => 0))
    (h2 : TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), E2 n k ω ^ 2) atTop
      (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), B (dyTime t n k) ω *
      (E1 n k ω * E2 n k ω)) atTop (fun _ => 0) := by
  have hBae : ∀ s, AEStronglyMeasurable (B s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hBm s)
  refine tendstoInMeasure_of_local fun δ hδ => ?_
  obtain ⟨R0, hR0δ, hR01⟩ :=
    (((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hBae hBc t)) δ hδ).and
      (eventually_ge_atTop 1)).exists
  set R : ℝ := (R0 : ℝ) with hRdef
  have hR : 0 < R := by rw [hRdef]; exact_mod_cast hR01
  refine ⟨bigSet B t R, hR0δ, fun n ω => ∑ k ∈ Finset.range (2 ^ n),
    clampH B R (dyTime t n k) ω * (E1 n k ω * E2 n k ω), fun _ => 0, ?_,
    Eventually.of_forall fun n ω hω => ?_, Eventually.of_forall fun _ _ => rfl⟩
  · refine tendstoInMeasure_zero_of_abs_le hR h1 h2 fun n ω => ?_
    calc |∑ k ∈ Finset.range (2 ^ n), clampH B R (dyTime t n k) ω * (E1 n k ω * E2 n k ω)|
        ≤ ∑ k ∈ Finset.range (2 ^ n), |clampH B R (dyTime t n k) ω * (E1 n k ω * E2 n k ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (2 ^ n), R * (E1 n k ω ^ 2 + E2 n k ω ^ 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          have hc := abs_clampH_le B hR.le (dyTime t n k) ω
          have h3 : |E1 n k ω * E2 n k ω| ≤ E1 n k ω ^ 2 + E2 n k ω ^ 2 := by
            rw [abs_mul]
            linarith only [sq_nonneg (|E1 n k ω| - |E2 n k ω|), sq_abs (E1 n k ω),
              sq_abs (E2 n k ω), mul_nonneg (abs_nonneg (E1 n k ω)) (abs_nonneg (E2 n k ω))]
          exact mul_le_mul hc h3 (abs_nonneg _) hR.le
      _ = R * (∑ k ∈ Finset.range (2 ^ n), E1 n k ω ^ 2 +
          ∑ k ∈ Finset.range (2 ^ n), E2 n k ω ^ 2) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ R * (|∑ k ∈ Finset.range (2 ^ n), E1 n k ω ^ 2| +
          |∑ k ∈ Finset.range (2 ^ n), E2 n k ω ^ 2|) := by
          gcongr <;> exact le_abs_self _
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [clampH_eq_of_abs_le B (abs_le_of_not_mem_bigSet hω (Finset.mem_range.1 hk).le)]

/-- M8f: quadratic covariation of Ito integrals along the dyadic grid:
`Σ_k B(t_k) ΔJ1_k ΔJ2_k → [j = j'] ∫_0^t B H1 H2 du` in probability. -/
theorem qvJ_tendsto {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j j' : Fin d) (t : ℝ≥0)
    {B H1 H2 J1 J2 : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (B s))
    (hBc : ∀ ω, Continuous fun s => B s ω)
    (hH1m : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H1 s))
    (hH1c : ∀ ω, Continuous fun s => H1 s ω)
    (hH2m : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H2 s))
    (hH2c : ∀ ω, Continuous fun s => H2 s ω)
    (hJ1 : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H1 J1)
    (hJ2 : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j') H2 J2) :
    TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n), B (dyTime t n k) ω *
      ((J1 (dyTime t n (k + 1)) ω - J1 (dyTime t n k) ω) *
        (J2 (dyTime t n (k + 1)) ω - J2 (dyTime t n k) ω))) atTop
      (fun ω => if j = j' then ∫ u in (0 : ℝ)..t.val,
        B u.toNNReal ω * H1 u.toNNReal ω * H2 u.toNNReal ω else 0) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hS1 := wSum_tendsto hW x₀ j j' t (C := fun s ω => B s ω * H1 s ω * H2 s ω)
    (fun s => ((hBm s).mul (hH1m s)).mul (hH2m s)) (fun ω => ((hBc ω).mul (hH1c ω)).mul (hH2c ω))
  have hE1 := cellErr_sq_tendsto hW x₀ j hH1m hH1c hJ1 t
  have hE2 := cellErr_sq_tendsto hW x₀ j' hH2m hH2c hJ2 t
  have hS2 := cross_tendsto_zero hW x₀ j t (C := fun s ω => B s ω * H1 s ω)
    (fun s => (hBm s).mul (hH1m s)) (fun ω => (hBc ω).mul (hH1c ω))
    (E := fun n k ω => cellErr W j' H2 J2 t n k ω) hE2
  have hS3 := cross_tendsto_zero hW x₀ j' t (C := fun s ω => B s ω * H2 s ω)
    (fun s => (hBm s).mul (hH2m s)) (fun ω => (hBc ω).mul (hH2c ω))
    (E := fun n k ω => cellErr W j H1 J1 t n k ω) hE1
  have hS4 := errProd_tendsto_zero hW x₀ t hBm hBc
    (E1 := fun n k ω => cellErr W j H1 J1 t n k ω)
    (E2 := fun n k ω => cellErr W j' H2 J2 t n k ω) hE1 hE2
  have hsum := tendstoInMeasure_add_real
    (tendstoInMeasure_add_real (tendstoInMeasure_add_real hS1 hS2) hS3) hS4
  refine TendstoInMeasure.congr' (Eventually.of_forall fun n => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => by simp only [add_zero]) hsum
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold cellErr
  ring

end M8f3


section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g


section M8g2

end M8g2


section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

end M8g4

section M8g5
variable [MeasurableSpace Ω]

theorem dyTime_at_top (t : ℝ≥0) (n : ℕ) : dyTime t n (2 ^ n) = t := by
  unfold dyTime; push_cast
  exact mul_div_cancel_left₀ t (pow_ne_zero _ two_ne_zero)

end M8g5

section M9a
variable [MeasurableSpace Ω]

theorem abs_clampH_le_abs (H : ℝ≥0 → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (s : ℝ≥0) (ω : Ω) :
    |clampH H R s ω| ≤ |H s ω| := by
  unfold clampH
  rw [abs_le]
  exact ⟨le_max_of_le_right (le_min (neg_abs_le _) (by linarith [abs_nonneg (H s ω)])),
    max_le (by linarith [abs_nonneg (H s ω)]) ((min_le_left _ _).trans (le_abs_self _))⟩

end M9a


section M9c

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF

end M9cF


section M9c2

end M9c2


section M9d

end M9d


section M9d2

end M9d2



section M9e1

end M9e1


section M9e2

end M9e2


end ItoLib

open EthierKurtz in



set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Generic transfer: a bigger filtration and an a.e.-equal driver keep the Ito relation. -/
lemma hasIto_lift {P : Measure Ω} {ℱ ℱ' : ℝ≥0 → MeasurableSpace Ω} (hle : ∀ t, ℱ t ≤ ℱ' t)
    {V V' H J : ℝ≥0 → Ω → ℝ} (hV : ∀ᵐ ω ∂P, ∀ t, V' t ω = V t ω)
    (h : HasBrownianItoIntegral P ℱ V H J) : HasBrownianItoIntegral P ℱ' V' H J := by
  refine ⟨h.1, fun t => ?_⟩
  obtain ⟨a, ham, haC, haH, haJ⟩ := h.2 t
  refine ⟨a, fun n k hk => (ham n k hk).mono (hle _) le_rfl, haC, haH, ?_⟩
  refine haJ.congr_left (fun n => ?_)
  filter_upwards [hV] with ω hω
  simp only [itoStepSum, hω]

lemma pair_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    Measurable (fun ω => (M.B t ω, M.Bt t ω)) := by
  have h1 : MeasurableSpace.comap (fun ω => (M.B t ω, M.Bt t ω)) inferInstance ≤ M.F t := by
    rw [hM.filtF t]
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le (f := fun s (_ : s ≤ t) =>
      MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance) t le_rfl le_rfl
  exact Measurable.of_comap_le (h1.trans (M.F.le t))

lemma B_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.B t) :=
  measurable_fst.comp (pair_measurable M hM t)

lemma Bt_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.Bt t) :=
  measurable_snd.comp (pair_measurable M hM t)

/-- The exceptional null set off which both Brownian paths are continuous. -/
def Nbad (M : Model p Ω) : Set Ω :=
  toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}

lemma Nbad_meas (M : Model p Ω) : MeasurableSet (Nbad M) := measurableSet_toMeasurable _ _

lemma Nbad_null (M : Model p Ω) (hM : M.Standing) : M.P (Nbad M) = 0 := by
  rw [Nbad, measure_toMeasurable]
  exact ae_iff.1 (hM.brownB.cont.and hM.brownBt.cont)

lemma not_Nbad (M : Model p Ω) {ω : Ω} (h : ω ∉ Nbad M) :
    Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω) := by
  by_contra h'
  exact h (subset_toMeasurable _ _ h')

lemma ae_not_Nbad (M : Model p Ω) (hM : M.Standing) : ∀ᵐ ω ∂M.P, ω ∉ Nbad M := by
  rw [ae_iff]; simpa using Nbad_null M hM

open Classical in
/-- The two coordinates, set to `0` on `Nbad`. -/
noncomputable def gB (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ Nbad M then 0 else M.B t ω

open Classical in
noncomputable def gBt (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ Nbad M then 0 else M.Bt t ω

/-- The standard 2-d Brownian motion `(B, B~)` with everywhere continuous paths. -/
noncomputable def W (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : SDEState 2 :=
  WithLp.toLp 2 ![gB M t ω, gBt M t ω]

@[simp] lemma W_zero (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : W M t ω 0 = gB M t ω := by
  simp [W]

@[simp] lemma W_one (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : W M t ω 1 = gBt M t ω := by
  simp [W]

lemma ae_W (M : Model p Ω) (hM : M.Standing) :
    ∀ᵐ ω ∂M.P, ∀ t, W M t ω 0 = M.B t ω ∧ W M t ω 1 = M.Bt t ω := by
  filter_upwards [ae_not_Nbad M hM] with ω hω t
  simp [gB, gBt, hω]

lemma gB_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (gB M t) :=
  Measurable.ite (Nbad_meas M) measurable_const (B_measurable M hM t)

lemma gBt_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (gBt M t) :=
  Measurable.ite (Nbad_meas M) measurable_const (Bt_measurable M hM t)

lemma W_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (W M t) := by
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  fin_cases i
  · simpa using gB_measurable M hM t
  · simpa using gBt_measurable M hM t

lemma gB_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => gB M t ω) := by
  by_cases h : ω ∈ Nbad M
  · simp only [gB, h, if_true]; exact continuous_const
  · simp only [gB, h, if_false]; exact (not_Nbad M h).1

lemma gBt_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => gBt M t ω) := by
  by_cases h : ω ∈ Nbad M
  · simp only [gBt, h, if_true]; exact continuous_const
  · simp only [gBt, h, if_false]; exact (not_Nbad M h).2

lemma W_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => W M t ω) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · simpa using gB_cont M ω
  · simpa using gBt_cont M ω

lemma gB_brownian (M : Model p Ω) (hM : M.Standing) : IsBrownianReal (gB M) M.P := by
  have hae : ∀ t, M.B t =ᵐ[M.P] gB M t := by
    intro t
    filter_upwards [ae_not_Nbad M hM] with ω hω
    simp [gB, hω]
  exact { toIsPreBrownianReal := hM.brownB.toIsPreBrownianReal.congr hae,
          cont := Eventually.of_forall fun ω => gB_cont M ω }

lemma gBt_brownian (M : Model p Ω) (hM : M.Standing) : IsBrownianReal (gBt M) M.P := by
  have hae : ∀ t, M.Bt t =ᵐ[M.P] gBt M t := by
    intro t
    filter_upwards [ae_not_Nbad M hM] with ω hω
    simp [gBt, hω]
  exact { toIsPreBrownianReal := hM.brownBt.toIsPreBrownianReal.congr hae,
          cont := Eventually.of_forall fun ω => gBt_cont M ω }

lemma gB_indep (M : Model p Ω) (hM : M.Standing) :
    IndepFun (fun ω t => gB M t ω) (fun ω t => gBt M t ω) M.P := by
  refine hM.indep.congr ?_ ?_
  · filter_upwards [ae_not_Nbad M hM] with ω hω
    funext t; simp [gB, hω]
  · filter_upwards [ae_not_Nbad M hM] with ω hω
    funext t; simp [gBt, hω]

lemma iIndepFun_fin_two {β : Type*} [MeasurableSpace β] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Fin 2 → Ω → β} (h : IndepFun (f 0) (f 1) μ) : iIndepFun f μ := by
  have hcases : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hS
  rcases hcases S with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · have h0 := hS 0 (by simp)
    have h1 := hS 1 (by simp)
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
    have := h _ _ h0 h1
    have hI : (⋂ i, f i ⁻¹' sets i) = f 0 ⁻¹' sets 0 ∩ f 1 ⁻¹' sets 1 := by
      ext ω; simp [Fin.forall_fin_two]
    simpa [Fin.prod_univ_two, hI] using this

lemma isStandardBrownian (M : Model p Ω) (hM : M.Standing) : IsStandardBrownian M.P (W M) := by
  refine ⟨W_measurable M hM, W_cont M, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using gB_brownian M hM
    · simpa using gBt_brownian M hM
  · have := hM.prob
    apply iIndepFun_fin_two
    simpa using gB_indep M hM

lemma cBP_null (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) (A : Set Ω) (hA : A ⊆ Nbad M) :
    MeasurableSet[completedBrownianPast M.P (W M) (fun _ => 0) t] A := by
  have h1 : MeasurableSet[MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N}] A :=
    MeasurableSpace.measurableSet_generateFrom ⟨Nbad M, Nbad_meas M, Nbad_null M hM, hA⟩
  exact (le_sup_right : MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N} ≤ _) A h1

lemma cBP_nullset (M : Model p Ω) (t : ℝ≥0) (N : Set Ω) (hN : MeasurableSet N) (hN0 : M.P N = 0) :
    MeasurableSet[completedBrownianPast M.P (W M) (fun _ => 0) t] N := by
  have h1 : MeasurableSet[MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N}] N :=
    MeasurableSpace.measurableSet_generateFrom ⟨N, hN, hN0, subset_rfl⟩
  exact (le_sup_right : MeasurableSpace.generateFrom
      {A : Set Ω | ∃ N : Set Ω, MeasurableSet N ∧ M.P N = 0 ∧ A ⊆ N} ≤ _) N h1

lemma W_meas_cBP (M : Model p Ω) (t s : ℝ≥0) (hs : s ≤ t) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (W M s) := by
  refine Measurable.of_comap_le ?_
  refine le_sup_of_le_left (le_sup_of_le_left ?_)
  exact le_iSup (f := fun s' : Set.Iic t => MeasurableSpace.comap (W M s'.val) inferInstance)
    ⟨s, hs⟩

lemma pairW_meas_cBP (M : Model p Ω) (t s : ℝ≥0) (hs : s ≤ t) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t]
      (fun ω => (W M s ω 0, W M s ω 1)) :=
  ((measurable_pi_apply 0).comp ((WithLp.measurable_ofLp 2 _).comp (W_meas_cBP M t s hs))).prodMk
    ((measurable_pi_apply 1).comp ((WithLp.measurable_ofLp 2 _).comp (W_meas_cBP M t s hs)))

/-- The model filtration sits inside the completed Brownian past of `W`. -/
lemma F_le_cBP (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    M.F t ≤ completedBrownianPast M.P (W M) (fun _ => 0) t := by
  rw [hM.filtF t]
  refine sup_le (iSup₂_le fun s hs => ?_) ?_
  · refine Measurable.comap_le ?_
    intro S hS
    have hset : (fun ω => (M.B s ω, M.Bt s ω)) ⁻¹' S =
        ((fun ω => (M.B s ω, M.Bt s ω)) ⁻¹' S ∩ Nbad M) ∪
          ((Nbad M)ᶜ ∩ (fun ω => (W M s ω 0, W M s ω 1)) ⁻¹' S) := by
      ext ω
      by_cases h : ω ∈ Nbad M <;> simp [h, gB, gBt]
    rw [hset]
    refine MeasurableSet.union (cBP_null M hM t _ Set.inter_subset_right) ?_
    exact MeasurableSet.inter (cBP_null M hM t _ subset_rfl).compl (pairW_meas_cBP M t s hs hS)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro N ⟨hN, hN0⟩
    exact cBP_nullset M t N hN hN0

/-- Transfer of a `dB` Ito integral of the model to the library setting (coordinate 0). -/
lemma hasIto_B (M : Model p Ω) (hM : M.Standing) {H J : ℝ≥0 → Ω → ℝ}
    (h : HasBrownianItoIntegral M.P (fun t => M.F t) M.B H J) :
    HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) H J :=
  hasIto_lift (F_le_cBP M hM) ((ae_W M hM).mono fun _ h t => (h t).1) h

/-- Model-adapted processes are measurable for the library filtration. -/
lemma meas_cBP_of_F (M : Model p Ω) (hM : M.Standing) {Y : ℝ≥0 → Ω → ℝ}
    (hY : ∀ s, StronglyMeasurable[M.F s] (Y s)) (s : ℝ≥0) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s] (Y s) :=
  ((hY s).measurable).mono (F_le_cBP M hM s) le_rfl

end StochCalcBr


set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Dyadic grid of `[0, t]` (same as `ItoLib.dyTime`). -/
noncomputable def dyT (t : ℝ≥0) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) * t / (2 : ℝ≥0) ^ n

lemma dyT_coe (t : ℝ≥0) (n k : ℕ) : (dyT t n k : ℝ) = (k : ℝ) * t / 2 ^ n := by
  simp [dyT]

lemma sum_sq_cell_le (g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (M : ℝ)
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) T, |g u| ≤ M) (n : ℕ) :
    ∑ k ∈ Finset.range (2 ^ n),
        (∫ u in ((k : ℝ) * T / 2 ^ n)..(((k + 1 : ℕ) : ℝ) * T / 2 ^ n), g u) ^ 2
      ≤ M ^ 2 * T ^ 2 / 2 ^ n := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hcell : ∀ k ∈ Finset.range (2 ^ n),
      (∫ u in ((k : ℝ) * T / 2 ^ n)..(((k + 1 : ℕ) : ℝ) * T / 2 ^ n), g u) ^ 2
        ≤ (M * (T / 2 ^ n)) ^ 2 := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ 2 ^ n := by
      have := Finset.mem_range.1 hk
      exact_mod_cast this
    have hab : (k : ℝ) * T / 2 ^ n ≤ ((k + 1 : ℕ) : ℝ) * T / 2 ^ n := by
      apply div_le_div_of_nonneg_right _ h2n.le
      push_cast; nlinarith
    have hbound : ‖∫ u in ((k : ℝ) * T / 2 ^ n)..(((k + 1 : ℕ) : ℝ) * T / 2 ^ n), g u‖ ≤
        M * |((k + 1 : ℕ) : ℝ) * T / 2 ^ n - (k : ℝ) * T / 2 ^ n| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      apply hM
      constructor
      · have : 0 ≤ (k : ℝ) * T / 2 ^ n := by positivity
        linarith [hx.1]
      · have : ((k + 1 : ℕ) : ℝ) * T / 2 ^ n ≤ T := by
          rw [div_le_iff₀ h2n]; push_cast; nlinarith
        linarith [hx.2]
    have hlen : |((k + 1 : ℕ) : ℝ) * T / 2 ^ n - (k : ℝ) * T / 2 ^ n| = T / 2 ^ n := by
      rw [abs_of_nonneg (by linarith)]
      push_cast; ring
    rw [hlen, Real.norm_eq_abs] at hbound
    have hM0 : 0 ≤ M * (T / 2 ^ n) := le_trans (abs_nonneg _) hbound
    calc _ = |∫ u in ((k : ℝ) * T / 2 ^ n)..(((k + 1 : ℕ) : ℝ) * T / 2 ^ n), g u| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (M * (T / 2 ^ n)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  calc _ ≤ ∑ k ∈ Finset.range (2 ^ n), (M * (T / 2 ^ n)) ^ 2 := Finset.sum_le_sum hcell
    _ = M ^ 2 * T ^ 2 / 2 ^ n := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp

lemma tendsto_sum_sq_cell (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
        (∫ u in ((k : ℝ) * T / 2 ^ n)..(((k + 1 : ℕ) : ℝ) * T / 2 ^ n), g u) ^ 2) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hg.continuousOn
  have hM' : ∀ u ∈ Set.Icc (0 : ℝ) T, |g u| ≤ M := fun u hu => by
    simpa [Real.norm_eq_abs] using hM u hu
  have hlim : Tendsto (fun n : ℕ => M ^ 2 * T ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have := h.const_mul (M ^ 2 * T ^ 2)
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [one_div_pow]; field_simp
  refine squeeze_zero (fun n => Finset.sum_nonneg (fun k _ => sq_nonneg _)) (fun n => ?_) hlim
  exact sum_sq_cell_le g T hT M hM' n

/-- D1a pathwise core: QV sums of `I = -(1/2)∫ g` on the grid tend to `∫_0^T g` in measure,
hence `∫_0^T g = 0` a.s. -/
theorem integral_eq_zero_of_qv {P : Measure Ω} [IsFiniteMeasure P] {I : ℝ≥0 → Ω → ℝ}
    {g : Ω → ℝ → ℝ} (T : ℝ≥0) (hgc : ∀ ω, Continuous (g ω))
    (hIm : ∀ t, AEStronglyMeasurable (I t) P)
    (hI : ∀ᵐ ω ∂P, ∀ n k : ℕ, k ≤ 2 ^ n →
      I (dyT T n k) ω = -(1 / 2) * ∫ u in (0 : ℝ)..(dyT T n k : ℝ), g ω u)
    (hqv : TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n),
        (I (dyT T n (k + 1)) ω - I (dyT T n k) ω) ^ 2) atTop
      (fun ω => ∫ u in (0 : ℝ)..(T : ℝ), g ω u)) :
    ∀ᵐ ω ∂P, ∫ u in (0 : ℝ)..(T : ℝ), g ω u = 0 := by
  have hpath : ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (2 ^ n),
      (I (dyT T n (k + 1)) ω - I (dyT T n k) ω) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hI] with ω hω
    have h := (tendsto_sum_sq_cell (g ω) (hgc ω) (T : ℝ) T.2).const_mul (1 / 4 : ℝ)
    simp only [mul_zero] at h
    refine h.congr (fun n => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk : k < 2 ^ n := Finset.mem_range.1 hk
    rw [hω n (k + 1) hk, hω n k hk.le]
    have hii : ∀ a b : ℝ, IntervalIntegrable (g ω) volume a b :=
      fun a b => (hgc ω).intervalIntegrable a b
    rw [show -(1 / 2) * (∫ u in (0 : ℝ)..(dyT T n (k + 1) : ℝ), g ω u) -
        -(1 / 2) * (∫ u in (0 : ℝ)..(dyT T n k : ℝ), g ω u) =
        -(1 / 2) * ((∫ u in (0 : ℝ)..(dyT T n (k + 1) : ℝ), g ω u) -
          ∫ u in (0 : ℝ)..(dyT T n k : ℝ), g ω u) by ring,
      intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _), dyT_coe, dyT_coe]
    ring
  have h0 : TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n),
      (I (dyT T n (k + 1)) ω - I (dyT T n k) ω) ^ 2) atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) hpath
    have := Finset.aestronglyMeasurable_sum (Finset.range (2 ^ n))
      (fun k _ => (((hIm (dyT T n (k + 1))).sub (hIm (dyT T n k))).pow 2))
    convert this using 1
    funext ω
    simp [Finset.sum_apply]
  have := tendstoInMeasure_ae_unique hqv h0
  exact this

end StochCalcD1a


namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma G_le_F (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : M.G t ≤ M.F t := by
  rw [hM.filtG t, hM.filtF t]
  refine sup_le_sup_right (iSup₂_mono fun s _ => ?_) _
  have h : M.B s = Prod.fst ∘ (fun ω => (M.B s ω, M.Bt s ω)) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le

lemma η_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) : Continuous (fun t => M.η t ω) := by
  unfold Model.η
  exact (hM.μ_cont ω).div (hM.σ_cont ω) (fun t => (hM.σ_pos t ω).ne')

lemma η_meas (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    StronglyMeasurable[M.F s] (M.η s) := by
  have h1 := (hM.μ_adapted s).mono (G_le_F M hM s)
  have h2 := (hM.σ_adapted s).mono (G_le_F M hM s)
  exact h1.div h2

lemma Z_eq_one_of_deg (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (t : ℝ≥0) (ht : t ≤ p.T) :
    M.Z t =ᵐ[M.P] fun _ => (1 : ℝ) := by
  have := hM.prob
  refine (h5.1.2.2 t p.T ht le_rfl).symm.trans ?_
  refine (condExp_congr_ae hdeg).trans ?_
  rw [condExp_const (M.F.le t)]

lemma dyT_le (T : ℝ≥0) {n k : ℕ} (hk : k ≤ 2 ^ n) : StochCalcD1a.dyT T n k ≤ T := by
  rw [← NNReal.coe_le_coe, StochCalcD1a.dyT_coe]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2n]
  have : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
  nlinarith [T.2]

/-- Statement of the planned child C_QV (quadratic variation of a Brownian Ito integral with a
continuous adapted integrand along the dyadic grid). -/
def QVStatement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d), IsStandardBrownian P W →
    ∀ (x₀ : SDEState d) (j : Fin d) (t : ℝ≥0) (H J : ℝ≥0 → Ω → ℝ),
    (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
    (∀ ω, Continuous fun s => H s ω) →
    HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀)) (fun s ω => W s ω j) H J →
    TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (2 ^ n),
        (J ((((k + 1 : ℕ) : ℝ≥0)) * t / 2 ^ n) ω - J (((k : ℕ) : ℝ≥0) * t / 2 ^ n) ω) ^ 2) atTop
      (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), H u.toNNReal ω ^ 2)

/-- D1a: `Z_T = 1` a.s. forces `∫_0^T η² = 0` a.s. -/
theorem int_η_sq_zero (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω) :
    ∀ᵐ ω ∂M.P, ∫ u in (0 : ℝ)..(p.T : ℝ), M.η u.toNNReal ω ^ 2 = 0 := by
  have := hM.prob
  have hqv := hQV 2 M.P (W M) (isStandardBrownian M hM) 0 0 p.T M.η M.I
    (meas_cBP_of_F M hM (η_meas M hM)) (η_cont M hM) (hasIto_B M hM hM.I_ito)
  refine StochCalcD1a.integral_eq_zero_of_qv (I := M.I)
    (g := fun ω u => M.η u.toNNReal ω ^ 2) p.T
    (fun ω => ((η_cont M hM ω).comp continuous_real_toNNReal).pow 2)
    (fun t => ((hM.I_adapted t).mono (M.G.le t)).aestronglyMeasurable) ?_ ?_
  · have hall : ∀ n k : ℕ, ∀ᵐ ω ∂M.P, k ≤ 2 ^ n →
        M.I (StochCalcD1a.dyT p.T n k) ω =
          -(1 / 2) * ∫ u in (0 : ℝ)..(StochCalcD1a.dyT p.T n k : ℝ), M.η u.toNNReal ω ^ 2 := by
      intro n k
      by_cases hk : k ≤ 2 ^ n
      · filter_upwards [Z_eq_one_of_deg M hM h5 hdeg _ (dyT_le p.T hk)] with ω hω _
        unfold Model.Z at hω
        have h0 := Real.exp_eq_one_iff _ |>.1 hω
        linarith
      · exact Filter.Eventually.of_forall (fun ω h => absurd h hk)
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k
    exact hall n k
  · exact hqv

/-- D1a consequence: the drift integral vanishes on `[0,T]` a.s. -/
theorem drift_zero (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω) :
    ∀ᵐ ω ∂M.P, ∀ t : ℝ≥0, t ≤ p.T →
      ∫ u in (0 : ℝ)..(t : ℝ), M.X u.toNNReal ω * M.μ u.toNNReal ω = 0 := by
  filter_upwards [int_η_sq_zero M hM h5 hdeg hQV] with ω hω t ht
  have hint : IntervalIntegrable (fun u : ℝ => M.η u.toNNReal ω ^ 2) volume 0 (p.T : ℝ) :=
    (((η_cont M hM ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae p.T.2
    (Filter.Eventually.of_forall (fun u => sq_nonneg _)) hint).1 hω
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hae
  have : ∫ u in (0 : ℝ)..(t : ℝ), M.X u.toNNReal ω * M.μ u.toNNReal ω =
      ∫ u in (0 : ℝ)..(t : ℝ), (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with u hu hut
    rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hut
    have hu' := hu ⟨hut.1, hut.2.trans (by exact_mod_cast ht)⟩
    simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, Model.η] at hu'
    rcases div_eq_zero_iff.1 hu' with h | h
    · simp [h]
    · exact absurd h (hM.σ_pos _ _).ne'
  rw [this, intervalIntegral.integral_zero]

/-- D1a final form: `X_t = x₀ + J_t` for `t ≤ T`, a.s. -/
theorem X_eq_J (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω) :
    ∀ᵐ ω ∂M.P, ∀ t : ℝ≥0, t ≤ p.T → M.X t ω = p.x₀ + M.J t ω := by
  filter_upwards [drift_zero M hM h5 hdeg hQV, hM.X_sde] with ω h1 h2 t ht
  rw [h2 t ht, h1 t ht, add_zero]

end StochCalcD1aW


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- Bounded in `L²` implies uniformly integrable (`p = 1`). -/
lemma unifIntegrable_of_sq_le {P : Measure Ω} (S : ℕ → Ω → ℝ) (hSm : ∀ n, MemLp (S n) 2 P)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ n, ∫ ω, S n ω ^ 2 ∂P ≤ K) : UnifIntegrable S 1 P := by
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hSm n).1) fun ε hε => ?_
  refine ⟨⟨K / ε + 1, by positivity⟩, fun n => ?_⟩
  set K' : ℝ := K / ε + 1 with hK'
  have hKpos : 0 < K' := by positivity
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc ∫⁻ ω, ‖{x | (⟨K', hKpos.le⟩ : ℝ≥0) ≤ ‖S n x‖₊}.indicator (S n) ω‖ₑ ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (S n ω ^ 2 / K') ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ {x | (⟨K', hKpos.le⟩ : ℝ≥0) ≤ ‖S n x‖₊}
        · rw [Set.indicator_of_mem hω, Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          have hK'' : K' ≤ |S n ω| := by
            have h1 : ((⟨K', hKpos.le⟩ : ℝ≥0) : ℝ) ≤ ((‖S n ω‖₊ : ℝ≥0) : ℝ) :=
              NNReal.coe_le_coe.2 hω
            simpa using h1
          rw [le_div_iff₀ hKpos, ← sq_abs]
          linarith only [mul_le_mul_of_nonneg_left hK'' (abs_nonneg (S n ω))]
        · rw [Set.indicator_of_notMem hω]; simp
    _ = ENNReal.ofReal (∫ ω, S n ω ^ 2 / K' ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal ((hSm n).integrable_sq.div_const K')
          (Filter.Eventually.of_forall fun ω => by positivity)).symm
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div, div_le_iff₀ hKpos]
        calc ∫ ω, S n ω ^ 2 ∂P ≤ K := hK n
          _ ≤ ε * K' := by
            rw [hK', mul_add, mul_div_cancel₀ _ hε.ne', mul_one]; linarith

/-- Fatou: an in-measure limit of an `L²`-bounded sequence is in `L²` with the same bound. -/
lemma memLp_two_of_tendstoInMeasure {P : Measure Ω} (S : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hSm : ∀ n, MemLp (S n) 2 P) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ n, ∫ ω, S n ω ^ 2 ∂P ≤ K)
    (hconv : TendstoInMeasure P S atTop Y) :
    MemLp Y 2 P ∧ ∫ ω, Y ω ^ 2 ∂P ≤ K := by
  have hSaesm : ∀ n, AEStronglyMeasurable (S n) P := fun n => (hSm n).1
  have hYm : AEStronglyMeasurable Y P := hconv.aestronglyMeasurable hSaesm
  obtain ⟨φ, _hφ, hae⟩ := hconv.exists_seq_tendsto_ae
  have hlin : ∀ n, ∫⁻ ω, ENNReal.ofReal (S n ω ^ 2) ∂P = ENNReal.ofReal (∫ ω, S n ω ^ 2 ∂P) :=
    fun n => (ofReal_integral_eq_lintegral_ofReal (hSm n).integrable_sq
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)).symm
  have hfatou : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P ≤ ENNReal.ofReal K := by
    calc ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P
        = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (S (φ k) ω ^ 2)) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            ((continuous_pow 2).continuousAt.tendsto.comp hω)).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (S (φ k) ω ^ 2) ∂P) atTop :=
          lintegral_liminf_le' fun k =>
            (ENNReal.measurable_ofReal.comp_aemeasurable ((hSaesm (φ k)).aemeasurable.pow_const 2))
      _ ≤ ENNReal.ofReal K := by
          refine liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun k => ?_)
          rw [hlin]
          exact ENNReal.ofReal_le_ofReal (hK _)
  have hYint2 : Integrable (fun ω => Y ω ^ 2) P := by
    refine ⟨hYm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact hfatou.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hYm).2 hYint2, ?_⟩
  have h := hfatou
  rw [← ofReal_integral_eq_lintegral_ofReal hYint2
    (Filter.Eventually.of_forall fun ω => sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hK0).1 h

/-- In-measure convergence of an `L²`-bounded sequence gives convergence of set integrals. -/
lemma tendsto_setIntegral_of_sq_le {P : Measure Ω} [IsFiniteMeasure P] (S : ℕ → Ω → ℝ)
    (Y : Ω → ℝ) (hSm : ∀ n, MemLp (S n) 2 P) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ n, ∫ ω, S n ω ^ 2 ∂P ≤ K) (hconv : TendstoInMeasure P S atTop Y) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, S n ω ∂P) atTop (𝓝 (∫ ω in A, Y ω ∂P)) := by
  have hY := memLp_two_of_tendstoInMeasure S Y hSm K hK0 hK hconv
  have hui := unifIntegrable_of_sq_le S hSm K hK0 hK
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n => (hSm n).1) (hY.1.mono_exponent one_le_two) hui hconv
  exact tendsto_setIntegral_of_L1 Y hY.1.1
    (Filter.Eventually.of_forall fun n => (hSm n).integrable one_le_two)
    (by simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hL1) A




/-- Fatou/Riemann isometry bound for a bounded integrand: `E J_t² ≤ E ∫_0^t H²`. -/
lemma ito_sq_le_bdd {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    MemLp (J t) 2 P ∧
      ∫ ω, J t ω ^ 2 ∂P ≤ ∫ ω, (∫ u in (0 : ℝ)..t.val, H u.toNNReal ω ^ 2) ∂P := by
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  set G : ℝ≥0 → Ω → ℝ := fun s ω => H s ω ^ 2 with hGdef
  have hGae : ∀ s, AEStronglyMeasurable (G s) P := fun s => (hHae s).pow 2
  have hGc : ∀ ω, Continuous fun s => G s ω := fun ω => (hHc ω).pow 2
  have hGb : ∀ s ω, |G s ω| ≤ C ^ 2 := fun s ω => by
    simp only [hGdef, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC s ω) 2
  set S : ℕ → Ω → ℝ := fun n =>
    itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n) with hSdef
  have hconv : TendstoInMeasure P S atTop (J t) :=
    clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ t
  have ham : ∀ (n k : ℕ), Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (leftCoef (clampH H n) t n k) :=
    fun n k => clampH_measurable (hHm _) _
  have hab : ∀ (n k : ℕ) ω, |leftCoef (clampH H n) t n k ω| ≤ C := fun n k ω =>
    (abs_clampH_le_abs H (Nat.cast_nonneg n) _ ω).trans (hC _ ω)
  have hSm : ∀ n, MemLp (S n) 2 P := fun n =>
    itoStepSum_memLp hW t n j _
      (fun k _ => aestronglyMeasurable_of_completedPast hW x₀ _ (ham n k)) C
      (fun k _ ω => hab n k ω)
  set Rie : ℕ → Ω → ℝ := fun n ω => (∑ k ∈ Finset.range (2 ^ n), G (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) with hRiedef
  have hGint : ∀ s, Integrable (G s) P := fun s =>
    Integrable.of_bound (C := C ^ 2) (hGae s) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hGb s ω)
  -- E S_n² ≤ E Rie_n
  have hSR : ∀ n, ∫ ω, S n ω ^ 2 ∂P ≤ ∫ ω, Rie n ω ∂P := by
    intro n
    simp only [hSdef]
    rw [itoStepSum_isometry hW x₀ t n j _ (fun k _ => ham n k) C (fun k _ ω => hab n k ω)]
    simp only [hRiedef]
    rw [integral_mul_const, integral_finsetSum _ (fun k _ => hGint _), Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (NNReal.coe_nonneg _)
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) (hGint _)
      (Eventually.of_forall fun ω => ?_)
    simp only [hGdef, leftCoef]
    have h1 := abs_clampH_le_abs H (Nat.cast_nonneg n) (dyTime t n k) ω
    calc clampH H n (dyTime t n k) ω ^ 2 = |clampH H n (dyTime t n k) ω| ^ 2 := (sq_abs _).symm
      _ ≤ |H (dyTime t n k) ω| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = H (dyTime t n k) ω ^ 2 := sq_abs _
  -- E Rie_n → E ∫ G (dominated convergence)
  have hRlim : Tendsto (fun n => ∫ ω, Rie n ω ∂P) atTop
      (𝓝 (∫ ω, (∫ u in (0 : ℝ)..t.val, G u.toNNReal ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C ^ 2 * t)
      (fun n => riemann_aesm hGae t n) (integrable_const _) (fun n => ?_)
      (Eventually.of_forall fun ω => riemann_tendsto hGc t ω)
    refine Eventually.of_forall fun ω => ?_
    simp only [hRiedef, Real.norm_eq_abs]
    rw [abs_mul, NNReal.abs_eq]
    calc |∑ k ∈ Finset.range (2 ^ n), G (dyTime t n k) ω| * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)
        ≤ (∑ k ∈ Finset.range (2 ^ n), C ^ 2) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (NNReal.coe_nonneg _)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hGb _ ω)
      _ = C ^ 2 * t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
  set K : ℝ := ∫ ω, (∫ u in (0 : ℝ)..t.val, G u.toNNReal ω) ∂P with hKdef
  have hK0 : 0 ≤ K := integral_nonneg fun ω =>
    intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _
  have hstep : ∀ ε > 0, MemLp (J t) 2 P ∧ ∫ ω, J t ω ^ 2 ∂P ≤ K + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hRlim.eventually (gt_mem_nhds
      (show K < K + ε by linarith))))
    have hc' : TendstoInMeasure P (fun m => S (m + N)) atTop (J t) :=
      hconv.comp (tendsto_add_atTop_nat N)
    exact memLp_two_of_tendstoInMeasure (fun m => S (m + N)) (J t) (fun m => hSm _) (K + ε)
      (by linarith) (fun m => ((hSR _).trans (hN _ (Nat.le_add_left N m)).le)) hc'
  refine ⟨(hstep 1 one_pos).1, le_of_forall_pos_le_add fun ε hε => (hstep ε hε).2⟩

/-- Pointwise: clamping does not increase `∫_0^u H²`. -/
lemma intSq_clamp_le {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω) {R : ℝ}
    (hR : 0 ≤ R) (u : ℝ≥0) (ω : Ω) :
    ∫ v in (0 : ℝ)..u.val, clampH H R v.toNNReal ω ^ 2 ≤
      ∫ v in (0 : ℝ)..u.val, H v.toNNReal ω ^ 2 := by
  refine intervalIntegral.integral_mono_on u.2
    ((((clampH_continuous hHc R ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _)
    ((((hHc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _) fun v _ => ?_
  have h1 := abs_clampH_le_abs H hR v.toNNReal ω
  calc clampH H R v.toNNReal ω ^ 2 = |clampH H R v.toNNReal ω| ^ 2 := (sq_abs _).symm
    _ ≤ |H v.toNNReal ω| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = H v.toNNReal ω ^ 2 := sq_abs _

/-- Pointwise monotonicity of `∫_0^u H²` in `u`. -/
lemma intSq_mono {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω) {u t : ℝ≥0}
    (hut : u ≤ t) (ω : Ω) :
    ∫ v in (0 : ℝ)..u.val, H v.toNNReal ω ^ 2 ≤ ∫ v in (0 : ℝ)..t.val, H v.toNNReal ω ^ 2 :=
  intervalIntegral.integral_mono_interval le_rfl u.2 hut
    (Eventually.of_forall fun v => sq_nonneg _)
    ((((hHc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _)

/-- Truncations converge: `J^R_s → J_s` in measure as `R → ∞`. -/
lemma tendsto_clamp_ito {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ} (JR : ℕ → ℝ≥0 → Ω → ℝ)
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJR : ∀ R : ℕ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (clampH H R) (JR R)) (s : ℝ≥0) :
    TendstoInMeasure P (fun R => JR R s) atTop (J s) := by
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  intro ε hε
  have hle : ∀ R : ℕ, P {ω | ε ≤ edist (JR R s ω) (J s ω)} ≤ P (bigSet H s R) := by
    intro R
    have hae := hasBrownianItoIntegral_eq_on hW x₀ j (fun u => clampH_measurable (hHm u) (R : ℝ))
      (clampH_continuous hHc (R : ℝ)) hHm hHc (hJR R) hJ s (bigSet H s R)ᶜ
      (fun ω hω N i hi => clampH_eq_of_abs_le H (abs_le_of_not_mem_bigSet hω hi))
    refine measure_mono_ae ?_
    filter_upwards [hae] with ω hω hmem
    by_contra hc
    have h1 := hω hc
    have h2 : ε ≤ edist (JR R s ω) (J s ω) := hmem
    rw [h1, edist_self] at h2
    exact absurd h2 (not_le.2 hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (bigSet_tendsto hHae hHc s) (fun _ => bot_le) hle


/-- `E J_u² ≤ E ∫_0^t H²` for `u ≤ t`, unbounded continuous adapted `H`. -/
lemma ito_sq_le {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0)
    (hint : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω ^ 2) P)
    (u : ℝ≥0) (hu : u ≤ t) :
    MemLp (J u) 2 P ∧
      ∫ ω, J u ω ^ 2 ∂P ≤ ∫ ω, (∫ v in (0 : ℝ)..t.val, H v.toNNReal ω ^ 2) ∂P := by
  have hex : ∀ R : ℕ, ∃ JR : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P
      (completedBrownianPast P W (fun _ => x₀)) (fun s ω => W s ω j) (clampH H R) JR :=
    fun R => exists_hasBrownianItoIntegral hW x₀ j (fun u => clampH_measurable (hHm u) (R : ℝ))
      (clampH_continuous hHc (R : ℝ))
  choose JR hJR using hex
  have hK0 : 0 ≤ ∫ ω, (∫ v in (0 : ℝ)..t.val, H v.toNNReal ω ^ 2) ∂P := integral_nonneg fun ω =>
    intervalIntegral.integral_nonneg t.2 fun v _ => sq_nonneg _
  have hbound : ∀ R : ℕ, MemLp (JR R u) 2 P ∧
      ∫ ω, JR R u ω ^ 2 ∂P ≤ ∫ ω, (∫ v in (0 : ℝ)..t.val, H v.toNNReal ω ^ 2) ∂P := by
    intro R
    obtain ⟨h1, h2⟩ := ito_sq_le_bdd hW x₀ j (fun u => clampH_measurable (hHm u) (R : ℝ))
      (clampH_continuous hHc (R : ℝ)) (fun u ω => abs_clampH_le H (Nat.cast_nonneg R) u ω)
      (hJR R) u
    refine ⟨h1, h2.trans (integral_mono_of_nonneg ?_ hint ?_)⟩
    · exact Eventually.of_forall fun ω => intervalIntegral.integral_nonneg u.2 fun v _ => sq_nonneg _
    · exact Eventually.of_forall fun ω =>
        (intSq_clamp_le hHc (Nat.cast_nonneg R) u ω).trans (intSq_mono hHc hu ω)
  exact memLp_two_of_tendstoInMeasure (fun R => JR R u) (J u) (fun R => (hbound R).1) _ hK0
    (fun R => (hbound R).2) (tendsto_clamp_ito hW x₀ j JR hHm hHc hJ hJR u)

end StochCalcL2M


namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The integrand `Xσ`. -/
def Hx (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ := M.X t ω * M.σ t ω

lemma Hx_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) : Continuous fun t => Hx M t ω :=
  (hM.X_cont ω).mul (hM.σ_cont ω)

lemma Hx_measF (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    StronglyMeasurable[M.F s] (Hx M s) :=
  ((hM.X_adapted s).mono (StochCalcD1aW.G_le_F M hM s)).mul
    ((hM.σ_adapted s).mono (StochCalcD1aW.G_le_F M hM s))

lemma Hx_meas (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) : Measurable (Hx M s) :=
  ((Hx_measF M hM s).mono (M.F.le s)).measurable

lemma Hx_cBP (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s] (Hx M s) :=
  meas_cBP_of_F M hM (Hx_measF M hM) s

/-- Assumption 4 gives `E ∫_0^T (Xσ)² < ∞` (Tonelli). -/
lemma hint_T (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) :
    Integrable (fun ω => ∫ u in (0 : ℝ)..(p.T : ℝ), Hx M u.toNNReal ω ^ 2) M.P := by
  have := hM.prob
  set f : Ω → ℝ → ℝ := fun ω u => Hx M u.toNNReal ω ^ 2 with hfdef
  have hfc : ∀ ω, Continuous (f ω) := fun ω =>
    ((Hx_cont M hM ω).comp continuous_real_toNNReal).pow 2
  have hjoint : Measurable (Function.uncurry fun (u : ℝ≥0) (ω : Ω) => Hx M u ω) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => Hx_cont M hM ω)
      (fun u => Hx_meas M hM u)
  have hjf : Measurable (fun q : Ω × ℝ => ENNReal.ofReal (f q.1 q.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have : (fun q : Ω × ℝ => f q.1 q.2) =
        (fun x => x ^ 2) ∘ (Function.uncurry fun (u : ℝ≥0) (ω : Ω) => Hx M u ω) ∘
          (fun q : Ω × ℝ => (q.2.toNNReal, q.1)) := by
      funext q; simp [hfdef, Function.uncurry]
    rw [this]
    exact (continuous_pow 2).measurable.comp
      (hjoint.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  have hnn : ∀ ω, 0 ≤ ∫ u in (0 : ℝ)..(p.T : ℝ), f ω u := fun ω =>
    intervalIntegral.integral_nonneg p.T.coe_nonneg fun u _ => sq_nonneg _
  have hpt : ∀ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..(p.T : ℝ), f ω u) =
      ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ENNReal.ofReal (f ω u) := by
    intro ω
    rw [intervalIntegral.integral_of_le p.T.coe_nonneg,
      ofReal_integral_eq_lintegral_ofReal
        ((hfc ω).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Eventually.of_forall fun u => sq_nonneg _),
      Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hmeasI : AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..(p.T : ℝ), f ω u) M.P :=
    integral_aesm (fun s => ((Hx_meas M hM s).pow_const 2).aestronglyMeasurable)
      (fun ω => (Hx_cont M hM ω).pow 2) p.T
  unfold Model.Assumption4 at h4
  refine ⟨hmeasI, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
  simp_rw [hpt]
  rw [lintegral_lintegral_swap hjf.aemeasurable]
  simpa [hfdef, Hx] using h4

lemma J_memLp (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (t : ℝ≥0) (ht : t ≤ p.T) :
    MemLp (M.J t) 2 M.P := by
  have := hM.prob
  exact (ito_sq_le (isStandardBrownian M hM) 0 0 (Hx_cBP M hM) (Hx_cont M hM)
    (hasIto_B M hM hM.X_ito) p.T (hint_T M hM h4) t ht).1

end StochCalcD1b


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

end StochCalcIndep


namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcHs


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}

end StochCalcGauss


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end StochCalcTilt

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcTiltM

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcOrth


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein

end StochCalcStein

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcSteinM


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma memLp_bdd_mul {Y ξ : Ω → ℝ} (hξ : MemLp ξ 2 P) (hY : AEStronglyMeasurable Y P) {C : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ C) : MemLp (fun ω => Y ω * ξ ω) 2 P := by
  refine (hξ.const_mul C).of_le (hY.mul hξ.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hYb ω).trans (le_abs_self C)) (abs_nonneg _)

variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)

end StochCalcP6S


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]

end StochCalcHedgeDeg


namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Grid points `t_k = k T / n`. -/
noncomputable def gr (p : Params) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) * (p.T / n)

lemma gr_mono (p : Params) (n : ℕ) : Monotone (gr p n) := fun i j hij => by
  unfold gr; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

lemma gr_le_T (p : Params) {n k : ℕ} (hk : k ≤ n) : gr p n k ≤ p.T := by
  unfold gr
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (0 : ℝ≥0) < n := by exact_mod_cast h
    calc (k : ℝ≥0) * (p.T / n) ≤ n * (p.T / n) := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
      _ = p.T := by field_simp

end StochCalcD2


namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcD2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6

end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)

end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcD3

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `B`-increment. -/
noncomputable def dB (M : Model p Ω) (u w : ℝ≥0) (ω : Ω) : ℝ := M.B w ω - M.B u ω

lemma gr_mul (p : Params) {m : ℕ} (hm : 0 < m) (n k : ℕ) : gr p (n * m) (k * m) = gr p n k := by
  unfold gr
  have hm' : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

end StochCalcD3


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end StochCalcR1


namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcR1M


namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcR4


open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]

end StochCalcR2


open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2


end StochCalcR2


namespace StochCalcR2

open MeasureTheory

end StochCalcR2


open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3

end StochCalcR3


set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6

end StochCalcR6


namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcR5


namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcR7


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- Dyadic floor index of `r` on the level-`n` grid of `[0,t]`. -/
noncomputable def rk (t r : ℝ≥0) (n : ℕ) : ℕ := ⌊(r : ℝ) / (t : ℝ) * 2 ^ n⌋₊

lemma dyTime_real (t : ℝ≥0) (n k : ℕ) :
    ((dyTime t n k : ℝ≥0) : ℝ) = (k : ℝ) * (t : ℝ) / 2 ^ n := by
  unfold dyTime; push_cast; ring

lemma dyTime_pow_mul' (t : ℝ≥0) (n m k : ℕ) : dyTime t (n + m) (2 ^ m * k) = dyTime t n k := by
  unfold dyTime
  push_cast
  rw [pow_add]
  have h2 : (2 : ℝ≥0) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have h3 : (2 : ℝ≥0) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp

lemma dyTime_lt_iff {t : ℝ≥0} (ht : 0 < t) (N l l' : ℕ) :
    dyTime t N l < dyTime t N l' ↔ l < l' := by
  rw [← NNReal.coe_lt_coe, dyTime_real, dyTime_real]
  have ht' : (0 : ℝ) < t := ht
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rw [div_lt_div_iff_of_pos_right h2]
  constructor
  · intro h
    by_contra hc
    have : (l' : ℝ) ≤ l := by exact_mod_cast not_lt.1 hc
    nlinarith
  · intro h
    have : (l : ℝ) < l' := by exact_mod_cast h
    nlinarith

lemma dyTime_lt_iff' {t : ℝ≥0} (ht : 0 < t) (n m l k : ℕ) :
    dyTime t (n + m) l < dyTime t n k ↔ l < 2 ^ m * k := by
  rw [← dyTime_pow_mul' t n m k, dyTime_lt_iff ht]

lemma rk_le {t r : ℝ≥0} (ht : 0 < t) (hr : r ≤ t) (n : ℕ) : rk t r n ≤ 2 ^ n := by
  unfold rk
  apply Nat.floor_le_of_le
  have ht' : (0 : ℝ) < t := ht
  have h1 : (r : ℝ) / t ≤ 1 := (div_le_one ht').2 (by exact_mod_cast hr)
  push_cast
  calc (r : ℝ) / t * 2 ^ n ≤ 1 * 2 ^ n := by gcongr
    _ = 2 ^ n := one_mul _

lemma dy_rk_le {t : ℝ≥0} (ht : 0 < t) (r : ℝ≥0) (n : ℕ) : dyTime t n (rk t r n) ≤ r := by
  rw [← NNReal.coe_le_coe, dyTime_real]
  have ht' : (0 : ℝ) < t := ht
  have htne : (t : ℝ) ≠ 0 := ht'.ne'
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl : ((rk t r n : ℕ) : ℝ) ≤ (r : ℝ) / t * 2 ^ n :=
    Nat.floor_le (by positivity)
  rw [div_le_iff₀ h2]
  calc ((rk t r n : ℕ) : ℝ) * t ≤ (r : ℝ) / t * 2 ^ n * t := by gcongr
    _ = (r : ℝ) * 2 ^ n := by field_simp

lemma lt_dy_rk_succ {t : ℝ≥0} (ht : 0 < t) (r : ℝ≥0) (n : ℕ) :
    r < dyTime t n (rk t r n + 1) := by
  rw [← NNReal.coe_lt_coe, dyTime_real]
  have ht' : (0 : ℝ) < t := ht
  have htne : (t : ℝ) ≠ 0 := ht'.ne'
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl : (r : ℝ) / t * 2 ^ n < ((rk t r n : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [lt_div_iff₀ h2]
  push_cast
  calc (r : ℝ) * 2 ^ n = (r : ℝ) / t * 2 ^ n * t := by field_simp
    _ < (((rk t r n : ℕ) : ℝ) + 1) * t := by gcongr

lemma meas_ite {m : MeasurableSpace Ω} (p : Prop) [Decidable p] {f : Ω → ℝ}
    (hf : Measurable[m] f) : Measurable[m] (fun ω => if p then f ω else 0) := by
  by_cases h : p
  · simp only [if_pos h]; exact hf
  · simp only [if_neg h]; exact measurable_const

/-- Masked clamped left-point coefficients: cells of the level-`N` grid of `[0,t]` starting in
`[a, b)`. -/
noncomputable def cMask (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (N : ℕ) (a b : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  if a ≤ dyTime t N k ∧ dyTime t N k < b then clampH H N (dyTime t N k) ω else 0

lemma split_mask (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (N : ℕ) {a b : ℝ≥0} (hab : a ≤ b) (k : ℕ)
    (ω : Ω) : cMask H t N 0 b k ω = cMask H t N 0 a k ω + cMask H t N a b k ω := by
  unfold cMask
  set x := dyTime t N k
  by_cases h2 : x < a
  · have h1 : 0 ≤ x ∧ x < b := ⟨(by positivity), lt_of_lt_of_le h2 hab⟩
    have h3 : ¬ (a ≤ x ∧ x < b) := fun h => absurd h.1 (not_le.2 h2)
    rw [if_pos h1, if_pos ⟨(by positivity), h2⟩, if_neg h3, add_zero]
  · by_cases h1 : x < b
    · rw [if_pos ⟨(by positivity), h1⟩, if_neg (fun h => h2 h.2), if_pos ⟨not_lt.1 h2, h1⟩, zero_add]
    · rw [if_neg (fun h => h1 h.2), if_neg (fun h => h2 h.2), if_neg (fun h => h1 h.2),
        add_zero]

/-- **Truncation consistency** at an arbitrary `r ≤ t`. -/
theorem truncSum_tendsto {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) {t r : ℝ≥0} (ht : 0 < t) (hr : r ≤ t)
    (hJc : TendstoInMeasure P (fun n => J (dyTime t n (rk t r n))) atTop (J r)) :
    TendstoInMeasure P (fun N => itoStepSum (fun s ω => W s ω j) t N
      (cMask H t N 0 r)) atTop (J r) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  set S : ℝ≥0 → Ω → ℝ := fun s ω => W s ω j with hS
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with heT | heT
  · exact Eventually.of_forall fun _ => heT ▸ le_top
  set q : ℝ≥0∞ := e / 2 / 2 with hq
  have hq0 : 0 < q := ENNReal.half_pos (ENNReal.half_pos he.ne').ne'
  have hqT : q ≠ ⊤ := by
    rw [hq]
    exact ENNReal.div_ne_top (ENNReal.div_ne_top heT two_ne_zero) two_ne_zero
  have hqq : q + q + q + q = e := by
    rw [hq, add_assoc, ENNReal.add_halves, ENNReal.add_halves]
  set ε' : ℝ := ε / 3 with hε'
  have hε'0 : 0 < ε' := by positivity
  set δ : ℝ := ε' ^ 2 * q.toReal with hδ
  have hqR : 0 < q.toReal := ENNReal.toReal_pos hq0.ne' hqT
  have hδ0 : 0 < δ := by positivity
  have hδq : ENNReal.ofReal (δ / ε' ^ 2) = q := by
    rw [hδ, mul_div_cancel_left₀ _ (by positivity), ENNReal.ofReal_toReal hqT]
  -- (a) the level `R0` of the big set
  obtain ⟨R0, hR0⟩ := ((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHae hHc t) q hq0).exists)
  -- (c) the coarse level `n`
  have hev1 : ∀ᶠ n : ℕ in atTop, ((R0 : ℝ) ^ 2 * t) / 2 ^ n ≤ δ := by
    obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (((R0 : ℝ) ^ 2 * t) / δ) one_lt_two
    filter_upwards [eventually_ge_atTop n1] with n hn
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_iff₀ h2]
    have : ((R0 : ℝ) ^ 2 * t) / δ < 2 ^ n :=
      lt_of_lt_of_le hn1 (pow_le_pow_right₀ one_le_two hn)
    rw [div_lt_iff₀ hδ0] at this
    linarith
  have hev2 : ∀ᶠ n : ℕ in atTop,
      P {ω | ε' ≤ dist (J (dyTime t n (rk t r n)) ω) (J r ω)} ≤ q :=
    ENNReal.tendsto_nhds_zero.1 ((tendstoInMeasure_iff_dist.1 hJc) ε' hε'0) q hq0
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  set k := rk t r n with hk
  set rn := dyTime t n k with hrn
  have hkle : k ≤ 2 ^ n := rk_le ht hr n
  have hrnr : rn ≤ r := dy_rk_le ht r n
  have hrlt : r < dyTime t n (k + 1) := lt_dy_rk_succ ht r n
  -- (d) the middle term: masked sums up to the dyadic floor converge to `J rn`
  have hmid : TendstoInMeasure P (fun m => itoStepSum S t (n + m) (cMask H t (n + m) 0 rn))
      atTop (J rn) := by
    refine tendstoInMeasure_of_local fun η hη => ?_
    obtain ⟨R1, hR1⟩ := ((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHae hHc t) η hη).exists)
    refine ⟨bigSet H t R1, hR1, _, _,
      partialSum_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ t n k hkle, ?_,
      Eventually.of_forall fun _ _ => rfl⟩
    filter_upwards [eventually_ge_atTop R1] with m hm ω hω
    unfold itoStepSum
    refine Finset.sum_congr rfl fun l hl => ?_
    congr 1
    have hl' : l ≤ 2 ^ (n + m) := (Finset.mem_range.1 hl).le
    have hHb : |H (dyTime t (n + m) l) ω| ≤ R1 := abs_le_of_not_mem_bigSet hω hl'
    unfold cMask
    beta_reduce
    by_cases hlt : l < 2 ^ m * k
    · have hlt' : dyTime t (n + m) l < rn := (dyTime_lt_iff' ht n m l k).2 hlt
      rw [if_pos ⟨(by positivity), hlt'⟩, if_pos hlt,
        clampH_eq_of_abs_le H (hHb.trans (show (R1 : ℝ) ≤ ((n + m : ℕ) : ℝ) by
          exact_mod_cast (hm.trans (Nat.le_add_left m n)))),
        clampH_eq_of_abs_le H (hHb.trans (show (R1 : ℝ) ≤ ((m : ℕ) : ℝ) by exact_mod_cast hm))]
    · rw [if_neg (fun h => hlt ((dyTime_lt_iff' ht n m l k).1 h.2)), if_neg hlt]
  have hev3 : ∀ᶠ m : ℕ in atTop, P {ω | ε' ≤ dist (itoStepSum S t (n + m)
      (cMask H t (n + m) 0 rn) ω) (J rn ω)} ≤ q :=
    ENNReal.tendsto_nhds_zero.1 ((tendstoInMeasure_iff_dist.1 hmid) ε' hε'0) q hq0
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 hev3
  filter_upwards [eventually_ge_atTop (n + m0)] with N hN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right n m0) hN)
  have hm : m0 ≤ m := by omega
  set TA : Ω → ℝ := itoStepSum S t (n + m) (cMask H t (n + m) 0 rn) with hTA
  set D : Ω → ℝ := itoStepSum S t (n + m) (cMask H t (n + m) rn r) with hD
  have hdec : ∀ ω, itoStepSum S t (n + m) (cMask H t (n + m) 0 r) ω = TA ω + D ω := by
    intro ω
    simp only [hTA, hD]
    unfold itoStepSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [split_mask H t (n + m) hrnr l ω, add_mul]
  -- (e) the cells in `[rn, r)`: Lenglart bound
  have hcheb := itoStepSum_local_chebyshev hW x₀ t (n + m) j (cMask H t (n + m) rn r)
    (fun l _ => by unfold cMask; exact meas_ite _ (clampH_measurable (hHm _) _)) ((n + m : ℕ) : ℝ)
    (fun l _ ω => by
      unfold cMask
      split_ifs
      · exact abs_clampH_le H (Nat.cast_nonneg _) _ ω
      · simp only [abs_zero]; positivity) hε'0 hδ0.le
  have hsmall : {ω | δ < (∑ l ∈ Finset.range (2 ^ (n + m)), cMask H t (n + m) rn r l ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ)} ⊆ bigSet H t R0 := by
    intro ω hω
    by_contra hωB
    simp only [Set.mem_setOf_eq] at hω
    have hterm : ∀ l ∈ Finset.range (2 ^ (n + m)), cMask H t (n + m) rn r l ω ^ 2 ≤
        if l ∈ Finset.Ico (2 ^ m * k) (2 ^ m * (k + 1)) then ((R0 : ℕ) : ℝ) ^ 2 else 0 := by
      intro l hl
      have hl' : l ≤ 2 ^ (n + m) := (Finset.mem_range.1 hl).le
      unfold cMask
      by_cases hc : rn ≤ dyTime t (n + m) l ∧ dyTime t (n + m) l < r
      · have hmem : l ∈ Finset.Ico (2 ^ m * k) (2 ^ m * (k + 1)) := by
          rw [Finset.mem_Ico]
          refine ⟨not_lt.1 fun h => not_lt.2 hc.1 ((dyTime_lt_iff' ht n m l k).2 h), ?_⟩
          exact (dyTime_lt_iff' ht n m l (k + 1)).1 (lt_trans hc.2 hrlt)
        rw [if_pos hc, if_pos hmem]
        have h1 := (abs_clampH_le_abs H (Nat.cast_nonneg (n + m)) (dyTime t (n + m) l) ω).trans
          (abs_le_of_not_mem_bigSet hωB hl')
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      · rw [if_neg hc]
        split_ifs
        · exact (zero_pow two_ne_zero : (0 : ℝ) ^ 2 = 0).trans_le (sq_nonneg _)
        · exact (zero_pow two_ne_zero : (0 : ℝ) ^ 2 = 0).le
    have hsum : (∑ l ∈ Finset.range (2 ^ (n + m)), cMask H t (n + m) rn r l ω ^ 2) ≤
        (2 ^ m : ℝ) * ((R0 : ℕ) : ℝ) ^ 2 := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_ite_mem]
      refine (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        fun _ _ _ => by positivity).trans ?_
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have : 2 ^ m * (k + 1) - 2 ^ m * k = 2 ^ m := by
        rw [mul_add, mul_one, Nat.add_sub_cancel_left]
      rw [this]; exact le_of_eq (by push_cast; ring)
    have hh : ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ) = (t : ℝ) / (2 ^ n * 2 ^ m) := by
      push_cast; rw [pow_add]
    have hfin : (∑ l ∈ Finset.range (2 ^ (n + m)), cMask H t (n + m) rn r l ω ^ 2) *
        ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ) ≤ δ := by
      rw [hh]
      have h2m : (0 : ℝ) < 2 ^ m := by positivity
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have ht0 : (0 : ℝ) ≤ t := t.2
      calc _ ≤ (2 ^ m : ℝ) * ((R0 : ℕ) : ℝ) ^ 2 * ((t : ℝ) / (2 ^ n * 2 ^ m)) := by
            gcongr
        _ = ((R0 : ℝ) ^ 2 * t) / 2 ^ n := by field_simp
        _ ≤ δ := hn1
    linarith
  have hD_le : P {ω | ε' ≤ |D ω|} ≤ q + q :=
    hcheb.trans (by rw [hδq]; exact add_le_add le_rfl ((measure_mono hsmall).trans hR0))
  -- three-term inclusion
  have hsub : {ω | ε ≤ dist (itoStepSum S t (n + m) (cMask H t (n + m) 0 r) ω) (J r ω)} ⊆
      ({ω | ε' ≤ |D ω|} ∪ {ω | ε' ≤ dist (TA ω) (J rn ω)}) ∪
        {ω | ε' ≤ dist (J rn ω) (J r ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq] at hω ⊢
    by_contra hc
    push_neg at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    rw [hdec ω] at hω
    have h4 : |D ω + (TA ω - J rn ω) + (J rn ω - J r ω)| ≤
        |D ω| + |TA ω - J rn ω| + |J rn ω - J r ω| := abs_add_three _ _ _
    have h5 : TA ω + D ω - J r ω = D ω + (TA ω - J rn ω) + (J rn ω - J r ω) := by ring
    rw [← h5] at h4
    linarith
  calc P {ω | ε ≤ dist (itoStepSum S t (n + m) (cMask H t (n + m) 0 r) ω) (J r ω)}
      ≤ P (({ω | ε' ≤ |D ω|} ∪ {ω | ε' ≤ dist (TA ω) (J rn ω)}) ∪
        {ω | ε' ≤ dist (J rn ω) (J r ω)}) := measure_mono hsub
    _ ≤ P {ω | ε' ≤ |D ω|} + P {ω | ε' ≤ dist (TA ω) (J rn ω)} +
        P {ω | ε' ≤ dist (J rn ω) (J r ω)} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (q + q) + q + q := add_le_add (add_le_add hD_le (hm0 m hm)) hn2
    _ = e := hqq

/-- Simple-in-time weight: `θ_i` on `[s_i, s_{i+1})`, `i < n'`. -/
noncomputable def thetaS (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n', if s i ≤ u ∧ u < s (i + 1) then θ i ω else 0

lemma mask_min {t : ℝ≥0} (H : ℝ≥0 → Ω → ℝ) (N : ℕ) (ht : 0 < t) (b : ℝ≥0) {k : ℕ}
    (hk : k < 2 ^ N) (ω : Ω) : cMask H t N 0 (min b t) k ω = cMask H t N 0 b k ω := by
  have hx : dyTime t N k < t := by
    have := (dyTime_lt_iff ht N k (2 ^ N)).2 hk
    rwa [dyTime_at_top] at this
  unfold cMask
  have : dyTime t N k < min b t ↔ dyTime t N k < b := by
    rw [lt_min_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  simp only [this]


lemma stepValue_cell (t : ℝ≥0) (n : ℕ) {u : ℝ} (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      ∀ c : ℕ → Ω → ℝ, itoStepValue t n c u ω = c k ω := by
  obtain ⟨k, hk, h1, h2, -⟩ := itoStepValue_eq_cell t n (fun _ _ => (0 : ℝ)) hu ω
  refine ⟨k, hk, h1, h2, fun c => ?_⟩
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨h1, h2⟩]
  · intro k' _ hk'
    rw [if_neg]
    rintro ⟨h1', h2'⟩
    apply hk'
    have a1 : (k' : ℝ) * t.val / 2 ^ n < ((k : ℝ) + 1) * t.val / 2 ^ n := lt_of_lt_of_le h1' h2
    have a2 : (k : ℝ) * t.val / 2 ^ n < ((k' : ℝ) + 1) * t.val / 2 ^ n := lt_of_lt_of_le h1 h2'
    rw [div_lt_div_iff_of_pos_right h2n] at a1 a2
    have b1 : (k' : ℝ) < k + 1 := lt_of_mul_lt_mul_right a1 ht.le
    have b2 : (k : ℝ) < k' + 1 := lt_of_mul_lt_mul_right a2 ht.le
    have c1 : k' < k + 1 := by exact_mod_cast b1
    have c2 : k < k' + 1 := by exact_mod_cast b2
    omega
  · intro hk'; exact absurd (Finset.mem_range.2 hk) hk'

lemma abs_thetaS_le (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) {Cθ : ℝ} (hC : 0 ≤ Cθ)
    (hθb : ∀ i ω, |θ i ω| ≤ Cθ) (u : ℝ≥0) (ω : Ω) : |thetaS s θ n' u ω| ≤ n' * Cθ := by
  unfold thetaS
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ Finset.range n', |if s i ≤ u ∧ u < s (i + 1) then θ i ω else 0| ≤ Cθ := by
    intro i _
    split_ifs
    · exact hθb i ω
    · simpa using hC
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `thetaS` does not change between `x ≤ u` unless some jump time lies in `(x, u]`. -/
lemma thetaS_eq_of_no_jump (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) {x u : ℝ≥0} (hxu : x ≤ u)
    (hno : ∀ l, l ≤ n' → ¬ (x < s l ∧ s l ≤ u)) (ω : Ω) :
    thetaS s θ n' x ω = thetaS s θ n' u ω := by
  unfold thetaS
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n' := Finset.mem_range.1 hi
  have hiff : (s i ≤ x ∧ x < s (i + 1)) ↔ (s i ≤ u ∧ u < s (i + 1)) := by
    constructor
    · rintro ⟨a, b⟩
      refine ⟨a.trans hxu, lt_of_not_ge fun h => hno (i + 1) (by omega) ⟨b, h⟩⟩
    · rintro ⟨a, b⟩
      refine ⟨le_of_not_gt fun h => hno i hi'.le ⟨h, a⟩, lt_of_le_of_lt hxu b⟩
  by_cases hc : s i ≤ u ∧ u < s (i + 1)
  · rw [if_pos (hiff.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]

/-- **S1b pointwise bound** on a cell: the error of the `thetaS · clamp` step integrand against
`thetaS · H` splits into the left-point error of `clamp H` and a jump term supported on
`[s_l, s_l + t/2^N)`. -/
lemma sq_add_le_two_S1b (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

lemma S1b_pointwise (H : ℝ≥0 → Ω → ℝ) (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) {Cθ : ℝ}
    (hC : 0 ≤ Cθ) (hθb : ∀ i ω, |θ i ω| ≤ Cθ) (t : ℝ≥0) (N : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    (itoStepValue t N (fun k ω => thetaS s θ n' (dyTime t N k) ω *
        clampH H N (dyTime t N k) ω) u ω - thetaS s θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2 ≤
      2 * ((n' : ℝ) * Cθ) ^ 2 *
        (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2 +
      2 * (2 * (n' : ℝ) * Cθ) ^ 2 * H u.toNNReal ω ^ 2 *
        ∑ l ∈ Finset.range (n' + 1),
          (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator (fun _ => (1 : ℝ)) u := by
  obtain ⟨k, hk, h1, h2, hval⟩ := stepValue_cell (Ω := Ω) t N hu ω
  rw [hval, hval]
  simp only [leftCoef]
  simp only [NNReal.val_eq_coe] at h1 h2
  have hu0 : 0 ≤ u := hu.1.le
  have hcu : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu0
  set A := thetaS s θ n' (dyTime t N k) ω with hAdef
  set B := thetaS s θ n' u.toNNReal ω with hBdef
  set c := clampH H N (dyTime t N k) ω
  set h := H u.toNNReal ω
  set Sg1 := ∑ l ∈ Finset.range (n' + 1),
    (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator (fun _ => (1 : ℝ)) u with hSg
  have hA : |A| ≤ n' * Cθ := abs_thetaS_le s θ n' hC hθb _ ω
  have hB : |B| ≤ n' * Cθ := abs_thetaS_le s θ n' hC hθb _ ω
  have hA2 : A ^ 2 ≤ ((n' : ℝ) * Cθ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hsum0 : 0 ≤ Sg1 :=
    Finset.sum_nonneg fun l _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hjump : (A - B) ^ 2 ≤ (2 * (n' : ℝ) * Cθ) ^ 2 * Sg1 := by
    by_cases hno : ∀ l, l ≤ n' → ¬ (dyTime t N k < s l ∧ s l ≤ u.toNNReal)
    · have hxu : dyTime t N k ≤ u.toNNReal := by
        rw [← NNReal.coe_le_coe, dyTime_real, hcu]; exact h1.le
      rw [hAdef, hBdef, thetaS_eq_of_no_jump s θ n' hxu hno ω, sub_self]
      have : 0 ≤ (2 * (n' : ℝ) * Cθ) ^ 2 * Sg1 := mul_nonneg (sq_nonneg _) hsum0
      simpa using this
    · push_neg at hno
      obtain ⟨l, hl, hl1, hl2⟩ := hno
      have hl1' : (k : ℝ) * t / 2 ^ N < s l := by
        have := (NNReal.coe_lt_coe.2 hl1); rwa [dyTime_real] at this
      have hl2' : (s l : ℝ) ≤ u := by
        have := (NNReal.coe_le_coe.2 hl2); rwa [hcu] at this
      have hmem : u ∈ Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N) := by
        refine ⟨hl2', ?_⟩
        have e : ((k : ℝ) + 1) * t / 2 ^ N = (k : ℝ) * t / 2 ^ N + t / 2 ^ N := by ring
        linarith
      have hone : (1 : ℝ) ≤ Sg1 := by
        have := Finset.single_le_sum (f := fun l => (Set.Ico ((s l : ℝ))
          ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator (fun _ => (1 : ℝ)) u)
          (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
        simp only [Set.indicator_of_mem hmem] at this
        exact this
      have hAB : |A - B| ≤ 2 * n' * Cθ := by
        have := abs_sub A B; linarith
      have hAB2 : (A - B) ^ 2 ≤ (2 * (n' : ℝ) * Cθ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hAB 2
      exact hAB2.trans (le_mul_of_one_le_right (sq_nonneg _) hone)
  have i1 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg (c - h))
  have i2 := mul_le_mul_of_nonneg_right hjump (sq_nonneg h)
  have e0 : (A * c - B * h) ^ 2 ≤ 2 * (A ^ 2 * (c - h) ^ 2) + 2 * ((A - B) ^ 2 * h ^ 2) := by
    calc (A * c - B * h) ^ 2 = (A * (c - h) + (A - B) * h) ^ 2 := by ring
      _ ≤ 2 * (A * (c - h)) ^ 2 + 2 * ((A - B) * h) ^ 2 := sq_add_le_two_S1b _ _
      _ = 2 * (A ^ 2 * (c - h) ^ 2) + 2 * ((A - B) ^ 2 * h ^ 2) := by ring
  first | linarith | nlinarith

end StochCalcTC


namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Off `bigSet H t R`, a path-continuous `H` is bounded by `R` on all of `[0,t]`. -/
lemma abs_le_of_not_mem_bigSet' {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    {t : ℝ≥0} (ht : 0 < t) {R : ℝ} {ω : Ω} (hω : ω ∉ bigSet H t R) {r : ℝ≥0} (hr : r ≤ t) :
    |H r ω| ≤ R := by
  have h0 : Tendsto (fun n : ℕ => (t : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hlim : Tendsto (fun n => dyTime t n (rk t r n)) atTop (𝓝 r) := by
    rw [← NNReal.tendsto_coe]
    have hlow : Tendsto (fun n : ℕ => (r : ℝ) - (t : ℝ) / 2 ^ n) atTop (𝓝 (r : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (r : ℝ))).sub h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
      (fun n => NNReal.coe_le_coe.2 (dy_rk_le ht r n))
    have h1 := NNReal.coe_lt_coe.2 (lt_dy_rk_succ ht r n)
    rw [dyTime_real] at h1
    rw [dyTime_real]
    push_cast at h1
    have e : (((rk t r n : ℕ) : ℝ) + 1) * t / 2 ^ n =
        ((rk t r n : ℕ) : ℝ) * t / 2 ^ n + t / 2 ^ n := by ring
    linarith
  have hc : Tendsto (fun n => |H (dyTime t n (rk t r n)) ω|) atTop (𝓝 (|H r ω|)) :=
    (continuous_abs.tendsto _).comp (((hHc ω).tendsto r).comp hlim)
  exact le_of_tendsto' hc fun n => abs_le_of_not_mem_bigSet hω (rk_le ht hr n)

lemma intervalIntegrable_indicator_Ico_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ico a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ico

lemma integral_indicator_Ico_le (T a h : ℝ) (hT : 0 ≤ T) (hh : 0 ≤ h) :
    ∫ u in (0 : ℝ)..T, (Set.Ico a (a + h)).indicator (fun _ => (1 : ℝ)) u ≤ h := by
  rw [intervalIntegral.integral_of_le hT, integral_indicator measurableSet_Ico,
    setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply measurableSet_Ico]
  have hle : volume (Set.Ico a (a + h) ∩ Set.Ioc 0 T) ≤ volume (Set.Ico a (a + h)) :=
    measure_mono Set.inter_subset_left
  have hfin : volume (Set.Ico a (a + h)) ≠ ⊤ := by simp
  calc (volume (Set.Ico a (a + h) ∩ Set.Ioc 0 T)).toReal
      ≤ (volume (Set.Ico a (a + h))).toReal := ENNReal.toReal_mono hfin hle
    _ = h := by rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]; ring

lemma integral_sum_indicator_Ico_le (T h : ℝ) (hT : 0 ≤ T) (hh : 0 ≤ h) (a : ℕ → ℝ) (m : ℕ) :
    ∫ u in (0 : ℝ)..T, ∑ l ∈ Finset.range m,
      (Set.Ico (a l) (a l + h)).indicator (fun _ => (1 : ℝ)) u ≤ m * h := by
  rw [intervalIntegral.integral_finsetSum
    (fun l _ => intervalIntegrable_indicator_Ico_const T _ _ 1 hT)]
  calc ∑ l ∈ Finset.range m, ∫ u in (0 : ℝ)..T,
        (Set.Ico (a l) (a l + h)).indicator (fun _ => (1 : ℝ)) u
      ≤ ∑ _l ∈ Finset.range m, h :=
        Finset.sum_le_sum fun l _ => integral_indicator_Ico_le T (a l) h hT hh
    _ = m * h := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma sub_sq_intervalIntegrable {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) volume 0 t.val := by
  have hH : Continuous fun u : ℝ => H u.toNNReal ω := (hHc ω).comp continuous_real_toNNReal
  have h1 := itoStepValue_sq_intervalIntegrable t n e ω
  have h2 := (itoStepValue_intervalIntegrable t n e ω).mul_continuousOn hH.continuousOn
  have h3 := (hH.pow 2).intervalIntegrable (μ := volume) 0 t.val
  have h4 := (h1.sub (h2.const_mul 2)).add h3
  have heq : (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) = fun u =>
      (itoStepValue t n e u ω) ^ 2 - 2 * (itoStepValue t n e u ω * H u.toNNReal ω) +
        H u.toNNReal ω ^ 2 := by
    funext u; ring
  rw [heq]; exact h4

lemma integral_le_of_ae_aux {f g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hg : IntervalIntegrable g volume 0 T) (hf0 : ∀ u, 0 ≤ f u)
    (h : ∀ u ∈ Set.Ioc 0 T, f u ≤ g u) : ∫ u in (0 : ℝ)..T, f u ≤ ∫ u in (0 : ℝ)..T, g u := by
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
  refine integral_mono_of_nonneg (Eventually.of_forall hf0)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hg) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall h)

/-- **S1b**: the `thetaS · clamp_N H` left-point approximants satisfy the integrated-squared-error
clause of `HasBrownianItoIntegral` for the integrand `thetaS · H`. -/
theorem S1b_tendsto {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (hHc : ∀ ω, Continuous fun s => H s ω)
    (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) {Cθ : ℝ} (hC : 0 ≤ Cθ)
    (hθb : ∀ i ω, |θ i ω| ≤ Cθ) (t : ℝ≥0) :
    TendstoInMeasure P (fun (N : ℕ) ω => ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t N (fun k ω => thetaS s θ n' (dyTime t N k) ω *
        clampH H N (dyTime t N k) ω) u ω - thetaS s θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2)
      atTop (fun _ => 0) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht
  · subst ht0
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have : ∀ N : ℕ, {ω : Ω | ε ≤ dist (∫ u in (0 : ℝ)..((0 : ℝ≥0) : ℝ),
      (itoStepValue 0 N (fun k ω => thetaS s θ n' (dyTime 0 N k) ω *
        clampH H N (dyTime 0 N k) ω) u ω - thetaS s θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2)
        0} = ∅ := by
      intro N
      ext ω
      simp only [NNReal.coe_zero, intervalIntegral.integral_same, dist_self, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    simp only [NNReal.val_eq_coe] at this ⊢
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  set K1 : ℝ := 2 * ((n' : ℝ) * Cθ) ^ 2 with hK1
  set c2 : ℝ := 2 * (2 * (n' : ℝ) * Cθ) ^ 2 with hc2
  have hK1n : 0 ≤ K1 := by positivity
  have hc2n : 0 ≤ c2 := by positivity
  have htr : (0 : ℝ) < t.val := ht
  have hA := clampLeft_approx hHm hHc t
  rw [tendstoInMeasure_iff_dist] at hA ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHm hHc t)) (δ / 2) hδ2).exists
  set ε' : ℝ := ε / (2 * (K1 + 1)) with hε'def
  have hε' : 0 < ε' := by positivity
  have h1 := (ENNReal.tendsto_nhds_zero.1 (hA ε' hε')) (δ / 2) hδ2
  have h0 : Tendsto (fun N : ℕ => (t : ℝ) / 2 ^ N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h0' : Tendsto (fun N : ℕ => c2 * (R : ℝ) ^ 2 * (((n' + 1 : ℕ) : ℝ) * ((t : ℝ) / 2 ^ N)))
      atTop (𝓝 0) := by
    simpa using (h0.const_mul (((n' + 1 : ℕ) : ℝ))).const_mul (c2 * (R : ℝ) ^ 2)
  have h2 := h0'.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [h1, h2] with N hN1 hN2
  calc P {ω | ε ≤ dist (∫ u in (0 : ℝ)..t.val,
      (itoStepValue t N (fun k ω => thetaS s θ n' (dyTime t N k) ω *
        clampH H N (dyTime t N k) ω) u ω - thetaS s θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2) 0}
      ≤ P ({ω | ε' ≤ dist (∫ u in (0 : ℝ)..t.val,
          (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2) 0} ∪
          bigSet H t R) := by
        refine measure_mono fun ω hω => ?_
        by_contra hcon
        simp only [Set.mem_union, not_or, Set.mem_setOf_eq, Real.dist_eq, sub_zero,
          not_le] at hcon hω
        obtain ⟨hcA, hcB⟩ := hcon
        -- pointwise bound with `H² ≤ R²` on `(0,t]`
        have hHR : ∀ u ∈ Set.Ioc (0 : ℝ) t.val, H u.toNNReal ω ^ 2 ≤ (R : ℝ) ^ 2 := by
          intro u hu
          have hut : u.toNNReal ≤ t := by
            rw [Real.toNNReal_le_iff_le_coe]; exact hu.2
          have hb := abs_le_of_not_mem_bigSet' hHc ht hcB hut
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have h1i : IntervalIntegrable (fun u => K1 *
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2)
            volume 0 t.val := (sub_sq_intervalIntegrable hHc t N _ ω).const_mul K1
        have hsi : IntervalIntegrable (fun u => ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u) volume 0 t.val := by
          have h := IntervalIntegrable.sum (Finset.range (n' + 1)) fun l _ =>
            intervalIntegrable_indicator_Ico_const t.val ((s l : ℝ))
              ((s l : ℝ) + (t : ℝ) / 2 ^ N) 1 htr.le
          rw [Finset.sum_fn] at h
          exact h
        have h2i : IntervalIntegrable (fun u => c2 * (R : ℝ) ^ 2 * ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u) volume 0 t.val := hsi.const_mul _
        have hpt : ∀ u ∈ Set.Ioc (0 : ℝ) t.val,
            (itoStepValue t N (fun k ω => thetaS s θ n' (dyTime t N k) ω *
              clampH H N (dyTime t N k) ω) u ω - thetaS s θ n' u.toNNReal ω *
                H u.toNNReal ω) ^ 2 ≤ (fun u => K1 *
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2) u +
              (fun u => c2 * (R : ℝ) ^ 2 * ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u) u := by
          intro u hu
          have hp := S1b_pointwise H s θ n' hC hθb t N hu ω
          have hS0 : 0 ≤ ∑ l ∈ Finset.range (n' + 1),
              (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
                (fun _ => (1 : ℝ)) u :=
            Finset.sum_nonneg fun l _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
          have hm : c2 * H u.toNNReal ω ^ 2 * ∑ l ∈ Finset.range (n' + 1),
              (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
                (fun _ => (1 : ℝ)) u ≤ c2 * (R : ℝ) ^ 2 * ∑ l ∈ Finset.range (n' + 1),
              (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
                (fun _ => (1 : ℝ)) u :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hHR u hu) hc2n) hS0
          dsimp only
          linarith
        have hint_le := integral_le_of_ae_aux htr.le (h1i.add h2i) (fun u => sq_nonneg _) hpt
        have hsplit := intervalIntegral.integral_add h1i h2i
        have hc1 : ∫ u in (0 : ℝ)..t.val, K1 *
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2 =
            K1 * ∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2 :=
          intervalIntegral.integral_const_mul _ _
        have hc2' : ∫ u in (0 : ℝ)..t.val, c2 * (R : ℝ) ^ 2 * ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator (fun _ => (1 : ℝ)) u =
            c2 * (R : ℝ) ^ 2 * ∫ u in (0 : ℝ)..t.val, ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator (fun _ => (1 : ℝ)) u :=
          intervalIntegral.integral_const_mul _ _
        have hint2 : (∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (fun k ω => thetaS s θ n' (dyTime t N k) ω *
              clampH H N (dyTime t N k) ω) u ω - thetaS s θ n' u.toNNReal ω *
                H u.toNNReal ω) ^ 2) ≤ K1 * (∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2) +
            c2 * (R : ℝ) ^ 2 * ∫ u in (0 : ℝ)..t.val, ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s l : ℝ)) ((s l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u := by
          rw [← hc1, ← hc2', ← hsplit]; exact hint_le
        have hind := integral_sum_indicator_Ico_le t.val ((t : ℝ) / 2 ^ N) htr.le (by positivity)
          (fun l => (s l : ℝ)) (n' + 1)
        have hA0 : 0 ≤ ∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2 :=
          intervalIntegral.integral_nonneg htr.le (fun u _ => sq_nonneg _)
        rw [abs_of_nonneg hA0] at hcA
        have hF0 : 0 ≤ ∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (fun k ω => thetaS s θ n' (dyTime t N k) ω *
              clampH H N (dyTime t N k) ω) u ω - thetaS s θ n' u.toNNReal ω *
                H u.toNNReal ω) ^ 2 :=
          intervalIntegral.integral_nonneg htr.le (fun u _ => sq_nonneg _)
        rw [abs_of_nonneg hF0] at hω
        have hK1e : K1 * ε' ≤ ε / 2 := by
          rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
          have e : ε * (2 * (K1 + 1)) = K1 * ε * 2 + 2 * ε := by ring
          rw [e]; linarith
        have t1 := mul_le_mul_of_nonneg_left hcA.le hK1n
        have t2 := mul_le_mul_of_nonneg_left hind (mul_nonneg hc2n (sq_nonneg (R : ℝ)))
        push_cast at hN2 t2
        linarith [hint2, t1, t2, hK1e, hN2, hω]
    _ ≤ δ / 2 + δ / 2 := (measure_union_le _ _).trans (add_le_add hN1 hR)
    _ = δ := ENNReal.add_halves δ

end StochCalcTC


namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

omit mΩ in
lemma thetaS_measurable_u (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) (ω : Ω) :
    Measurable (fun u : ℝ => thetaS s θ n' u.toNNReal ω) := by
  unfold thetaS
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_le (f := fun _ : ℝ => s i) (g := fun u : ℝ => u.toNNReal)
    measurable_const measurable_real_toNNReal).inter
    (measurableSet_lt (f := fun u : ℝ => u.toNNReal) (g := fun _ : ℝ => s (i + 1))
      measurable_real_toNNReal measurable_const)

lemma thetaS_measF (ℱ : ℝ≥0 → MeasurableSpace Ω) (hℱ : Monotone ℱ) (s : ℕ → ℝ≥0)
    (θ : ℕ → Ω → ℝ) (n' : ℕ) (hθm : ∀ i, Measurable[ℱ (s i)] (θ i)) (x : ℝ≥0) :
    Measurable[ℱ x] (thetaS s θ n' x) := by
  unfold thetaS
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : s i ≤ x ∧ x < s (i + 1)
  · simp only [if_pos h]; exact (hθm i).mono (hℱ h.1) le_rfl
  · simp only [if_neg h]; exact measurable_const

lemma tendstoInMeasure_of_zero {P : Measure Ω} (f : ℕ → Ω → ℝ) (hf : ∀ n ω, f n ω = 0)
    (g : Ω → ℝ) (hg : ∀ ω, g ω = 0) : TendstoInMeasure P f atTop g := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have : ∀ n, {ω | ε ≤ dist (f n ω) (g ω)} = ∅ := by
    intro n; ext ω
    simp only [hf, hg, dist_self, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  simp only [this, measure_empty]
  exact tendsto_const_nhds

end StochCalcTC


namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

theorem stepSum_simple_tendsto' {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) {t : ℝ≥0} (ht : 0 < t)
    (n' : ℕ) (s : ℕ → ℝ≥0) (hs : Monotone s) (θ : ℕ → Ω → ℝ) {Cθ : ℝ}
    (hθb : ∀ i ω, |θ i ω| ≤ Cθ)
    (hJc : ∀ i, i ≤ n' → TendstoInMeasure P
      (fun n => J (dyTime t n (rk t (min (s i) t) n))) atTop (J (min (s i) t))) :
    TendstoInMeasure P (fun N => itoStepSum (fun s ω => W s ω j) t N
      (fun k ω => thetaS s θ n' (dyTime t N k) ω * clampH H N (dyTime t N k) ω)) atTop
      (fun ω => ∑ i ∈ Finset.range n',
        θ i ω * (J (min (s (i + 1)) t) ω - J (min (s i) t) ω)) := by
  have heq : ∀ N ω, itoStepSum (fun s ω => W s ω j) t N
      (fun k ω => thetaS s θ n' (dyTime t N k) ω * clampH H N (dyTime t N k) ω) ω =
      ∑ i ∈ Finset.range n', θ i ω *
        (itoStepSum (fun s ω => W s ω j) t N (cMask H t N 0 (min (s (i + 1)) t)) ω -
          itoStepSum (fun s ω => W s ω j) t N (cMask H t N 0 (min (s i) t)) ω) := by
    intro N ω
    simp only [itoStepSum_sub]
    unfold itoStepSum thetaS
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < 2 ^ N := Finset.mem_range.1 hk
    rw [mask_min H N ht _ hk', mask_min H N ht _ hk']
    have hsplit := split_mask H t N (hs (Nat.le_succ i)) k ω
    have e1 : cMask H t N 0 (s (i + 1)) k ω - cMask H t N 0 (s i) k ω =
        cMask H t N (s i) (s (i + 1)) k ω := by rw [hsplit]; ring
    rw [e1]
    unfold cMask
    split_ifs <;> ring
  have hlim : TendstoInMeasure P (fun N ω => ∑ i ∈ Finset.range n', θ i ω *
      (itoStepSum (fun s ω => W s ω j) t N (cMask H t N 0 (min (s (i + 1)) t)) ω -
        itoStepSum (fun s ω => W s ω j) t N (cMask H t N 0 (min (s i) t)) ω)) atTop
      (fun ω => ∑ i ∈ Finset.range n',
        θ i ω * (J (min (s (i + 1)) t) ω - J (min (s i) t) ω)) := by
    refine tendstoInMeasure_finsetSum_real _ fun i hi => ?_
    have hi' : i < n' := Finset.mem_range.1 hi
    refine tendstoInMeasure_mul_left_real (θ i) (R := max Cθ 1) (lt_of_lt_of_le one_pos
      (le_max_right _ _)) (fun ω => (hθb i ω).trans (le_max_left _ _)) ?_
    exact tendstoInMeasure_sub_real
      (truncSum_tendsto hW x₀ j hHm hHc hJ ht (min_le_right _ _) (hJc (i + 1) hi'))
      (truncSum_tendsto hW x₀ j hHm hHc hJ ht (min_le_right _ _) (hJc i hi'.le))
  have hfun : (fun N => itoStepSum (fun s ω => W s ω j) t N
      (fun k ω => thetaS s θ n' (dyTime t N k) ω * clampH H N (dyTime t N k) ω)) =
      (fun N ω => ∑ i ∈ Finset.range n', θ i ω *
      (itoStepSum (fun s ω => W s ω j) t N (cMask H t N 0 (min (s (i + 1)) t)) ω -
        itoStepSum (fun s ω => W s ω j) t N (cMask H t N 0 (min (s i) t)) ω)) := by
    funext N ω; exact heq N ω
  rw [hfun]; exact hlim


lemma dy_rk_tendsto {t : ℝ≥0} (ht : 0 < t) (r : ℝ≥0) :
    Tendsto (fun n => dyTime t n (rk t r n)) atTop (𝓝 r) := by
  have h0 : Tendsto (fun n : ℕ => (t : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  rw [← NNReal.tendsto_coe]
  have hlow : Tendsto (fun n : ℕ => (r : ℝ) - (t : ℝ) / 2 ^ n) atTop (𝓝 (r : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (r : ℝ))).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => NNReal.coe_le_coe.2 (dy_rk_le ht r n))
  have h1 := NNReal.coe_lt_coe.2 (lt_dy_rk_succ ht r n)
  rw [dyTime_real] at h1
  rw [dyTime_real]
  push_cast at h1
  have e : (((rk t r n : ℕ) : ℝ) + 1) * t / 2 ^ n =
      ((rk t r n : ℕ) : ℝ) * t / 2 ^ n + t / 2 ^ n := by ring
  linarith

lemma S1_clause1 {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) {Cθ : ℝ} (hC : 0 ≤ Cθ)
    (hθb : ∀ i ω, |θ i ω| ≤ Cθ) (t : ℝ≥0) (ω : Ω) :
    IntervalIntegrable (fun u : ℝ => (thetaS s θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2)
      volume 0 t.val := by
  have hg : IntervalIntegrable (fun u : ℝ => H u.toNNReal ω ^ 2) volume 0 t.val :=
    (((hHc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.2] at hg ⊢
  have hb := hg.bdd_mul (f := fun u : ℝ => thetaS s θ n' u.toNNReal ω ^ 2)
    (c := ((n' : ℝ) * Cθ) ^ 2) ((thetaS_measurable_u s θ n' ω).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_thetaS_le s θ n' hC hθb _ ω) 2)
  have heq : (fun u : ℝ => (thetaS s θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2) =
      fun u => thetaS s θ n' u.toNNReal ω ^ 2 * H u.toNNReal ω ^ 2 := by
    funext u; ring
  rw [heq]; exact hb

end StochCalcTC


set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma condExp_stop {T : ℝ≥0} {F : Filtration ℝ≥0 mΩ} {Q : Measure Ω} [IsFiniteMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsMartingaleOn T F Q X) (c : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) : Q[X (min c t) | F s] =ᵐ[Q] X (min c s) := by
  rcases le_or_gt c s with hcs | hsc
  · rw [min_eq_left (hcs.trans hst), min_eq_left hcs]
    rw [condExp_of_stronglyMeasurable (F.le s)
      ((hX.1 c (hcs.trans (hst.trans htT))).mono (F.mono hcs))
      (hX.2.1 c (hcs.trans (hst.trans htT)))]
  · rw [min_eq_right hsc.le]
    exact hX.2.2 s (min c t) (le_min hsc.le hst) ((min_le_right _ _).trans htT)

lemma mart_zero (T : ℝ≥0) (F : Filtration ℝ≥0 mΩ) (Q : Measure Ω) [IsFiniteMeasure Q] :
    IsMartingaleOn T F Q (fun _ _ => (0 : ℝ)) := by
  refine ⟨fun _ _ => stronglyMeasurable_const, fun _ _ => integrable_const _, fun s t _ _ => ?_⟩
  rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, condExp_zero]

lemma mart_add {T : ℝ≥0} {F : Filtration ℝ≥0 mΩ} {Q : Measure Ω} [IsFiniteMeasure Q]
    {Y1 Y2 : ℝ≥0 → Ω → ℝ} (h1 : IsMartingaleOn T F Q Y1) (h2 : IsMartingaleOn T F Q Y2) :
    IsMartingaleOn T F Q (fun t ω => Y1 t ω + Y2 t ω) := by
  refine ⟨fun t ht => (h1.1 t ht).add (h2.1 t ht), fun t ht => (h1.2.1 t ht).add (h2.2.1 t ht),
    fun s t hst htT => ?_⟩
  exact (condExp_add (h1.2.1 t htT) (h2.2.1 t htT) _).trans
    ((h1.2.2 s t hst htT).add (h2.2.2 s t hst htT))

lemma mart_sum {T : ℝ≥0} {F : Filtration ℝ≥0 mΩ} {Q : Measure Ω} [IsFiniteMeasure Q]
    {Y : ℕ → ℝ≥0 → Ω → ℝ} (n : ℕ) (h : ∀ i, i < n → IsMartingaleOn T F Q (Y i)) :
    IsMartingaleOn T F Q (fun t ω => ∑ i ∈ Finset.range n, Y i t ω) := by
  induction n with
  | zero => simpa using mart_zero T F Q
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    exact mart_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

/-- One simple term `θ (X(b ∧ t) − X(a ∧ t))` is a martingale. -/
theorem mart_term {T : ℝ≥0} {F : Filtration ℝ≥0 mΩ} {Q : Measure Ω} [IsFiniteMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsMartingaleOn T F Q X) {a b : ℝ≥0} (hab : a ≤ b)
    {θ : Ω → ℝ} (hθm : StronglyMeasurable[F a] θ) {C : ℝ} (hθb : ∀ ω, |θ ω| ≤ C) :
    IsMartingaleOn T F Q (fun t ω => θ ω * (X (min b t) ω - X (min a t) ω)) := by
  have hint : ∀ c t, t ≤ T → Integrable (X (min c t)) Q := fun c t ht =>
    hX.2.1 _ ((min_le_right _ _).trans ht)
  have hYint : ∀ t, t ≤ T → Integrable (fun ω => θ ω * (X (min b t) ω - X (min a t) ω)) Q :=
    fun t ht => ((hint b t ht).sub (hint a t ht)).bdd_mul
      (hθm.mono (F.le a)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hθb ω)
  -- the computation for `a ≤ s' ≤ t`
  have key : ∀ s' t, a ≤ s' → s' ≤ t → t ≤ T →
      Q[fun ω => θ ω * (X (min b t) ω - X (min a t) ω) | F s'] =ᵐ[Q]
        fun ω => θ ω * (X (min b s') ω - X (min a s') ω) := by
    intro s' t has hst htT
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := F s') (μ := Q)
      (hθm.mono (F.mono has)) (hYint t htT) ((hint b t htT).sub (hint a t htT))
    have h2 := condExp_sub (hint b t htT) (hint a t htT) (F s')
    have h3 := (condExp_stop hX b hst htT).sub (condExp_stop hX a hst htT)
    refine h1.trans ?_
    filter_upwards [h2, h3] with ω e2 e3
    simp only [Pi.mul_apply, Pi.sub_apply] at e2 e3 ⊢
    have e2' : Q[fun ω => X (min b t) ω - X (min a t) ω | F s'] ω =
        Q[X (min b t) | F s'] ω - Q[X (min a t) | F s'] ω := e2
    rw [e2', e3]
  refine ⟨fun t ht => ?_, hYint, fun s t hst htT => ?_⟩ <;> beta_reduce
  · by_cases hat : a ≤ t
    · exact (hθm.mono (F.mono hat)).mul
        (((hX.1 _ ((min_le_right _ _).trans ht)).mono (F.mono (min_le_right _ _))).sub
          ((hX.1 _ ((min_le_right _ _).trans ht)).mono (F.mono (min_le_right _ _))))
    · have hta : t ≤ a := le_of_not_ge hat
      have h0 : (fun ω => θ ω * (X (min b t) ω - X (min a t) ω)) = fun _ => 0 := by
        funext ω; rw [min_eq_right hta, min_eq_right (hta.trans hab), sub_self, mul_zero]
      rw [h0]; exact stronglyMeasurable_const
  · by_cases has : a ≤ s
    · exact key s t has hst htT
    · have hsa : s ≤ a := le_of_not_ge has
      have hYs : (fun ω => θ ω * (X (min b s) ω - X (min a s) ω)) = fun _ => 0 := by
        funext ω; rw [min_eq_right hsa, min_eq_right (hsa.trans hab), sub_self, mul_zero]
      rw [hYs]
      by_cases hta : t ≤ a
      · have h0 : (fun ω => θ ω * (X (min b t) ω - X (min a t) ω)) = fun _ => 0 := by
          funext ω; rw [min_eq_right hta, min_eq_right (hta.trans hab), sub_self, mul_zero]
        rw [h0, show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, condExp_zero]
      · have hat : a ≤ t := le_of_not_ge hta
        have hk := key a t le_rfl hat htT
        have hka : (fun ω => θ ω * (X (min b a) ω - X (min a a) ω)) = fun _ => 0 := by
          funext ω; rw [min_eq_right hab, min_self, sub_self, mul_zero]
        rw [hka] at hk
        refine (condExp_condExp_of_le (F.mono hsa) (F.le a)).symm.trans ?_
        refine (condExp_congr_ae hk).trans ?_
        rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, condExp_zero]

end StochCalcMart


namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The gains of the simple strategy. -/
def chiS (M : Model p Ω) (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n', θ i ω * (M.X (min (s (i + 1)) t) ω - M.X (min (s i) t) ω)

lemma X_measF (M : Model p Ω) (hM : M.Standing) (u : ℝ≥0) : StronglyMeasurable[M.F u] (M.X u) :=
  (hM.X_adapted u).mono (G_le_F M hM u)

lemma J_contOn (M : Model p Ω) (hM : M.Standing) :
    ∀ᵐ ω ∂M.P, ContinuousOn (fun u => M.J u ω) (Set.Icc 0 p.T) := by
  filter_upwards [hM.X_sde] with ω hω
  set g : ℝ≥0 → ℝ := fun u => M.X u ω - p.x₀ -
    ∫ v in (0 : ℝ)..(u : ℝ), M.X v.toNNReal ω * M.μ v.toNNReal ω with hg
  have hgc : Continuous g := by
    refine ((hM.X_cont ω).sub continuous_const).sub ?_
    have hc : Continuous fun v : ℝ => M.X v.toNNReal ω * M.μ v.toNNReal ω :=
      ((hM.X_cont ω).comp continuous_real_toNNReal).mul
        ((hM.μ_cont ω).comp continuous_real_toNNReal)
    exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp
      NNReal.continuous_coe
  have hJg : ∀ u, u ≤ p.T → M.J u ω = g u := fun u hu => by
    simp only [hg]; rw [hω u hu]; ring
  exact hgc.continuousOn.congr fun y hy => hJg y hy.2

lemma hJc_model (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) {t : ℝ≥0} (ht : 0 < t)
    {r : ℝ≥0} (hrT : r ≤ p.T) :
    TendstoInMeasure M.P (fun n => M.J (dyTime t n (rk t r n))) atTop (M.J r) := by
  have := hM.prob
  refine tendstoInMeasure_of_tendsto_ae (fun n =>
    (J_memLp M hM h4 _ ((dy_rk_le ht r n).trans hrT)).aestronglyMeasurable) ?_
  filter_upwards [J_contOn M hM] with ω hω
  have hmem : ∀ n, dyTime t n (rk t r n) ∈ Set.Icc 0 p.T := fun n =>
    ⟨zero_le, (dy_rk_le ht r n).trans hrT⟩
  exact (hω r ⟨zero_le, hrT⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨dy_rk_tendsto ht r, Eventually.of_forall hmem⟩)

/-- **S1 in the model**: Ito integral of `thetaS · Xσ` w.r.t. `(M.F, M.B)`. -/
theorem S1_model (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (n' : ℕ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hsT : ∀ i, i ≤ n' → s i ≤ p.T) (θ : ℕ → Ω → ℝ)
    {Cθ : ℝ} (hC : 0 ≤ Cθ) (hθb : ∀ i ω, |θ i ω| ≤ Cθ)
    (hθm : ∀ i, StronglyMeasurable[M.F (s i)] (θ i)) :
    HasBrownianItoIntegral M.P (fun t => M.F t) M.B (fun u ω => thetaS s θ n' u ω * Hx M u ω)
      (fun t ω => ∑ i ∈ Finset.range n',
        θ i ω * (M.J (min (s (i + 1)) t) ω - M.J (min (s i) t) ω)) := by
  have := hM.prob
  have hW := isStandardBrownian M hM
  have hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (Hx M) M.J := hasIto_B M hM hM.X_ito
  have hHae : ∀ u, AEStronglyMeasurable (Hx M u) M.P := fun u =>
    (Hx_meas M hM u).aestronglyMeasurable
  refine ⟨fun t ω => S1_clause1 (Hx_cont M hM) s θ n' hC hθb t ω, fun t => ?_⟩
  refine ⟨fun N k ω => thetaS s θ n' (dyTime t N k) ω * clampH (Hx M) N (dyTime t N k) ω,
    ?_, ?_, S1b_tendsto hHae (Hx_cont M hM) s θ n' hC hθb t, ?_⟩
  · intro N k _
    exact (thetaS_measF (fun t => M.F t) (fun a b h => M.F.mono h) s θ n'
      (fun i => (hθm i).measurable) (dyTime t N k)).mul
      (clampH_measurable (Hx_measF M hM _).measurable (N : ℝ))
  · intro N
    refine ⟨(n' : ℝ) * Cθ * N, fun k _ ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (abs_thetaS_le s θ n' hC hθb _ ω)
      (abs_clampH_le (Hx M) (Nat.cast_nonneg N) _ ω) (abs_nonneg _) (by positivity)
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht
    · subst ht0
      refine tendstoInMeasure_of_zero _ (fun N ω => ?_) _ (fun ω => ?_)
      · unfold itoStepSum
        simp
      · simp
    · have h := stepSum_simple_tendsto' hW 0 0 (Hx_cBP M hM) (Hx_cont M hM) hJ ht n' s hs θ hθb
        (fun i hi => hJc_model M hM h4 ht ((min_le_left _ _).trans (hsT i hi)))
      refine h.congr_left (fun n => ?_)
      filter_upwards [ae_W M hM] with ω hω
      simp only [itoStepSum, fun t => (hω t).1]

lemma thetaS_prog (M : Model p Ω) (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ)
    (hθm : ∀ i, StronglyMeasurable[M.F (s i)] (θ i)) :
    IsStronglyProgressive M.F (thetaS s θ n') := by
  intro j
  have hfst : Measurable[Subtype.instMeasurableSpace.prod (M.F j)]
      (fun q : Set.Iic j × Ω => (q.1 : ℝ≥0)) :=
    measurable_subtype_coe.comp (@measurable_fst _ _ _ (M.F j))
  have hsum : Measurable[Subtype.instMeasurableSpace.prod (M.F j)]
      (fun q : Set.Iic j × Ω => thetaS s θ n' q.1 q.2) := by
    unfold thetaS
    refine Finset.measurable_sum _ fun i _ => ?_
    by_cases hij : s i ≤ j
    · have hθ' : Measurable[Subtype.instMeasurableSpace.prod (M.F j)]
          (fun q : Set.Iic j × Ω => θ i q.2) :=
        ((hθm i).measurable.mono (M.F.mono hij) le_rfl).comp (@measurable_snd _ _ _ (M.F j))
      have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (M.F j)]
          {q : Set.Iic j × Ω | s i ≤ (q.1 : ℝ≥0) ∧ (q.1 : ℝ≥0) < s (i + 1)} :=
        (measurableSet_le (f := fun _ : Set.Iic j × Ω => s i)
          (g := fun q : Set.Iic j × Ω => (q.1 : ℝ≥0)) measurable_const hfst).inter
          (measurableSet_lt (f := fun q : Set.Iic j × Ω => (q.1 : ℝ≥0))
            (g := fun _ : Set.Iic j × Ω => s (i + 1)) hfst measurable_const)
      exact Measurable.ite hset hθ' measurable_const
    · have h0 : (fun q : Set.Iic j × Ω =>
          if s i ≤ (q.1 : ℝ≥0) ∧ (q.1 : ℝ≥0) < s (i + 1) then θ i q.2 else 0) =
          fun _ => 0 := by
        funext q
        exact if_neg fun h => hij (h.1.trans q.1.2)
      rw [h0]; exact measurable_const
  exact hsum.stronglyMeasurable

lemma chiS_adapted (M : Model p Ω) (hM : M.Standing) (s : ℕ → ℝ≥0) (hs : Monotone s)
    (θ : ℕ → Ω → ℝ) (n' : ℕ) (hθm : ∀ i, StronglyMeasurable[M.F (s i)] (θ i)) :
    StronglyAdapted M.F (chiS M s θ n') := by
  intro t
  refine Measurable.stronglyMeasurable ?_
  unfold chiS
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases hit : s i ≤ t
  · exact ((hθm i).measurable.mono (M.F.mono hit) le_rfl).mul
      ((((X_measF M hM _).measurable).mono (M.F.mono (min_le_right _ _)) le_rfl).sub
        (((X_measF M hM _).measurable).mono (M.F.mono (min_le_right _ _)) le_rfl))
  · have hti : t ≤ s i := le_of_not_ge hit
    have h0 : (fun ω => θ i ω * (M.X (min (s (i + 1)) t) ω - M.X (min (s i) t) ω)) =
        fun _ => 0 := by
      funext ω
      rw [min_eq_right hti, min_eq_right (hti.trans (hs (Nat.le_succ i))), sub_self, mul_zero]
    rw [h0]; exact measurable_const

/-- In the degenerate case the drift `μ` vanishes on `[0,T]` (a.s.), given `T > 0`. -/
lemma mu_zero (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω) :
    ∀ᵐ ω ∂M.P, 0 < p.T → ∀ u : ℝ≥0, u ≤ p.T → M.μ u ω = 0 := by
  filter_upwards [int_η_sq_zero M hM h5 hdeg hQV] with ω hω hT u hu
  by_contra hne
  have hη : M.η u ω ≠ 0 := div_ne_zero hne (hM.σ_pos u ω).ne'
  have hpos : 0 < ∫ x in (0 : ℝ)..(p.T : ℝ), M.η x.toNNReal ω ^ 2 := by
    refine intervalIntegral.integral_pos (by exact_mod_cast hT)
      ((((η_cont M hM ω).comp continuous_real_toNNReal).pow 2).continuousOn)
      (fun x _ => sq_nonneg _) ⟨(u : ℝ), ⟨u.2, by exact_mod_cast hu⟩, ?_⟩
    rw [Real.toNNReal_coe]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hη))
  linarith

lemma X_memLp (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω) (t : ℝ≥0) (ht : t ≤ p.T) :
    MemLp (M.X t) 2 M.P := by
  have := hM.prob
  refine ((memLp_const p.x₀).add (J_memLp M hM h4 t ht)).ae_eq ?_
  filter_upwards [X_eq_J M hM h5 hdeg hQV] with ω hω
  simp only [Pi.add_apply]
  exact (hω t ht).symm

/-- **The simple strategy is admissible.** -/
theorem simple_mem_AX (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4)
    (h5 : M.Assumption5) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω)
    (n' : ℕ) (s : ℕ → ℝ≥0) (hs : Monotone s) (hsT : ∀ i, i ≤ n' → s i ≤ p.T)
    (θ : ℕ → Ω → ℝ) {Cθ : ℝ} (hC : 0 ≤ Cθ) (hθb : ∀ i ω, |θ i ω| ≤ Cθ)
    (hθm : ∀ i, StronglyMeasurable[M.F (s i)] (θ i)) :
    (thetaS s θ n', chiS M s θ n') ∈ M.AX := by
  have := hM.prob
  refine ⟨thetaS_prog M s θ n' hθm, chiS_adapted M hM s hs θ n' hθm, ⟨fun ω t ht => ?_,
    fun t ω => ∑ i ∈ Finset.range n',
      θ i ω * (M.J (min (s (i + 1)) t) ω - M.J (min (s i) t) ω), ?_, ?_⟩, ?_, ?_⟩
  · -- drift integrability
    have hg : IntervalIntegrable (fun u : ℝ => M.X u.toNNReal ω * M.μ u.toNNReal ω)
        volume 0 (t : ℝ) :=
      (((hM.X_cont ω).comp continuous_real_toNNReal).mul
        ((hM.μ_cont ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)] at hg ⊢
    have hb := hg.bdd_mul (f := fun u : ℝ => thetaS s θ n' u.toNNReal ω)
      (c := (n' : ℝ) * Cθ) (thetaS_measurable_u s θ n' ω).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs]; exact abs_thetaS_le s θ n' hC hθb _ ω)
    have heq : (fun u : ℝ => thetaS s θ n' u.toNNReal ω * M.X u.toNNReal ω *
        M.μ u.toNNReal ω) = fun u => thetaS s θ n' u.toNNReal ω *
          (M.X u.toNNReal ω * M.μ u.toNNReal ω) := by
      funext u; ring
    rw [heq]; exact hb
  · -- the Ito relation (cutoff redundant)
    have heq : (fun t ω => if t ≤ p.T then thetaS s θ n' t ω * M.X t ω * M.σ t ω else 0) =
        fun u ω => thetaS s θ n' u ω * Hx M u ω := by
      funext u ω
      split_ifs with hu
      · simp only [Hx]; ring
      · have h0 : thetaS s θ n' u ω = 0 := by
          unfold thetaS
          refine Finset.sum_eq_zero fun i hi => if_neg fun h => ?_
          have := hsT (i + 1) (Finset.mem_range.1 hi)
          exact hu (h.2.le.trans this)
        rw [h0, zero_mul]
    rw [heq]
    exact S1_model M hM h4 n' s hs hsT θ hC hθb hθm
  · -- gains identity
    filter_upwards [X_eq_J M hM h5 hdeg hQV, mu_zero M hM h5 hdeg hQV] with ω hX hμ t ht
    have hdrift : ∫ u in (0 : ℝ)..(t : ℝ), thetaS s θ n' u.toNNReal ω * M.X u.toNNReal ω *
        M.μ u.toNNReal ω = 0 := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | htp
      · rw [← ht0]; simp
      · have hT : 0 < p.T := lt_of_lt_of_le htp ht
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u hu => ?_)]
        · simp
        · rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hu
          have hut : u.toNNReal ≤ p.T := by
            rw [Real.toNNReal_le_iff_le_coe]; exact hu.2.trans (by exact_mod_cast ht)
          simp only [hμ hT _ hut, mul_zero]
    rw [hdrift, zero_add]
    unfold chiS
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hX _ ((min_le_right _ _).trans ht), hX _ ((min_le_right _ _).trans ht)]
    ring
  · -- L²
    show MemLp (fun ω => ∑ i ∈ Finset.range n',
      θ i ω * (M.X (min (s (i + 1)) p.T) ω - M.X (min (s i) p.T) ω)) 2 M.P
    refine memLp_finsetSum _ fun i _ => ?_
    exact StochCalcP6S.memLp_bdd_mul
      ((X_memLp M hM h4 h5 hdeg hQV _ (min_le_right _ _)).sub
        (X_memLp M hM h4 h5 hdeg hQV _ (min_le_right _ _)))
      ((hθm i).mono (M.F.le _)).aestronglyMeasurable (hθb i)
  · -- martingale under every `Q ∈ M_X`
    intro Q hQ
    have := hQ.1
    exact mart_sum n' fun i _ => mart_term hQ.2.2.2.2 (hs (Nat.le_succ i)) (hθm i) (hθb i)

end StochCalcS1M


namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- Clamp to `[-R, R]`. -/
noncomputable def clR (R x : ℝ) : ℝ := max (-R) (min R x)

lemma clR_zero {R : ℝ} (hR : 0 ≤ R) : clR R 0 = 0 := by
  simp only [clR]; rw [min_eq_right hR, max_eq_right (by linarith)]

lemma abs_clR_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clR R x| ≤ R := by
  simp only [clR]; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clR_eq {R x : ℝ} (hx : |x| ≤ R) : clR R x = x := by
  simp only [clR]; rw [abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1]

lemma clR_continuous (R : ℝ) : Continuous (clR R) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma clR_lip (R x y : ℝ) : |clR R x - clR R y| ≤ |x - y| := by
  simp only [clR]
  rw [max_comm (-R) (min R x), max_comm (-R) (min R y)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have := abs_min_sub_min_le_max R x R y
  rw [sub_self, abs_zero] at this
  exact this.trans (max_le (abs_nonneg _) le_rfl)

/-- The distance from `x` to `[-R,R]` is at most the distance to any point of it. -/
lemma abs_sub_clR_le {R x y : ℝ} (hy : |y| ≤ R) : |x - clR R x| ≤ |x - y| := by
  rw [abs_le] at hy
  simp only [clR]
  rcases le_total x R with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-R) x with h2 | h2
    · rw [max_eq_right h2, sub_self, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]; linarith

lemma clR_sq_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : clR R x ^ 2 ≤ x ^ 2 := by
  have h := clR_lip R x 0
  rw [clR_zero hR, sub_zero, sub_zero] at h
  exact sq_le_sq.2 h

lemma sub_clR_sq_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : (x - clR R x) ^ 2 ≤ x ^ 2 := by
  have h := abs_sub_clR_le (R := R) (x := x) (y := 0) (by rw [abs_zero]; exact hR)
  rw [sub_zero] at h
  exact sq_le_sq.2 h

/-- Clamping the coefficients clamps the step function (on `(0,t]`). -/
lemma sv_clR (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (R : ℝ) {u : ℝ} (hu : u ∈ Set.Ioc 0 t.val)
    (ω : Ω) :
    itoStepValue t n (fun k ω => clR R (c k ω)) u ω = clR R (itoStepValue t n c u ω) := by
  obtain ⟨k, -, -, -, hval⟩ := stepValue_cell (Ω := Ω) t n hu ω
  rw [hval, hval]

lemma sv_meas_u (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    Measurable fun u : ℝ => itoStepValue t n c u ω := by
  unfold itoStepValue
  refine Finset.measurable_sum _ fun k _ => ?_
  have hs : MeasurableSet {u : ℝ | (k : ℝ) * t.val / (2 : ℝ) ^ n < u ∧
      u ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n} :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)
  exact Measurable.ite hs measurable_const measurable_const

lemma sv_joint (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (hc : ∀ k, k < 2 ^ n → Measurable (c k)) :
    Measurable fun q : ℝ × Ω => itoStepValue t n c q.1 q.2 := by
  unfold itoStepValue
  refine Finset.measurable_sum _ fun k hk => ?_
  have hs : MeasurableSet {q : ℝ × Ω | (k : ℝ) * t.val / (2 : ℝ) ^ n < q.1 ∧
      q.1 ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  exact Measurable.ite hs ((hc k (Finset.mem_range.1 hk)).comp measurable_snd) measurable_const

lemma meas_intInt {F : ℝ → Ω → ℝ} (hF : Measurable fun q : ℝ × Ω => F q.1 q.2) {t : ℝ}
    (ht : 0 ≤ t) : Measurable fun ω => ∫ u in (0 : ℝ)..t, F u ω := by
  simp_rw [intervalIntegral.integral_of_le ht]
  exact (StronglyMeasurable.integral_prod_left (μ := volume.restrict (Set.Ioc 0 t))
    (f := F) hF.stronglyMeasurable).measurable

lemma ii_sub_sq {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : Measurable f) (hg : Measurable g)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 t)
    (hg2 : IntervalIntegrable (fun u => g u ^ 2) volume 0 t) :
    IntervalIntegrable (fun u => (f u - g u) ^ 2) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at hf2 hg2 ⊢
  refine Integrable.mono' ((hf2.const_mul 2).add (hg2.const_mul 2))
    ((hf.sub hg).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show (f u - g u) ^ 2 ≤ 2 * f u ^ 2 + 2 * g u ^ 2
  nlinarith [sq_nonneg (f u + g u)]

lemma ii_sq_of_le {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : Measurable f)
    (hg2 : IntervalIntegrable (fun u => g u ^ 2) volume 0 t) (hle : ∀ u, f u ^ 2 ≤ g u ^ 2) :
    IntervalIntegrable (fun u => f u ^ 2) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at hg2 ⊢
  refine Integrable.mono' hg2 (hf.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hle u

section pathwise

variable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (ω : Ω) {g : ℝ → ℝ}
  (hg : Measurable g) (hg2 : IntervalIntegrable (fun u => g u ^ 2) volume 0 t.val)
include hR hg hg2

/-- P1: clamping does not increase the integrated squared error. -/
lemma P1 : ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (fun k ω => clR R (c k ω)) u ω -
      clR R (g u)) ^ 2 ≤ ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω - g u) ^ 2 := by
  refine integral_le_of_ae_aux t.2 (ii_sub_sq t.2 (sv_meas_u t n c ω) hg
    (itoStepValue_sq_intervalIntegrable t n c ω) hg2) (fun u => sq_nonneg _) fun u hu => ?_
  rw [sv_clR t n c R hu ω]
  exact sq_le_sq.2 (clR_lip R _ _)

/-- P2: the clamped error is at most `(2R)² t`. -/
lemma P2 : ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (fun k ω => clR R (c k ω)) u ω -
      clR R (g u)) ^ 2 ≤ (2 * R) ^ 2 * t.val := by
  have h := integral_le_of_ae_aux (f := fun u => (itoStepValue t n (fun k ω => clR R (c k ω)) u ω -
      clR R (g u)) ^ 2) (g := fun _ => (2 * R) ^ 2) t.2 intervalIntegrable_const
    (fun u => sq_nonneg _) fun u hu => ?_
  · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    linarith
  · rw [sv_clR t n c R hu ω]
    have h1 := abs_clR_le hR (itoStepValue t n c u ω)
    have h2 := abs_clR_le hR (g u)
    have h3 : |clR R (itoStepValue t n c u ω) - clR R (g u)| ≤ 2 * R :=
      (abs_sub _ _).trans (by linarith)
    calc _ = |clR R (itoStepValue t n c u ω) - clR R (g u)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2

/-- P3: the clamping change of the step function is controlled by the error plus the tail. -/
lemma P3 : ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (fun k ω => clR R (c k ω)) u ω -
      itoStepValue t n c u ω) ^ 2 ≤
      2 * (∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω - g u) ^ 2) +
      2 * ∫ u in (0 : ℝ)..t.val, (g u - clR R (g u)) ^ 2 := by
  have hsv := sv_meas_u t n c ω
  have hclg : Measurable fun u => clR R (g u) := (clR_continuous R).measurable.comp hg
  have hcl2 : IntervalIntegrable (fun u => clR R (g u) ^ 2) volume 0 t.val :=
    ii_sq_of_le t.2 hclg hg2 fun u => clR_sq_le hR _
  have hi1 := ii_sub_sq t.2 hsv hg (itoStepValue_sq_intervalIntegrable t n c ω) hg2
  have hi2 := ii_sub_sq t.2 hg hclg hg2 hcl2
  have hsum : ∫ u in (0 : ℝ)..t.val, (2 * (itoStepValue t n c u ω - g u) ^ 2 +
      2 * (g u - clR R (g u)) ^ 2) =
      2 * (∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω - g u) ^ 2) +
      2 * ∫ u in (0 : ℝ)..t.val, (g u - clR R (g u)) ^ 2 := by
    rw [intervalIntegral.integral_add (hi1.const_mul 2) (hi2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [← hsum]
  refine integral_le_of_ae_aux t.2 ((hi1.const_mul 2).add (hi2.const_mul 2))
    (fun u => sq_nonneg _) fun u hu => ?_
  rw [sv_clR t n c R hu ω]
  set x := itoStepValue t n c u ω
  have h1 : |clR R x - x| ≤ |x - clR R (g u)| := by
    rw [abs_sub_comm]; exact abs_sub_clR_le (abs_clR_le hR _)
  have h2 : |x - clR R (g u)| ≤ |x - g u| + |g u - clR R (g u)| := by
    have := abs_add_le (x - g u) (g u - clR R (g u))
    rwa [show x - g u + (g u - clR R (g u)) = x - clR R (g u) by ring] at this
  have h3 : (clR R x - x) ^ 2 ≤ (|x - g u| + |g u - clR R (g u)|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  show (clR R x - x) ^ 2 ≤ 2 * (x - g u) ^ 2 + 2 * (g u - clR R (g u)) ^ 2
  nlinarith [sq_abs (x - g u), sq_abs (g u - clR R (g u)),
    sq_nonneg (|x - g u| - |g u - clR R (g u)|)]

/-- P4: `∫ (step)² ≤ (1+δ) ∫ g² + (1 + 1/δ) · (clamped error)`. -/
lemma P4 {δ : ℝ} (hδ : 0 < δ) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (fun k ω => clR R (c k ω)) u ω) ^ 2 ≤
      (1 + δ) * (∫ u in (0 : ℝ)..t.val, g u ^ 2) +
      (1 + 1 / δ) * ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (fun k ω => clR R (c k ω)) u ω -
        clR R (g u)) ^ 2 := by
  set c' : ℕ → Ω → ℝ := fun k ω => clR R (c k ω)
  have hsv := sv_meas_u t n c' ω
  have hclg : Measurable fun u => clR R (g u) := (clR_continuous R).measurable.comp hg
  have hcl2 : IntervalIntegrable (fun u => clR R (g u) ^ 2) volume 0 t.val :=
    ii_sq_of_le t.2 hclg hg2 fun u => clR_sq_le hR _
  have hi1 := ii_sub_sq t.2 hsv hclg (itoStepValue_sq_intervalIntegrable t n c' ω) hcl2
  have hstep : ∫ u in (0 : ℝ)..t.val, clR R (g u) ^ 2 ≤ ∫ u in (0 : ℝ)..t.val, g u ^ 2 :=
    integral_le_of_ae_aux t.2 hg2 (fun u => sq_nonneg _) fun u _ => clR_sq_le hR _
  have hmain : ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c' u ω) ^ 2 ≤
      (1 + δ) * (∫ u in (0 : ℝ)..t.val, clR R (g u) ^ 2) +
      (1 + 1 / δ) * ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c' u ω - clR R (g u)) ^ 2 := by
    have hsum : ∫ u in (0 : ℝ)..t.val, ((1 + δ) * clR R (g u) ^ 2 +
        (1 + 1 / δ) * (itoStepValue t n c' u ω - clR R (g u)) ^ 2) =
        (1 + δ) * (∫ u in (0 : ℝ)..t.val, clR R (g u) ^ 2) +
        (1 + 1 / δ) * ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c' u ω - clR R (g u)) ^ 2 := by
      rw [intervalIntegral.integral_add (hcl2.const_mul _) (hi1.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hsum]
    refine integral_le_of_ae_aux t.2 ((hcl2.const_mul _).add (hi1.const_mul _))
      (fun u => sq_nonneg _) fun u _ => ?_
    set x := itoStepValue t n c' u ω
    set y := clR R (g u)
    show x ^ 2 ≤ (1 + δ) * y ^ 2 + (1 + 1 / δ) * (x - y) ^ 2
    have hk : 0 ≤ (δ * y - (x - y)) ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
    have he : (δ * y - (x - y)) ^ 2 / δ = δ * y ^ 2 - 2 * y * (x - y) + (x - y) ^ 2 / δ := by
      field_simp; ring
    have he2 : (1 + 1 / δ) * (x - y) ^ 2 = (x - y) ^ 2 + (x - y) ^ 2 / δ := by ring
    nlinarith [hk, he, he2]
  have hδ1 : 0 ≤ 1 + δ := by linarith
  exact hmain.trans (add_le_add (mul_le_mul_of_nonneg_left hstep hδ1) le_rfl)

end pathwise

/-- Convergence in probability to `0` along an arbitrary level sequence `L` (version of
`ItoLib.itoStepSum_tendstoInMeasure_zero` where the level is not the index). -/
theorem stepSum_zero_seq {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (j : Fin d) (L : ℕ → ℕ)
    (c : ℕ → ℕ → Ω → ℝ)
    (hc : ∀ m k : ℕ, k < 2 ^ L m → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ L m)] (c m k))
    (hC : ∀ m, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ L m → ∀ ω, |c m k ω| ≤ C)
    (hq : TendstoInMeasure P (fun m ω => (∑ k ∈ Finset.range (2 ^ L m), c m k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ L m : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun m => itoStepSum (fun s ω => W s ω j) t (L m) (c m)) atTop
      (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hq ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall fun _ => le_top
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have he2top : e / 2 ≠ ⊤ := ENNReal.div_ne_top hetop (by norm_num)
  set δ : ℝ := (e / 2).toReal * ε ^ 2 with hδdef
  have hδpos : 0 < δ := mul_pos (ENNReal.toReal_pos he2.ne' he2top) (by positivity)
  have hδe : ENNReal.ofReal (δ / ε ^ 2) = e / 2 := by
    rw [hδdef, mul_div_cancel_right₀ _ (by positivity), ENNReal.ofReal_toReal he2top]
  have h2 := (ENNReal.tendsto_nhds_zero.1 (hq δ hδpos)) (e / 2) he2
  filter_upwards [h2] with m hm
  obtain ⟨C, hCn⟩ := hC m
  have hset : {ω | ε ≤ dist (itoStepSum (fun s ω => W s ω j) t (L m) (c m) ω) 0} =
      {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t (L m) (c m) ω|} := by
    ext ω; simp
  rw [hset]
  calc _ ≤ ENNReal.ofReal (δ / ε ^ 2) +
        P {ω | δ < (∑ k ∈ Finset.range (2 ^ L m), c m k ω ^ 2) *
          ((t / (2 : ℝ≥0) ^ L m : ℝ≥0) : ℝ)} :=
        itoStepSum_local_chebyshev hW x₀ t (L m) j (c m) (hc m) C hCn hε hδpos.le
    _ ≤ e / 2 + e / 2 := by
        rw [hδe]
        refine add_le_add le_rfl (le_trans (measure_mono fun ω hω => ?_) hm)
        simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
        exact hω.le.trans (le_abs_self _)
    _ = e := ENNReal.add_halves e

end StochCalcS2


namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Generic Ito `L²` bound**: `E K_t² ≤ E ∫_0^t G²` for an arbitrary jointly measurable
integrand `G` with `E ∫_0^t G² < ∞` (no continuity, no boundedness). -/
theorem ito_sq_le_gen {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {ℱ : ℝ≥0 → MeasurableSpace Ω}
    (hle : ∀ t, ℱ t ≤ completedBrownianPast P W (fun _ => x₀) t) (hℱ : ∀ t, ℱ t ≤ mΩ)
    {B G K : ℝ≥0 → Ω → ℝ} (hB : ∀ᵐ ω ∂P, ∀ t, B t ω = W t ω j)
    (hK : HasBrownianItoIntegral P ℱ B G K) (t : ℝ≥0)
    (hGj : Measurable (fun q : ℝ × Ω => G q.1.toNNReal q.2))
    (hint : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, G u.toNNReal ω ^ 2) P) :
    MemLp (K t) 2 P ∧
      ∫ ω, K t ω ^ 2 ∂P ≤ ∫ ω, (∫ u in (0 : ℝ)..t.val, G u.toNNReal ω ^ 2) ∂P := by
  obtain ⟨a, ham, haC, hD, hS⟩ := hK.2 t
  have ht0 : (0 : ℝ) ≤ t.val := t.2
  set EI : ℝ := ∫ ω, (∫ u in (0 : ℝ)..t.val, G u.toNNReal ω ^ 2) ∂P with hEI
  have hEI0 : 0 ≤ EI := integral_nonneg fun ω =>
    intervalIntegral.integral_nonneg ht0 fun u _ => sq_nonneg _
  have hamc : ∀ n k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (a n k) := fun n k hk =>
    (ham n k hk).mono (hle _) le_rfl
  have hamm : ∀ n k : ℕ, k < 2 ^ n → Measurable (a n k) := fun n k hk =>
    (ham n k hk).mono (hℱ _) le_rfl
  have hGu : ∀ ω, Measurable fun u : ℝ => G u.toNNReal ω := fun ω =>
    hGj.comp (measurable_id.prodMk measurable_const)
  have hG2 : ∀ ω, IntervalIntegrable (fun u : ℝ => G u.toNNReal ω ^ 2) volume 0 t.val :=
    fun ω => hK.1 t ω
  -- clamped coefficients
  set A : ℕ → ℕ → ℕ → Ω → ℝ := fun R n k ω => clR R (a n k ω) with hAdef
  have hAm : ∀ R n k, k < 2 ^ n → Measurable (A R n k) := fun R n k hk =>
    (clR_continuous R).measurable.comp (hamm n k hk)
  have hAb : ∀ (R : ℕ) n k ω, |A R n k ω| ≤ R := fun R n k ω =>
    abs_clR_le (Nat.cast_nonneg R) _
  have hAint : ∀ R n k, k < 2 ^ n → Integrable (fun ω => A R n k ω ^ 2) P := fun R n k hk =>
    Integrable.of_bound (C := (R : ℝ) ^ 2) ((hAm R n k hk).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hAb R n k ω) 2)
  set e : ℕ → ℕ → Ω → ℝ := fun R n ω => ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (A R n) u ω - clR R (G u.toNNReal ω)) ^ 2 with hedef
  set D : ℕ → Ω → ℝ := fun n ω => ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (a n) u ω - G u.toNNReal ω) ^ 2 with hDdef
  have he0 : ∀ R n ω, 0 ≤ e R n ω := fun R n ω =>
    intervalIntegral.integral_nonneg ht0 fun u _ => sq_nonneg _
  have heD : ∀ (R : ℕ) n ω, e R n ω ≤ D n ω := fun R n ω =>
    P1 t n (a n) (Nat.cast_nonneg R) ω (hGu ω) (hG2 ω)
  have heB : ∀ (R : ℕ) n ω, e R n ω ≤ (2 * (R : ℝ)) ^ 2 * t.val := fun R n ω =>
    P2 t n (a n) (Nat.cast_nonneg R) ω (hGu ω) (hG2 ω)
  have hem : ∀ (R : ℕ) n, Measurable (e R n) := fun R n =>
    meas_intInt (F := fun u ω => (itoStepValue t n (A R n) u ω - clR R (G u.toNNReal ω)) ^ 2)
      (((sv_joint t n (A R n) (hAm R n)).sub
        ((clR_continuous R).measurable.comp hGj)).pow_const 2) ht0
  have heint : ∀ (R : ℕ) n, Integrable (e R n) P := fun R n =>
    Integrable.of_bound (C := (2 * (R : ℝ)) ^ 2 * t.val) (hem R n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (he0 R n ω)]; exact heB R n ω)
  -- (F2) for fixed `R`, `e R n → 0` in measure and in mean
  have heD_tm : ∀ R : ℕ, TendstoInMeasure P (fun n => e R n) atTop (fun _ => 0) := fun R =>
    tendstoInMeasure_zero_of_abs_le one_pos hD hD fun n ω => by
      have h1 := heD R n ω
      have h2 : 0 ≤ D n ω := (he0 R n ω).trans h1
      rw [abs_of_nonneg (he0 R n ω), one_mul, abs_of_nonneg h2]; linarith
  have heL : ∀ R : ℕ, Tendsto (fun n => ∫ ω, e R n ω ∂P) atTop (𝓝 0) := by
    intro R
    set Cb : ℝ := (2 * (R : ℝ)) ^ 2 * t.val with hCb
    have hm2 : ∀ n, MemLp (e R n) 2 P := fun n =>
      MemLp.of_bound (hem R n).aestronglyMeasurable Cb (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (he0 R n ω)]; exact heB R n ω)
    have hK2 : ∀ n, ∫ ω, e R n ω ^ 2 ∂P ≤ Cb ^ 2 := fun n => by
      calc ∫ ω, e R n ω ^ 2 ∂P ≤ ∫ _ω, Cb ^ 2 ∂P := integral_mono_of_nonneg
            (Eventually.of_forall fun ω => sq_nonneg _) (integrable_const _)
            (Eventually.of_forall fun ω => pow_le_pow_left₀ (he0 R n ω) (heB R n ω) 2)
        _ = Cb ^ 2 := by simp
    have h := tendsto_setIntegral_of_sq_le (fun n => e R n) (fun _ => 0) hm2 (Cb ^ 2)
      (sq_nonneg _) hK2 (heD_tm R) Set.univ
    simpa only [Measure.restrict_univ, integral_zero] using h
  -- (F3) the clamping tail `τ R → 0`
  set τ : ℕ → Ω → ℝ := fun R ω => ∫ u in (0 : ℝ)..t.val,
      (G u.toNNReal ω - clR R (G u.toNNReal ω)) ^ 2 with hτdef
  have hτm : ∀ R : ℕ, Measurable (τ R) := fun R =>
    meas_intInt (F := fun u ω => (G u.toNNReal ω - clR R (G u.toNNReal ω)) ^ 2)
      ((hGj.sub ((clR_continuous R).measurable.comp hGj)).pow_const 2) ht0
  have hτ : TendstoInMeasure P τ atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun R => (hτm R).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := t.val) (l := atTop)
      (F := fun (R : ℕ) u => (G u.toNNReal ω - clR R (G u.toNNReal ω)) ^ 2) (f := fun _ => 0)
      (fun u => G u.toNNReal ω ^ 2)
      (Eventually.of_forall fun R => (((hGu ω).sub ((clR_continuous R).measurable.comp
        (hGu ω))).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun R => Eventually.of_forall fun u _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sub_clR_sq_le (Nat.cast_nonneg R) _)
      (hG2 ω)
      (Eventually.of_forall fun u _ => by
        obtain ⟨N, hN⟩ := exists_nat_ge |G u.toNNReal ω|
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with R hR
        rw [clR_eq (hN.trans (Nat.cast_le.2 hR)), sub_self]
        norm_num)
    simpa only [intervalIntegral.integral_zero] using h
  -- diagonal choice of levels
  have hchoose : ∀ R : ℕ, ∃ n, R ≤ n ∧ ∫ ω, e R n ω ∂P ≤ 1 / ((R : ℝ) + 1) := fun R =>
    ((eventually_ge_atTop R).and ((heL R).eventually
      (ge_mem_nhds (by positivity)))).exists
  choose nR hnR1 hnR2 using hchoose
  have hnR : Tendsto nR atTop atTop := tendsto_atTop_mono hnR1 tendsto_id
  set Wj : ℝ≥0 → Ω → ℝ := fun s ω => W s ω j with hWj
  have hBW : ∀ n (c : ℕ → Ω → ℝ), itoStepSum B t n c =ᵐ[P] itoStepSum Wj t n c :=
    fun n c => by
      filter_upwards [hB] with ω hω
      simp only [itoStepSum, hω, hWj]
  set S' : ℕ → Ω → ℝ := fun R => itoStepSum B t (nR R) (A R (nR R)) with hS'def
  -- (F4) the clamped step sums still converge to `K t`
  have hdiff : TendstoInMeasure P (fun R => itoStepSum Wj t (nR R)
      (fun k ω => A R (nR R) k ω - a (nR R) k ω)) atTop (fun _ => 0) := by
    refine stepSum_zero_seq hW x₀ t j nR (fun R k ω => A R (nR R) k ω - a (nR R) k ω)
      (fun R k hk => ((clR_continuous R).measurable.comp (hamc _ k hk)).sub (hamc _ k hk))
      (fun R => ?_) ?_
    · obtain ⟨C, hC⟩ := haC (nR R)
      exact ⟨R + C, fun k hk ω => (abs_sub _ _).trans (add_le_add (hAb R _ k ω) (hC k hk ω))⟩
    · refine tendstoInMeasure_zero_of_abs_le two_pos (hD.comp hnR) hτ fun R ω => ?_
      have hsq := itoStepValue_sq_integral t (nR R)
        (fun k ω => A R (nR R) k ω - a (nR R) k ω) ω
      have hq : (∑ k ∈ Finset.range (2 ^ nR R), (A R (nR R) k ω - a (nR R) k ω) ^ 2) *
          ((t / (2 : ℝ≥0) ^ nR R : ℝ≥0) : ℝ) = ∫ u in (0 : ℝ)..t.val,
            (itoStepValue t (nR R) (A R (nR R)) u ω -
              itoStepValue t (nR R) (a (nR R)) u ω) ^ 2 := by
        rw [← hsq]
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [itoStepValue_sub]
      have hP3 := P3 t (nR R) (a (nR R)) (Nat.cast_nonneg R) ω (hGu ω) (hG2 ω)
      have hD0 : 0 ≤ D (nR R) ω := intervalIntegral.integral_nonneg ht0 fun u _ => sq_nonneg _
      have hτ0 : 0 ≤ τ R ω := intervalIntegral.integral_nonneg ht0 fun u _ => sq_nonneg _
      have hq0 : 0 ≤ (∑ k ∈ Finset.range (2 ^ nR R), (A R (nR R) k ω - a (nR R) k ω) ^ 2) *
          ((t / (2 : ℝ≥0) ^ nR R : ℝ≥0) : ℝ) :=
        mul_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (NNReal.coe_nonneg _)
      show |(∑ k ∈ Finset.range (2 ^ nR R), (A R (nR R) k ω - a (nR R) k ω) ^ 2) *
          ((t / (2 : ℝ≥0) ^ nR R : ℝ≥0) : ℝ)| ≤ 2 * (|D (nR R) ω| + |τ R ω|)
      rw [abs_of_nonneg hq0, abs_of_nonneg hD0, abs_of_nonneg hτ0, hq]
      linarith [hP3]
  have hSn : TendstoInMeasure P (fun R => itoStepSum B t (nR R) (a (nR R))) atTop (K t) :=
    hS.comp hnR
  have hS'conv : TendstoInMeasure P S' atTop (K t) := by
    have h := tendstoInMeasure_add_real hSn hdiff
    simp only [add_zero] at h
    refine h.congr_left (fun R => ?_)
    filter_upwards [hBW (nR R) (fun k ω => A R (nR R) k ω - a (nR R) k ω),
      hBW (nR R) (A R (nR R)), hBW (nR R) (a (nR R))] with ω h1 h2 h3
    have h4 := itoStepSum_sub B t (nR R) (A R (nR R)) (a (nR R)) ω
    simp only [hS'def]
    linarith
  have hS'm : ∀ R, MemLp (S' R) 2 P := fun R =>
    (itoStepSum_memLp hW t (nR R) j (A R (nR R))
      (fun k hk => (hAm R _ k hk).aestronglyMeasurable) R
      (fun k _ ω => hAb R _ k ω)).ae_eq (hBW _ _).symm
  -- (F5) `E S'_R² = E f_R ≤ (1+δ) E I + (1+1/δ)/(R+1)`
  have hS'f : ∀ R, ∫ ω, S' R ω ^ 2 ∂P = ∫ ω, (∫ u in (0 : ℝ)..t.val,
      (itoStepValue t (nR R) (A R (nR R)) u ω) ^ 2) ∂P := by
    intro R
    have h1 : ∫ ω, S' R ω ^ 2 ∂P = ∫ ω, itoStepSum Wj t (nR R) (A R (nR R)) ω ^ 2 ∂P :=
      integral_congr_ae ((hBW _ _).mono fun ω h => by simp only [hS'def]; rw [h])
    rw [h1, itoStepSum_isometry hW x₀ t (nR R) j (A R (nR R))
      (fun k hk => (clR_continuous R).measurable.comp (hamc _ k hk)) R
      (fun k _ ω => hAb R _ k ω)]
    simp only [itoStepValue_sq_integral]
    rw [integral_mul_const, integral_finset_sum _ (fun k hk => hAint R _ k
      (Finset.mem_range.1 hk)), Finset.sum_mul]
  have hfle : ∀ (R : ℕ) {δ : ℝ}, 0 < δ → ∫ ω, S' R ω ^ 2 ∂P ≤
      (1 + δ) * EI + (1 + 1 / δ) * (1 / ((R : ℝ) + 1)) := by
    intro R δ hδ
    rw [hS'f R]
    have hg : Integrable (fun ω => (1 + δ) * (∫ u in (0 : ℝ)..t.val, G u.toNNReal ω ^ 2) +
        (1 + 1 / δ) * e R (nR R) ω) P :=
      (hint.const_mul _).add ((heint R _).const_mul _)
    calc _ ≤ ∫ ω, ((1 + δ) * (∫ u in (0 : ℝ)..t.val, G u.toNNReal ω ^ 2) +
          (1 + 1 / δ) * e R (nR R) ω) ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω =>
            intervalIntegral.integral_nonneg ht0 fun u _ => sq_nonneg _) hg
            (Eventually.of_forall fun ω =>
              P4 t (nR R) (a (nR R)) (Nat.cast_nonneg R) ω (hGu ω) (hG2 ω) hδ)
      _ = (1 + δ) * EI + (1 + 1 / δ) * ∫ ω, e R (nR R) ω ∂P := by
          rw [integral_add (hint.const_mul _) ((heint R _).const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by
          have h1 : 0 ≤ 1 + 1 / δ := by positivity
          have := mul_le_mul_of_nonneg_left (hnR2 R) h1
          linarith
  have hkey : ∀ ε > 0, MemLp (K t) 2 P ∧ ∫ ω, K t ω ^ 2 ∂P ≤ EI + ε := by
    intro ε hε
    set δ : ℝ := ε / (2 * (EI + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    have hδE : δ * EI ≤ ε / 2 := by
      rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    obtain ⟨R0, hR0⟩ := exists_nat_ge ((1 + 1 / δ) * (2 / ε))
    have hbd : ∀ R, R0 ≤ R → ∫ ω, S' R ω ^ 2 ∂P ≤ EI + ε := by
      intro R hR
      have hR1 : (1 + 1 / δ) * (2 / ε) ≤ (R : ℝ) + 1 := by
        have := (Nat.cast_le (α := ℝ)).2 hR; linarith
      have h3 : (1 + 1 / δ) * (1 / ((R : ℝ) + 1)) ≤ ε / 2 := by
        have hx : (1 + 1 / δ) = (ε / 2) * ((1 + 1 / δ) * (2 / ε)) := by field_simp
        rw [mul_one_div, div_le_iff₀ (by positivity), hx]
        exact mul_le_mul_of_nonneg_left hR1 (by positivity)
      have := hfle R hδ
      nlinarith
    have hconv' : TendstoInMeasure P (fun m => S' (m + R0)) atTop (K t) :=
      hS'conv.comp (tendsto_add_atTop_nat R0)
    exact memLp_two_of_tendstoInMeasure (fun m => S' (m + R0)) (K t) (fun m => hS'm _)
      (EI + ε) (by linarith) (fun m => hbd _ (Nat.le_add_left R0 m)) hconv'
  exact ⟨(hkey 1 one_pos).1, le_of_forall_pos_le_add fun ε hε => (hkey ε hε).2⟩

end StochCalcS2


namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma ii_add_sq {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : Measurable f) (hg : Measurable g)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 t)
    (hg2 : IntervalIntegrable (fun u => g u ^ 2) volume 0 t) :
    IntervalIntegrable (fun u => (f u + g u) ^ 2) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at hf2 hg2 ⊢
  refine Integrable.mono' ((hf2.const_mul 2).add (hg2.const_mul 2))
    ((hf.add hg).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show (f u + g u) ^ 2 ≤ 2 * f u ^ 2 + 2 * g u ^ 2
  nlinarith [sq_nonneg (f u - g u)]

lemma sv_add (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n (fun k ω => a k ω + b k ω) u ω =
      itoStepValue t n a u ω + itoStepValue t n b u ω := by
  unfold itoStepValue
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma stepSum_add (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t n (fun k ω => a k ω + b k ω) ω =
      itoStepSum W t n a ω + itoStepSum W t n b ω := by
  unfold itoStepSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Linearity: Ito integrals of `G₁` and `G₂` (u-measurable paths) add. -/
theorem hasIto_add {P : Measure Ω} {ℱ : ℝ≥0 → MeasurableSpace Ω} {B G₁ G₂ K₁ K₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : HasBrownianItoIntegral P ℱ B G₁ K₁) (h₂ : HasBrownianItoIntegral P ℱ B G₂ K₂)
    (hG₁ : ∀ ω, Measurable fun u : ℝ => G₁ u.toNNReal ω)
    (hG₂ : ∀ ω, Measurable fun u : ℝ => G₂ u.toNNReal ω) :
    HasBrownianItoIntegral P ℱ B (fun s ω => G₁ s ω + G₂ s ω) (fun s ω => K₁ s ω + K₂ s ω) := by
  refine ⟨fun t ω => ii_add_sq t.2 (hG₁ ω) (hG₂ ω) (h₁.1 t ω) (h₂.1 t ω), fun t => ?_⟩
  obtain ⟨a, ham, haC, haD, haS⟩ := h₁.2 t
  obtain ⟨b, hbm, hbC, hbD, hbS⟩ := h₂.2 t
  refine ⟨fun n k ω => a n k ω + b n k ω, fun n k hk => (ham n k hk).add (hbm n k hk),
    fun n => ?_, ?_, ?_⟩
  · obtain ⟨C₁, hC₁⟩ := haC n
    obtain ⟨C₂, hC₂⟩ := hbC n
    exact ⟨C₁ + C₂, fun k hk ω => (abs_add_le _ _).trans (add_le_add (hC₁ k hk ω) (hC₂ k hk ω))⟩
  · refine tendstoInMeasure_zero_of_abs_le two_pos haD hbD fun n ω => ?_
    have i1 := ii_sub_sq t.2 (sv_meas_u t n (a n) ω) (hG₁ ω)
      (itoStepValue_sq_intervalIntegrable t n (a n) ω) (h₁.1 t ω)
    have i2 := ii_sub_sq t.2 (sv_meas_u t n (b n) ω) (hG₂ ω)
      (itoStepValue_sq_intervalIntegrable t n (b n) ω) (h₂.1 t ω)
    have hsum : ∫ u in (0 : ℝ)..t.val, (2 * (itoStepValue t n (a n) u ω - G₁ u.toNNReal ω) ^ 2 +
        2 * (itoStepValue t n (b n) u ω - G₂ u.toNNReal ω) ^ 2) =
        2 * (∫ u in (0 : ℝ)..t.val, (itoStepValue t n (a n) u ω - G₁ u.toNNReal ω) ^ 2) +
        2 * ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (b n) u ω - G₂ u.toNNReal ω) ^ 2 := by
      rw [intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hle : ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (fun k ω => a n k ω + b n k ω) u ω -
        (G₁ u.toNNReal ω + G₂ u.toNNReal ω)) ^ 2 ≤
        ∫ u in (0 : ℝ)..t.val, (2 * (itoStepValue t n (a n) u ω - G₁ u.toNNReal ω) ^ 2 +
          2 * (itoStepValue t n (b n) u ω - G₂ u.toNNReal ω) ^ 2) := by
      refine integral_le_of_ae_aux t.2 ((i1.const_mul 2).add (i2.const_mul 2))
        (fun u => sq_nonneg _) fun u _ => ?_
      rw [sv_add]
      nlinarith [sq_nonneg ((itoStepValue t n (a n) u ω - G₁ u.toNNReal ω) -
        (itoStepValue t n (b n) u ω - G₂ u.toNNReal ω))]
    have h0 : 0 ≤ ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (fun k ω => a n k ω + b n k ω) u ω -
        (G₁ u.toNNReal ω + G₂ u.toNNReal ω)) ^ 2 :=
      intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _
    have h1 : 0 ≤ ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (a n) u ω - G₁ u.toNNReal ω) ^ 2 :=
      intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _
    have h2 : 0 ≤ ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (b n) u ω - G₂ u.toNNReal ω) ^ 2 :=
      intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _
    rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonneg h2]
    rw [hsum] at hle
    linarith
  · have h := tendstoInMeasure_add_real haS hbS
    refine h.congr_left (fun n => Eventually.of_forall fun ω => ?_)
    simp only [stepSum_add]

end StochCalcS2


namespace StochCalcS2M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcD2 StochCalcD3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- S1 in the model for a GENERIC continuous adapted integrand `H` with Ito integral `J`
(a.s. continuous on `[0,T]`). -/
theorem S1_model_gen (M : Model p Ω) (hM : M.Standing) {H J : ℝ≥0 → Ω → ℝ}
    (hHF : ∀ s, StronglyMeasurable[M.F s] (H s)) (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral M.P (fun t => M.F t) M.B H J)
    (hJm : ∀ s, AEStronglyMeasurable (J s) M.P)
    (hJcont : ∀ᵐ ω ∂M.P, ContinuousOn (fun u => J u ω) (Set.Icc 0 p.T)) (n' : ℕ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hsT : ∀ i, i ≤ n' → s i ≤ p.T) (θ : ℕ → Ω → ℝ)
    {Cθ : ℝ} (hC : 0 ≤ Cθ) (hθb : ∀ i ω, |θ i ω| ≤ Cθ)
    (hθm : ∀ i, StronglyMeasurable[M.F (s i)] (θ i)) :
    HasBrownianItoIntegral M.P (fun t => M.F t) M.B (fun u ω => thetaS s θ n' u ω * H u ω)
      (fun t ω => ∑ i ∈ Finset.range n',
        θ i ω * (J (min (s (i + 1)) t) ω - J (min (s i) t) ω)) := by
  have := hM.prob
  have hW := isStandardBrownian M hM
  have hJ' : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) H J := hasIto_B M hM hJ
  have hHae : ∀ u, AEStronglyMeasurable (H u) M.P := fun u =>
    ((hHF u).mono (M.F.le u)).aestronglyMeasurable
  have hHcBP : ∀ u, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) u] (H u) :=
    meas_cBP_of_F M hM hHF
  have hJc : ∀ {t : ℝ≥0}, 0 < t → ∀ {r : ℝ≥0}, r ≤ p.T →
      TendstoInMeasure M.P (fun n => J (dyTime t n (rk t r n))) atTop (J r) := by
    intro t ht r hrT
    refine tendstoInMeasure_of_tendsto_ae (fun n => hJm _) ?_
    filter_upwards [hJcont] with ω hω
    have hmem : ∀ n, dyTime t n (rk t r n) ∈ Set.Icc 0 p.T := fun n =>
      ⟨zero_le, (dy_rk_le ht r n).trans hrT⟩
    exact (hω r ⟨zero_le, hrT⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨dy_rk_tendsto ht r, Eventually.of_forall hmem⟩)
  refine ⟨fun t ω => S1_clause1 hHc s θ n' hC hθb t ω, fun t => ?_⟩
  refine ⟨fun N k ω => thetaS s θ n' (dyTime t N k) ω * clampH H N (dyTime t N k) ω,
    ?_, ?_, S1b_tendsto hHae hHc s θ n' hC hθb t, ?_⟩
  · intro N k _
    exact (thetaS_measF (fun t => M.F t) (fun a b h => M.F.mono h) s θ n'
      (fun i => (hθm i).measurable) (dyTime t N k)).mul
      (clampH_measurable (hHF _).measurable (N : ℝ))
  · intro N
    refine ⟨(n' : ℝ) * Cθ * N, fun k _ ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (abs_thetaS_le s θ n' hC hθb _ ω)
      (abs_clampH_le H (Nat.cast_nonneg N) _ ω) (abs_nonneg _) (by positivity)
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht
    · subst ht0
      refine tendstoInMeasure_of_zero _ (fun N ω => ?_) _ (fun ω => ?_)
      · unfold itoStepSum
        simp
      · simp
    · have h := stepSum_simple_tendsto' hW 0 0 hHcBP hHc hJ' ht n' s hs θ hθb
        (fun i hi => hJc ht ((min_le_left _ _).trans (hsT i hi)))
      refine h.congr_left (fun n => ?_)
      filter_upwards [ae_W M hM] with ω hω
      simp only [itoStepSum, fun t => (hω t).1]

/-- `∫ 1 dB = B − B₀`. -/
lemma hasIto_one_B (M : Model p Ω) (hM : M.Standing) :
    HasBrownianItoIntegral M.P (fun t => M.F t) M.B (fun _ _ => 1)
      (fun t ω => M.B t ω - M.B 0 ω) := by
  refine ⟨fun t ω => intervalIntegrable_const, fun t => ⟨fun _ _ _ => 1,
    fun n k _ => measurable_const, fun n => ⟨1, fun k _ ω => by simp⟩, ?_, ?_⟩⟩
  · refine tendstoInMeasure_of_zero _ (fun N ω => ?_) _ (fun ω => rfl)
    refine le_antisymm ?_ (intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _)
    have h := integral_le_of_ae_aux (f := fun u => (itoStepValue t N (fun _ _ => (1 : ℝ)) u ω -
      (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) u.toNNReal ω) ^ 2) (g := fun _ => (0 : ℝ)) t.2
      intervalIntegrable_const (fun u => sq_nonneg _) fun u hu => by
        obtain ⟨k, -, -, -, hval⟩ := stepValue_cell (Ω := Ω) t N hu ω
        simp only [hval (fun _ _ => (1 : ℝ)), sub_self]; norm_num
    simpa using h
  · rw [tendstoInMeasure_real_iff_sub]
    refine tendstoInMeasure_of_zero _ (fun N ω => ?_) _ (fun ω => rfl)
    set f : ℕ → ℝ := fun k => M.B ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ N) ω with hf
    have hterm : ∀ k : ℕ, (fun _ _ => (1 : ℝ)) k ω * (M.B (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ N) ω -
        M.B ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ N) ω) = f (k + 1) - f k := by
      intro k; simp [hf, Nat.cast_succ]
    unfold itoStepSum
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_range_sub]
    have h2 : ((2 ^ N : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ N = t := by
      push_cast; field_simp
    simp only [hf, h2, Nat.cast_zero, zero_mul, zero_div, sub_self]

/-- Joint measurability of a simple-in-time process. -/
lemma thetaS_joint (s : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) (hθ : ∀ i, Measurable (θ i)) :
    Measurable fun q : ℝ × Ω => thetaS s θ n' q.1.toNNReal q.2 := by
  unfold thetaS
  refine Finset.measurable_sum _ fun i _ => ?_
  have hm : Measurable fun q : ℝ × Ω => q.1.toNNReal := measurable_real_toNNReal.comp measurable_fst
  have hs : MeasurableSet {q : ℝ × Ω | s i ≤ q.1.toNNReal ∧ q.1.toNNReal < s (i + 1)} :=
    (measurableSet_le (f := fun _ => s i) (g := fun q : ℝ × Ω => q.1.toNNReal)
      measurable_const hm).inter
      (measurableSet_lt (f := fun q : ℝ × Ω => q.1.toNNReal) (g := fun _ => s (i + 1))
        hm measurable_const)
  exact Measurable.ite hs ((hθ i).comp measurable_snd) measurable_const

lemma Hx_joint (M : Model p Ω) (hM : M.Standing) :
    Measurable fun q : ℝ × Ω => Hx M q.1.toNNReal q.2 :=
  measurable_uncurry_of_continuous_of_measurable
    (fun ω => (Hx_cont M hM ω).comp continuous_real_toNNReal) (fun u => Hx_meas M hM _)

/-- **S2 bound in the degenerate model**: for the simple strategy `(thetaS s θ n', chiS)` and a
grid sum `Σ_k Y_k ΔB_k`, `E(χ_T + Σ Y ΔB)² ≤ E ∫_0^T (θ^s Xσ + Y^s)²`. -/
theorem S2_model (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4)
    (h5 : M.Assumption5) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω)
    (n' : ℕ) (s : ℕ → ℝ≥0) (hs : Monotone s) (hsT : ∀ i, i ≤ n' → s i ≤ p.T)
    (θ : ℕ → Ω → ℝ) {Cθ : ℝ} (hC : 0 ≤ Cθ) (hθb : ∀ i ω, |θ i ω| ≤ Cθ)
    (hθm : ∀ i, StronglyMeasurable[M.F (s i)] (θ i))
    (n : ℕ) (Y : ℕ → Ω → ℝ) {CY : ℝ} (hCY : 0 ≤ CY) (hYb : ∀ k ω, |Y k ω| ≤ CY)
    (hYm : ∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) :
    ∫ ω, (chiS M s θ n' p.T ω +
        ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω) ^ 2 ∂M.P ≤
      ∫ ω, (∫ u in (0 : ℝ)..(p.T : ℝ), (thetaS s θ n' u.toNNReal ω * Hx M u.toNNReal ω +
        thetaS (gr p n) Y n u.toNNReal ω) ^ 2) ∂M.P := by
  have := hM.prob
  have hK1 := S1_model M hM h4 n' s hs hsT θ hC hθb hθm
  have hJcont : ∀ᵐ ω ∂M.P, ContinuousOn (fun u => M.B u ω - M.B 0 ω) (Set.Icc 0 p.T) := by
    filter_upwards [ae_W M hM] with ω hω
    have heq : (fun u => M.B u ω - M.B 0 ω) = fun u => gB M u ω - gB M 0 ω := by
      funext u; rw [← (hω u).1, ← (hω 0).1, W_zero, W_zero]
    rw [heq]; exact ((gB_cont M ω).sub continuous_const).continuousOn
  have hK2 := S1_model_gen M hM (H := fun _ _ => (1 : ℝ)) (J := fun t ω => M.B t ω - M.B 0 ω)
    (fun _ => stronglyMeasurable_const) (fun _ => continuous_const) (hasIto_one_B M hM)
    (fun t => ((B_measurable M hM t).sub (B_measurable M hM 0)).aestronglyMeasurable) hJcont
    n (gr p n) (gr_mono p n) (fun i hi => gr_le_T p hi) Y hCY hYb hYm
  have hG1u : ∀ ω, Measurable fun u : ℝ => thetaS s θ n' u.toNNReal ω * Hx M u.toNNReal ω :=
    fun ω => (thetaS_measurable_u s θ n' ω).mul
      ((Hx_cont M hM ω).comp continuous_real_toNNReal).measurable
  have hG2u : ∀ ω, Measurable fun u : ℝ => thetaS (gr p n) Y n u.toNNReal ω *
      (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) u.toNNReal ω :=
    fun ω => (thetaS_measurable_u (gr p n) Y n ω).mul measurable_const
  have hsum := hasIto_add hK1 hK2 hG1u hG2u
  have hθmm : ∀ i, Measurable (θ i) := fun i => ((hθm i).mono (M.F.le _)).measurable
  have hYmm : ∀ k, Measurable (Y k) := fun k => ((hYm k).mono (M.F.le _)).measurable
  have hGj : Measurable fun q : ℝ × Ω => thetaS s θ n' q.1.toNNReal q.2 *
      Hx M q.1.toNNReal q.2 + thetaS (gr p n) Y n q.1.toNNReal q.2 * 1 :=
    ((thetaS_joint s θ n' hθmm).mul (Hx_joint M hM)).add
      ((thetaS_joint (gr p n) Y n hYmm).mul measurable_const)
  set a1 : ℝ := (n' : ℝ) * Cθ with ha1
  set a2 : ℝ := (n : ℝ) * CY with ha2
  have hT0 : (0 : ℝ) ≤ (p.T : ℝ) := NNReal.coe_nonneg _
  have hint : Integrable (fun ω => ∫ u in (0 : ℝ)..(p.T : ℝ), (thetaS s θ n' u.toNNReal ω *
      Hx M u.toNNReal ω + thetaS (gr p n) Y n u.toNNReal ω * 1) ^ 2) M.P := by
    refine Integrable.mono' (((hint_T M hM h4).const_mul (2 * a1 ^ 2)).add
      (integrable_const (2 * a2 ^ 2 * (p.T : ℝ))))
      (meas_intInt (F := fun u ω => (thetaS s θ n' u.toNNReal ω * Hx M u.toNNReal ω +
        thetaS (gr p n) Y n u.toNNReal ω * 1) ^ 2) (hGj.pow_const 2) hT0).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have hHx2 : IntervalIntegrable (fun u : ℝ => Hx M u.toNNReal ω ^ 2) volume 0 (p.T : ℝ) :=
      (((Hx_cont M hM ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg hT0
      fun u _ => sq_nonneg _)]
    calc _ ≤ ∫ u in (0 : ℝ)..(p.T : ℝ), (2 * a1 ^ 2 * Hx M u.toNNReal ω ^ 2 + 2 * a2 ^ 2) :=
          integral_le_of_ae_aux hT0 ((hHx2.const_mul _).add intervalIntegrable_const)
            (fun u => sq_nonneg _) fun u _ => by
            have hx := abs_thetaS_le s θ n' hC hθb u.toNNReal ω
            have hy := abs_thetaS_le (gr p n) Y n hCY hYb u.toNNReal ω
            set x := thetaS s θ n' u.toNNReal ω
            set y := thetaS (gr p n) Y n u.toNNReal ω
            set h := Hx M u.toNNReal ω
            have hx2 : x ^ 2 ≤ a1 ^ 2 := by
              rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
            have hy2 : y ^ 2 ≤ a2 ^ 2 := by
              rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
            have hxh : x ^ 2 * h ^ 2 ≤ a1 ^ 2 * h ^ 2 :=
              mul_le_mul_of_nonneg_right hx2 (sq_nonneg _)
            nlinarith [sq_nonneg (x * h - y * 1)]
      _ = 2 * a1 ^ 2 * (∫ u in (0 : ℝ)..(p.T : ℝ), Hx M u.toNNReal ω ^ 2) +
            2 * a2 ^ 2 * (p.T : ℝ) := by
          rw [intervalIntegral.integral_add (hHx2.const_mul _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
            sub_zero]
          ring
  have hB : ∀ᵐ ω ∂M.P, ∀ t, M.B t ω = W M t ω 0 :=
    (ae_W M hM).mono fun ω h t => (h t).1.symm
  have h := ito_sq_le_gen (isStandardBrownian M hM) 0 0 (F_le_cBP M hM) (fun t => M.F.le t)
    hB hsum p.T hGj hint
  have heq : (fun ω => (chiS M s θ n' p.T ω +
      ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω) ^ 2) =ᵐ[M.P]
      fun ω => ((∑ i ∈ Finset.range n',
        θ i ω * (M.J (min (s (i + 1)) p.T) ω - M.J (min (s i) p.T) ω)) +
        ∑ k ∈ Finset.range n, Y k ω * ((M.B (min (gr p n (k + 1)) p.T) ω - M.B 0 ω) -
          (M.B (min (gr p n k) p.T) ω - M.B 0 ω))) ^ 2 := by
    filter_upwards [X_eq_J M hM h5 hdeg hQV] with ω hX
    have e1 : chiS M s θ n' p.T ω = ∑ i ∈ Finset.range n',
        θ i ω * (M.J (min (s (i + 1)) p.T) ω - M.J (min (s i) p.T) ω) := by
      unfold chiS; refine Finset.sum_congr rfl fun i _ => ?_
      rw [hX _ (min_le_right _ _), hX _ (min_le_right _ _)]; ring
    have e2 : ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω =
        ∑ k ∈ Finset.range n, Y k ω * ((M.B (min (gr p n (k + 1)) p.T) ω - M.B 0 ω) -
          (M.B (min (gr p n k) p.T) ω - M.B 0 ω)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [min_eq_left (gr_le_T p (show k + 1 ≤ n from hk')), min_eq_left (gr_le_T p hk'.le)]
      simp only [dB]; ring
    rw [e1, e2]
  calc _ = _ := integral_congr_ae heq
    _ ≤ _ := by
      have h2 := h.2
      simp only [mul_one, NNReal.val_eq_coe] at h2
      exact h2

end StochCalcS2M


open MeasureTheory Filter
open scoped NNReal Topology

namespace StochCalcS2X

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS2M StochCalcD2 StochCalcD3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `g_N(x) = x / max(x², 1/(N+1)²)`: bounded by `N+1`, `g_N(x) x ∈ [0,1]`, `= 1` eventually if `x ≠ 0`. -/
noncomputable def gN (N : ℕ) (x : ℝ) : ℝ := x / max (x ^ 2) (1 / ((N : ℝ) + 1) ^ 2)

lemma gN_den_pos (N : ℕ) (x : ℝ) : 0 < max (x ^ 2) (1 / ((N : ℝ) + 1) ^ 2) :=
  lt_max_of_lt_right (by positivity)

lemma gN_continuous (N : ℕ) : Continuous (gN N) :=
  continuous_id.div ((continuous_pow 2).max continuous_const) fun x => (gN_den_pos N x).ne'

lemma abs_gN_le (N : ℕ) (x : ℝ) : |gN N x| ≤ (N : ℝ) + 1 := by
  unfold gN
  rw [abs_div, abs_of_pos (gN_den_pos N x), div_le_iff₀ (gN_den_pos N x)]
  have ha0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rcases le_or_gt (1 / ((N : ℝ) + 1)) |x| with h | h
  · calc |x| = ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) * |x| := by
          rw [mul_one_div_cancel ha0.ne', one_mul]
      _ ≤ ((N : ℝ) + 1) * |x| * |x| := by gcongr
      _ = ((N : ℝ) + 1) * x ^ 2 := by rw [mul_assoc, ← pow_two, sq_abs]
      _ ≤ ((N : ℝ) + 1) * max (x ^ 2) (1 / ((N : ℝ) + 1) ^ 2) := by
          gcongr; exact le_max_left _ _
  · calc |x| ≤ 1 / ((N : ℝ) + 1) := h.le
      _ = ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) ^ 2) := by field_simp
      _ ≤ ((N : ℝ) + 1) * max (x ^ 2) (1 / ((N : ℝ) + 1) ^ 2) := by
          gcongr; exact le_max_right _ _

lemma gN_mul_eq (N : ℕ) (x : ℝ) :
    gN N x * x = x ^ 2 / max (x ^ 2) (1 / ((N : ℝ) + 1) ^ 2) := by
  unfold gN; ring

lemma one_sub_gN_mem (N : ℕ) (x : ℝ) : 0 ≤ 1 - gN N x * x ∧ 1 - gN N x * x ≤ 1 := by
  rw [gN_mul_eq]
  have h0 : 0 ≤ x ^ 2 / max (x ^ 2) (1 / ((N : ℝ) + 1) ^ 2) :=
    div_nonneg (sq_nonneg _) (gN_den_pos N x).le
  have h1 : x ^ 2 / max (x ^ 2) (1 / ((N : ℝ) + 1) ^ 2) ≤ 1 :=
    (div_le_one (gN_den_pos N x)).2 (le_max_left _ _)
  constructor <;> linarith

lemma sq_one_sub_gN_le (N : ℕ) (x : ℝ) : (1 - gN N x * x) ^ 2 ≤ 1 := by
  obtain ⟨h0, h1⟩ := one_sub_gN_mem N x
  nlinarith

lemma tendsto_one_sub_gN {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun N : ℕ => 1 - gN N x * x) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈1 / |x|⌉₊] with N hN
  have hxa : 0 < |x| := abs_pos.2 hx
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : 1 / |x| ≤ (N : ℝ) + 1 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN.trans N.le_succ)
  have h2 : 1 / ((N : ℝ) + 1) ≤ |x| := (one_div_le hxa hN1).1 h1
  have h3 : 1 / ((N : ℝ) + 1) ^ 2 ≤ x ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    rwa [div_pow, one_pow, sq_abs] at this
  rw [gN_mul_eq, max_eq_left h3, div_self (pow_ne_zero 2 hx)]
  ring


lemma thetaS_gr (p : Params) {N : ℕ} (hN : 0 < N) (θ : ℕ → Ω → ℝ) {u : ℝ≥0} (hu : u < p.T)
    (ω : Ω) : thetaS (gr p N) θ N u ω = θ ⌊(u : ℝ) * (N : ℝ) / p.T⌋₊ ω := by
  have hT : (0 : ℝ) < p.T := p.hT
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : (0 : ℝ) < p.T / N := div_pos hT hNr
  have hu' : (u : ℝ) < p.T := hu
  have hx : (u : ℝ) * N / p.T = u / (p.T / N) := by rw [div_div_eq_mul_div]
  have e : ∀ k : ℕ, ((gr p N k : ℝ≥0) : ℝ) = k * ((p.T : ℝ) / N) := fun k => by simp [gr]
  have hcond : ∀ i, (gr p N i ≤ u ∧ u < gr p N (i + 1)) ↔ i = ⌊(u : ℝ) * (N : ℝ) / p.T⌋₊ := by
    intro i
    rw [← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, e, e, eq_comm,
      Nat.floor_eq_iff (by positivity), hx, le_div_iff₀ hd, div_lt_iff₀ hd]
    push_cast
    exact Iff.rfl
  have hjN : ⌊(u : ℝ) * (N : ℝ) / p.T⌋₊ < N := by
    rw [Nat.floor_lt (by positivity), div_lt_iff₀ hT]
    nlinarith [NNReal.coe_nonneg u]
  unfold thetaS
  rw [Finset.sum_eq_single ⌊(u : ℝ) * (N : ℝ) / p.T⌋₊
    (fun i _ hij => if_neg fun h => hij ((hcond i).1 h))
    (fun h => absurd (Finset.mem_range.2 hjN) h), if_pos ((hcond _).2 rfl)]

lemma thetaS_gr_ge (p : Params) (N : ℕ) (θ : ℕ → Ω → ℝ) {u : ℝ≥0} (hu : p.T ≤ u) (ω : Ω) :
    thetaS (gr p N) θ N u ω = 0 := by
  unfold thetaS
  refine Finset.sum_eq_zero fun i hi => if_neg fun h => ?_
  have := gr_le_T p (show i + 1 ≤ N from Finset.mem_range.1 hi)
  exact absurd (h.2.trans_le (this.trans hu)) (lt_irrefl _)

lemma floor_refine {m : ℕ} (hm : 0 < m) (x : ℝ) (n : ℕ) (T : ℝ) :
    ⌊x * ((n * m : ℕ) : ℝ) / T⌋₊ / m = ⌊x * n / T⌋₊ := by
  rw [← Nat.floor_div_natCast]
  congr 1
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  rw [div_div, mul_comm T, ← div_div, ← mul_assoc, mul_div_cancel_right₀ _ hm']

lemma gr_floor_tendsto (p : Params) (N : ℕ → ℕ) (hN : ∀ m, 0 < N m)
    (hNt : Tendsto N atTop atTop) (u : ℝ≥0) :
    Tendsto (fun m => gr p (N m) ⌊(u : ℝ) * (N m : ℝ) / p.T⌋₊) atTop (𝓝 u) := by
  have hT : (0 : ℝ) < p.T := p.hT
  rw [← NNReal.tendsto_coe]
  have hNp : ∀ m, (0 : ℝ) < (N m : ℝ) := fun m => by exact_mod_cast hN m
  have hval : ∀ m, ((gr p (N m) ⌊(u : ℝ) * (N m : ℝ) / p.T⌋₊ : ℝ≥0) : ℝ) =
      (⌊(u : ℝ) * (N m : ℝ) / p.T⌋₊ : ℝ) * ((p.T : ℝ) / N m) := fun m => by simp [gr]
  have hd : ∀ m, (0 : ℝ) < (p.T : ℝ) / N m := fun m => div_pos hT (hNp m)
  have hx : ∀ m, (u : ℝ) * N m / p.T * ((p.T : ℝ) / N m) = u := fun m => by
    field_simp [(hNp m).ne', hT.ne']
  have hup : ∀ m, ((gr p (N m) ⌊(u : ℝ) * (N m : ℝ) / p.T⌋₊ : ℝ≥0) : ℝ) ≤ u := fun m => by
    have h1 := mul_le_mul_of_nonneg_right
      (Nat.floor_le (a := (u : ℝ) * N m / p.T) (by positivity)) (hd m).le
    rw [hx m] at h1
    rw [hval]; exact h1
  have hlow : ∀ m, (u : ℝ) - (p.T : ℝ) / N m ≤
      ((gr p (N m) ⌊(u : ℝ) * (N m : ℝ) / p.T⌋₊ : ℝ≥0) : ℝ) := fun m => by
    rw [hval]
    have h1 := Nat.lt_floor_add_one ((u : ℝ) * N m / p.T)
    have h2 : ((u : ℝ) * N m / p.T - 1) * ((p.T : ℝ) / N m) ≤
        (⌊(u : ℝ) * N m / p.T⌋₊ : ℝ) * ((p.T : ℝ) / N m) :=
      mul_le_mul_of_nonneg_right (by linarith) (hd m).le
    rw [sub_mul, hx m, one_mul] at h2
    exact h2
  have h0 : Tendsto (fun m => (p.T : ℝ) / N m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hNt)
  have hl : Tendsto (fun m => (u : ℝ) - (p.T : ℝ) / N m) atTop (𝓝 (u : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (u : ℝ))).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup


/-- `θ_j = −Y_{j/m} g_N(Xσ(s_j))` on the grid `s_j = gr p (n m) j`. -/
noncomputable def θc (M : Model p Ω) (n m N : ℕ) (Y : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  -(Y (j / m) ω * gN N (Hx M (gr p (n * m) j) ω))

lemma θc_meas (M : Model p Ω) (hM : M.Standing) {n m : ℕ} (hm : 0 < m) (N : ℕ)
    (Y : ℕ → Ω → ℝ) (hYm : ∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) (j : ℕ) :
    StronglyMeasurable[M.F (gr p (n * m) j)] (θc M n m N Y j) := by
  have hle : gr p n (j / m) ≤ gr p (n * m) j := by
    rw [← gr_mul p hm n (j / m)]
    exact gr_mono p (n * m) (Nat.div_mul_le_self j m)
  exact (((hYm (j / m)).mono (M.F.mono hle)).mul
    ((gN_continuous N).comp_stronglyMeasurable (Hx_measF M hM _))).neg

lemma θc_bdd (M : Model p Ω) (n m N : ℕ) (Y : ℕ → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hYb : ∀ k ω, |Y k ω| ≤ C) (j : ℕ) (ω : Ω) :
    |θc M n m N Y j ω| ≤ C * ((N : ℝ) + 1) := by
  unfold θc
  rw [abs_neg, abs_mul]
  exact mul_le_mul (hYb _ ω) (abs_gN_le N _) (abs_nonneg _) hC

lemma integrand_eq (M : Model p Ω) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (N : ℕ)
    (Y : ℕ → Ω → ℝ) (u : ℝ≥0) (ω : Ω) (h : ℝ) :
    thetaS (gr p (n * m)) (θc M n m N Y) (n * m) u ω * h + thetaS (gr p n) Y n u ω =
      thetaS (gr p n) Y n u ω *
        (1 - gN N (Hx M (gr p (n * m) ⌊(u : ℝ) * ((n * m : ℕ) : ℝ) / p.T⌋₊) ω) * h) := by
  by_cases hu : u < p.T
  · rw [thetaS_gr p (Nat.mul_pos hn hm) _ hu, thetaS_gr p hn _ hu]
    unfold θc
    rw [floor_refine hm]
    ring
  · push_neg at hu
    rw [thetaS_gr_ge p _ _ hu, thetaS_gr_ge p _ _ hu]
    ring

/-- The S2 integrand for the grid `n (m+1)`. -/
noncomputable def Fm (M : Model p Ω) (n N : ℕ) (Y : ℕ → Ω → ℝ) (m : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  (thetaS (gr p (n * (m + 1))) (θc M n (m + 1) N Y) (n * (m + 1)) u.toNNReal ω *
    Hx M u.toNNReal ω + thetaS (gr p n) Y n u.toNNReal ω) ^ 2

/-- Its `m → ∞` limit. -/
noncomputable def fN (M : Model p Ω) (n N : ℕ) (Y : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  (thetaS (gr p n) Y n u.toNNReal ω *
    (1 - gN N (Hx M u.toNNReal ω) * Hx M u.toNNReal ω)) ^ 2

lemma Fm_tendsto (M : Model p Ω) (hM : M.Standing) {n : ℕ} (hn : 0 < n) (N : ℕ)
    (Y : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    Tendsto (fun m => Fm M n N Y m u ω) atTop (𝓝 (fN M n N Y u ω)) := by
  have hNt : Tendsto (fun m : ℕ => n * (m + 1)) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_succ m).trans (Nat.le_mul_of_pos_left _ hn))
      tendsto_id
  have hs := gr_floor_tendsto p (fun m => n * (m + 1)) (fun m => Nat.mul_pos hn m.succ_pos) hNt
    u.toNNReal
  have hg : Tendsto (fun m : ℕ => gN N (Hx M (gr p (n * (m + 1))
      ⌊((u.toNNReal : ℝ≥0) : ℝ) * ((n * (m + 1) : ℕ) : ℝ) / p.T⌋₊) ω)) atTop
      (𝓝 (gN N (Hx M u.toNNReal ω))) :=
    ((gN_continuous N).tendsto _).comp (((Hx_cont M hM ω).tendsto _).comp hs)
  have heq : (fun m => Fm M n N Y m u ω) = fun m : ℕ => (thetaS (gr p n) Y n u.toNNReal ω *
      (1 - gN N (Hx M (gr p (n * (m + 1))
        ⌊((u.toNNReal : ℝ≥0) : ℝ) * ((n * (m + 1) : ℕ) : ℝ) / p.T⌋₊) ω) *
        Hx M u.toNNReal ω)) ^ 2 := by
    funext m
    unfold Fm
    rw [integrand_eq M hn m.succ_pos N Y u.toNNReal ω]
  rw [heq]
  exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub (hg.mul tendsto_const_nhds))).pow 2

/-- Pointwise bound `F ≤ 2 a² (N+1)² (Xσ)² + 2 a²` with `a = n C`. -/
lemma Fm_le (M : Model p Ω) {n : ℕ} (hn : 0 < n) (N : ℕ) (Y : ℕ → Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hYb : ∀ k ω, |Y k ω| ≤ C) (m : ℕ) (u : ℝ) (ω : Ω) :
    Fm M n N Y m u ω ≤
      2 * ((n : ℝ) * C) ^ 2 * ((N : ℝ) + 1) ^ 2 * Hx M u.toNNReal ω ^ 2 +
        2 * ((n : ℝ) * C) ^ 2 := by
  unfold Fm
  rw [integrand_eq M hn m.succ_pos N Y u.toNNReal ω]
  have ha := abs_thetaS_le (gr p n) Y n hC hYb u.toNNReal ω
  have hg := abs_gN_le N (Hx M (gr p (n * (m + 1))
    ⌊((u.toNNReal : ℝ≥0) : ℝ) * ((n * (m + 1) : ℕ) : ℝ) / p.T⌋₊) ω)
  set a := thetaS (gr p n) Y n u.toNNReal ω
  set g := gN N (Hx M (gr p (n * (m + 1))
    ⌊((u.toNNReal : ℝ≥0) : ℝ) * ((n * (m + 1) : ℕ) : ℝ) / p.T⌋₊) ω)
  set h := Hx M u.toNNReal ω
  have ha2 : a ^ 2 ≤ ((n : ℝ) * C) ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hg2 : g ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
    rw [← sq_abs g]; exact pow_le_pow_left₀ (abs_nonneg _) hg 2
  have h1 : (1 - g * h) ^ 2 ≤ 2 + 2 * ((N : ℝ) + 1) ^ 2 * h ^ 2 := by
    nlinarith [sq_nonneg (1 + g * h), mul_le_mul_of_nonneg_right hg2 (sq_nonneg h)]
  calc (a * (1 - g * h)) ^ 2 = a ^ 2 * (1 - g * h) ^ 2 := by ring
    _ ≤ ((n : ℝ) * C) ^ 2 * (2 + 2 * ((N : ℝ) + 1) ^ 2 * h ^ 2) :=
        mul_le_mul ha2 h1 (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

lemma fN_le (M : Model p Ω) (n N : ℕ) (Y : ℕ → Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hYb : ∀ k ω, |Y k ω| ≤ C) (u : ℝ) (ω : Ω) :
    fN M n N Y u ω ≤ ((n : ℝ) * C) ^ 2 := by
  unfold fN
  have ha := abs_thetaS_le (gr p n) Y n hC hYb u.toNNReal ω
  have ha2 : (thetaS (gr p n) Y n u.toNNReal ω) ^ 2 ≤ ((n : ℝ) * C) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  rw [mul_pow]
  calc _ ≤ ((n : ℝ) * C) ^ 2 * 1 :=
        mul_le_mul ha2 (sq_one_sub_gN_le N _) (sq_nonneg _) (sq_nonneg _)
    _ = _ := mul_one _

lemma Fm_joint (M : Model p Ω) (hM : M.Standing) {n : ℕ} (N : ℕ) (Y : ℕ → Ω → ℝ)
    (hYm : ∀ k, Measurable (Y k)) (m : ℕ) :
    Measurable fun q : ℝ × Ω => Fm M n N Y m q.1 q.2 := by
  have hθ : ∀ j, Measurable (θc M n (m + 1) N Y j) := fun j =>
    ((hYm _).mul ((gN_continuous N).measurable.comp (Hx_meas M hM _))).neg
  exact (((thetaS_joint _ _ _ hθ).mul (Hx_joint M hM)).add
    (thetaS_joint (gr p n) Y n hYm)).pow_const 2

lemma fN_joint (M : Model p Ω) (hM : M.Standing) (n N : ℕ) (Y : ℕ → Ω → ℝ)
    (hYm : ∀ k, Measurable (Y k)) :
    Measurable fun q : ℝ × Ω => fN M n N Y q.1 q.2 :=
  ((thetaS_joint (gr p n) Y n hYm).mul (measurable_const.sub
    (((gN_continuous N).measurable.comp (Hx_joint M hM)).mul (Hx_joint M hM)))).pow_const 2



lemma inner_m_tendsto (M : Model p Ω) (hM : M.Standing) {n : ℕ} (hn : 0 < n) (N : ℕ)
    (Y : ℕ → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C) (hYb : ∀ k ω, |Y k ω| ≤ C) (ω : Ω) :
    Tendsto (fun m => ∫ u in (0 : ℝ)..(p.T : ℝ), Fm M n N Y m u ω) atTop
      (𝓝 (∫ u in (0 : ℝ)..(p.T : ℝ), fN M n N Y u ω)) := by
  have hHu : Continuous fun u : ℝ => Hx M u.toNNReal ω :=
    (Hx_cont M hM ω).comp continuous_real_toNNReal
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => 2 * ((n : ℝ) * C) ^ 2 * ((N : ℝ) + 1) ^ 2 * Hx M u.toNNReal ω ^ 2 +
      2 * ((n : ℝ) * C) ^ 2)
    (Eventually.of_forall fun m => ?_)
    (Eventually.of_forall fun m => Eventually.of_forall fun u _ => ?_) ?_
    (Eventually.of_forall fun u _ => Fm_tendsto M hM hn N Y u ω)
  · exact ((((thetaS_measurable_u _ _ _ ω).mul hHu.measurable).add
      (thetaS_measurable_u _ _ _ ω)).pow_const 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by unfold Fm; positivity)]
    exact Fm_le M hn N Y hC hYb m u ω
  · exact ((continuous_const.mul (hHu.pow 2)).add continuous_const).intervalIntegrable _ _

lemma outer_m_tendsto (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) {n : ℕ}
    (hn : 0 < n) (N : ℕ) (Y : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Y k)) {C : ℝ} (hC : 0 ≤ C)
    (hYb : ∀ k ω, |Y k ω| ≤ C) :
    Tendsto (fun m => ∫ ω, (∫ u in (0 : ℝ)..(p.T : ℝ), Fm M n N Y m u ω) ∂M.P) atTop
      (𝓝 (∫ ω, (∫ u in (0 : ℝ)..(p.T : ℝ), fN M n N Y u ω) ∂M.P)) := by
  have := hM.prob
  have hT0 : (0 : ℝ) ≤ (p.T : ℝ) := NNReal.coe_nonneg _
  refine tendsto_integral_of_dominated_convergence
    (fun ω => 2 * ((n : ℝ) * C) ^ 2 * ((N : ℝ) + 1) ^ 2 *
      (∫ u in (0 : ℝ)..(p.T : ℝ), Hx M u.toNNReal ω ^ 2) + 2 * ((n : ℝ) * C) ^ 2 * (p.T : ℝ))
    (fun m => (meas_intInt (Fm_joint M hM N Y hYm m) hT0).aestronglyMeasurable)
    (((hint_T M hM h4).const_mul _).add (integrable_const _))
    (fun m => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => inner_m_tendsto M hM hn N Y hC hYb ω)
  have hHx2 : IntervalIntegrable (fun u : ℝ => Hx M u.toNNReal ω ^ 2) volume 0 (p.T : ℝ) :=
    (((Hx_cont M hM ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg hT0
    fun u _ => by unfold Fm; positivity)]
  calc _ ≤ ∫ u in (0 : ℝ)..(p.T : ℝ), (2 * ((n : ℝ) * C) ^ 2 * ((N : ℝ) + 1) ^ 2 *
          Hx M u.toNNReal ω ^ 2 + 2 * ((n : ℝ) * C) ^ 2) :=
        integral_le_of_ae_aux hT0 ((hHx2.const_mul _).add intervalIntegrable_const)
          (fun u => by unfold Fm; positivity) fun u _ => Fm_le M hn N Y hC hYb m u ω
    _ = _ := by
        rw [intervalIntegral.integral_add (hHx2.const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
          sub_zero]
        ring

lemma N_tendsto (M : Model p Ω) (hM : M.Standing) {n : ℕ} (Y : ℕ → Ω → ℝ)
    (hYm : ∀ k, Measurable (Y k)) {C : ℝ} (hC : 0 ≤ C) (hYb : ∀ k ω, |Y k ω| ≤ C)
    (hS3 : ∀ᵐ ω ∂M.P, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) p.T → Hx M u.toNNReal ω ≠ 0) :
    Tendsto (fun N : ℕ => ∫ ω, (∫ u in (0 : ℝ)..(p.T : ℝ), fN M n N Y u ω) ∂M.P) atTop
      (𝓝 0) := by
  have := hM.prob
  have hT0 : (0 : ℝ) ≤ (p.T : ℝ) := NNReal.coe_nonneg _
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _ω, (0 : ℝ) ∂M.P) by simp]
  refine tendsto_integral_of_dominated_convergence (fun _ => ((n : ℝ) * C) ^ 2 * (p.T : ℝ))
    (fun N => (meas_intInt (fN_joint M hM n N Y hYm) hT0).aestronglyMeasurable)
    (integrable_const _) (fun N => Eventually.of_forall fun ω => ?_) (hS3.mono fun ω hω => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg hT0
      fun u _ => by unfold fN; positivity)]
    calc _ ≤ ∫ u in (0 : ℝ)..(p.T : ℝ), ((n : ℝ) * C) ^ 2 :=
          integral_le_of_ae_aux hT0 intervalIntegrable_const (fun u => by unfold fN; positivity)
            fun u _ => fN_le M n N Y hC hYb u ω
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
  · have hHu : Continuous fun u : ℝ => Hx M u.toNNReal ω :=
      (Hx_cont M hM ω).comp continuous_real_toNNReal
    rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _u in (0 : ℝ)..(p.T : ℝ), (0 : ℝ)) by simp]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ((n : ℝ) * C) ^ 2) (Eventually.of_forall fun N => ?_)
      (Eventually.of_forall fun N => Eventually.of_forall fun u _ => ?_)
      intervalIntegrable_const ?_
    · exact (((thetaS_measurable_u (gr p n) Y n ω).mul (measurable_const.sub
        (((gN_continuous N).measurable.comp hHu.measurable).mul hHu.measurable))).pow_const
          2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by unfold fN; positivity)]
      exact fN_le M n N Y hC hYb u ω
    · filter_upwards [hω] with u hu hmem
      rw [Set.uIoc_of_le hT0] at hmem
      have h0 := ((tendsto_const_nhds (x := thetaS (gr p n) Y n u.toNNReal ω)).mul
        (tendsto_one_sub_gN (hu hmem))).pow 2
      rw [mul_zero, zero_pow two_ne_zero] at h0
      exact h0

/-- **hXS from S3** (`Xσ ≠ 0` for a.e. `(u, ω)` on `(0,T]`): the exact `hXS` hypothesis of
`StochCalcD3.dens_of_rep`. -/
theorem hXS_of_S3 (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4)
    (h5 : M.Assumption5) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (hQV : QVStatement Ω)
    (hS3 : ∀ᵐ ω ∂M.P, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) p.T → Hx M u.toNNReal ω ≠ 0) :
    ∀ n : ℕ, 0 < n → ∀ (Y : ℕ → Ω → ℝ) (C : ℝ),
      (∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) → (∀ k ω, |Y k ω| ≤ C) →
      ∀ η : ℝ, 0 < η → ∃ θχ ∈ M.AX, ∃ m : ℕ, 0 < m ∧
      ∫ ω, (θχ.2 p.T ω + ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω) ^ 2
        ∂M.P ≤ η := by
  intro n hn Y C hYm hYb η hη
  have hC : 0 ≤ |C| := abs_nonneg C
  have hYb' : ∀ k ω, |Y k ω| ≤ |C| := fun k ω => (hYb k ω).trans (le_abs_self C)
  have hYmm : ∀ k, Measurable (Y k) := fun k => ((hYm k).mono (M.F.le _)).measurable
  obtain ⟨N, hN⟩ :=
    ((N_tendsto M hM (n := n) Y hYmm hC hYb' hS3).eventually (gt_mem_nhds hη)).exists
  obtain ⟨m, hm⟩ :=
    ((outer_m_tendsto M hM h4 hn N Y hYmm hC hYb').eventually (gt_mem_nhds hN)).exists
  have hsT : ∀ i, i ≤ n * (m + 1) → gr p (n * (m + 1)) i ≤ p.T := fun i hi => gr_le_T p hi
  have hCθ : 0 ≤ |C| * ((N : ℝ) + 1) := by positivity
  refine ⟨_, simple_mem_AX M hM h4 h5 hdeg hQV (n * (m + 1)) (gr p (n * (m + 1)))
    (gr_mono p _) hsT (θc M n (m + 1) N Y) hCθ (θc_bdd M n (m + 1) N Y hC hYb')
    (θc_meas M hM m.succ_pos N Y hYm), 1, one_pos, ?_⟩
  exact (S2_model M hM h4 h5 hdeg hQV (n * (m + 1)) (gr p (n * (m + 1))) (gr_mono p _) hsT
    (θc M n (m + 1) N Y) hCθ (θc_bdd M n (m + 1) N Y hC hYb')
    (θc_meas M hM m.succ_pos N Y hYm) n Y hC hYb' hYm).trans hm.le

end StochCalcS2X


open MeasureTheory Filter
open scoped NNReal Topology ENNReal

namespace StochCalcS3

open EthierKurtz ItoLib StochCalcTC StochCalcS2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS3


namespace StochCalcS3M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS2M StochCalcS3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS3M


namespace StochCalcFe

open Real

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end line

end StochCalcFe


namespace StochCalcS3c

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS2M StochCalcS3 StochCalcS3M StochCalcFe

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS3c


namespace StochCalcDegFinal

open HedgePSNV StochCalcD1aW StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `QVStatement` from the Ito library's quadratic-variation limit (`B = 1`, `j = j'`). -/
theorem qv_holds (Ω : Type*) [MeasurableSpace Ω] : QVStatement Ω := by
  intro d P W hW x₀ j t H J hHm hHc hJ
  have h := ItoLib.qvJ_tendsto hW x₀ j j t (B := fun _ _ => (1 : ℝ))
    (fun _ => measurable_const) (fun _ => continuous_const) hHm hHc hHm hHc hJ hJ
  simp only [eq_self_iff_true, if_true] at h
  have e1 : (fun n ω => ∑ k ∈ Finset.range (2 ^ n),
      (J ((((k + 1 : ℕ) : ℝ≥0)) * t / 2 ^ n) ω - J (((k : ℕ) : ℝ≥0) * t / 2 ^ n) ω) ^ 2) =
      (fun n ω => ∑ k ∈ Finset.range (2 ^ n), (fun _ _ => (1 : ℝ)) (ItoLib.dyTime t n k) ω *
        ((J (ItoLib.dyTime t n (k + 1)) ω - J (ItoLib.dyTime t n k) ω) *
          (J (ItoLib.dyTime t n (k + 1)) ω - J (ItoLib.dyTime t n k) ω))) := by
    funext n ω
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ItoLib.dyTime]
    ring
  have e2 : (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), H u.toNNReal ω ^ 2) =
      (fun ω => ∫ u in (0 : ℝ)..t.val,
        (fun _ _ => (1 : ℝ)) u.toNNReal ω * H u.toNNReal ω * H u.toNNReal ω) := by
    funext ω
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only
    ring
  rw [e1, e2]
  exact h

end StochCalcDegFinal



end StochCalcP6

open MeasureTheory ProbabilityTheory HedgePSNV
open scoped NNReal ENNReal

theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (hS3 : ∀ᵐ ω ∂M.P, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) p.T →
      M.X u.toNNReal ω * M.σ u.toNNReal ω ≠ 0) :
    ∀ n : ℕ, 0 < n → ∀ (Y : ℕ → Ω → ℝ) (C : ℝ),
      (∀ k, StronglyMeasurable[M.F (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Y k)) → (∀ k ω, |Y k ω| ≤ C) →
      ∀ η : ℝ, 0 < η → ∃ θχ ∈ M.AX,
      ∫ ω, (θχ.2 p.T ω + ∑ k ∈ Finset.range n, Y k ω * (M.B ((((k + 1 : ℕ) : ℝ≥0)) * (p.T / (n : ℝ≥0))) ω - M.B (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω)) ^ 2 ∂M.P ≤ η := by
  intro n hn Y C hY hC η hη
  obtain ⟨θχ, hθ, -, -, hint⟩ := StochCalcP6.StochCalcS2X.hXS_of_S3 M hM h4 h5 hdeg
    (StochCalcP6.StochCalcDegFinal.qv_holds Ω) hS3 n hn Y C hY hC η hη
  exact ⟨θχ, hθ, hint⟩
