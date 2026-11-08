-- Prove2me | solution 1 for HedgePSNV.stopped_simple_strategy_ito
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T18:00:08.27528+00:00
-- url     : https://prove2.me/submissions/86dff69b-66fc-48a5-8b33-da99217085ac

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false

-- ===== slice of Solutions.Sol_pv_1558a108 (Solutions/Sol_pv_1558a108.lean): 90/153 top-level decls kept =====

set_option linter.all false
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











end M7qv

section M7c
variable [MeasurableSpace Ω]



end M7c

section M8a
variable [MeasurableSpace Ω]








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




end M8d

section M8e
variable [MeasurableSpace Ω]






end M8e


section M8f
variable [MeasurableSpace Ω]


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




end M8f2


section M8f3
variable [MeasurableSpace Ω]


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
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib


-- ===== slice of P8c066573M16 (scratch/probe/8c066573_M16.lean): 96/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

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

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma G_le_F (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : M.G t ≤ M.F t := by
  rw [hM.filtG t, hM.filtF t]
  refine sup_le_sup_right (iSup₂_mono fun s _ => ?_) _
  have h : M.B s = Prod.fst ∘ (fun ω => (M.B s ω, M.Bt s ω)) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le









end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}







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



/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/

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


/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/

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

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

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

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




end StochCalcIndep

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcHs

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}


















end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]












end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



















end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein








end StochCalcStein
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6




/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]




variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)



end StochCalcP6S

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]











end StochCalcHedgeDeg

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcD2

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

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
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






















end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

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


/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/

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
    have b1 : (k' : ℝ) < k + 1 := by nlinarith
    have b2 : (k : ℝ) < k' + 1 := by nlinarith
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
      nlinarith [sq_nonneg (2 * (n' : ℝ) * Cθ)]
  have i1 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg (c - h))
  have i2 := mul_le_mul_of_nonneg_right hjump (sq_nonneg h)
  have e0 : (A * c - B * h) ^ 2 ≤ 2 * (A ^ 2 * (c - h) ^ 2) + 2 * ((A - B) ^ 2 * h ^ 2) := by
    nlinarith [sq_nonneg (A * (c - h) - (A - B) * h)]
  nlinarith

end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

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


end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

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

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




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

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



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








end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- Dyadic ceiling index of `x` on the level-`n` grid of `[0,t]`. -/
noncomputable def ck (t x : ℝ≥0) (n : ℕ) : ℕ := ⌈(x : ℝ) / (t : ℝ) * 2 ^ n⌉₊

lemma dy_lt_iff_real {t : ℝ≥0} (ht : 0 < t) (n k : ℕ) (x : ℝ≥0) :
    dyTime t n k < x ↔ (k : ℝ) < (x : ℝ) / t * 2 ^ n := by
  rw [← NNReal.coe_lt_coe, dyTime_real]
  have ht' : (0 : ℝ) < t := ht
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have e : (x : ℝ) / t * 2 ^ n = (x : ℝ) * 2 ^ n / t := by ring
  rw [e, lt_div_iff₀ ht', div_lt_iff₀ h2]

lemma le_dy_iff_real {t : ℝ≥0} (ht : 0 < t) (n k : ℕ) (x : ℝ≥0) :
    x ≤ dyTime t n k ↔ (x : ℝ) / t * 2 ^ n ≤ (k : ℝ) := by
  rw [← not_lt, dy_lt_iff_real ht, not_lt]

lemma le_dy_ck {t : ℝ≥0} (ht : 0 < t) (x : ℝ≥0) (n : ℕ) : x ≤ dyTime t n (ck t x n) :=
  (le_dy_iff_real ht n _ x).2 (Nat.le_ceil _)

lemma ck_le {t x : ℝ≥0} (ht : 0 < t) (hx : x ≤ t) (n : ℕ) : ck t x n ≤ 2 ^ n := by
  unfold ck
  apply Nat.ceil_le.2
  have ht' : (0 : ℝ) < t := ht
  have h1 : (x : ℝ) / t ≤ 1 := (div_le_one ht').2 (by exact_mod_cast hx)
  push_cast
  calc (x : ℝ) / t * 2 ^ n ≤ 1 * 2 ^ n := by gcongr
    _ = 2 ^ n := one_mul _

/-- `t_l < ρ^n` is decided at the level-`n` floor of `t_l`. -/
lemma lt_dy_ck_iff {t : ℝ≥0} (ht : 0 < t) (n m l : ℕ) (x : ℝ≥0) :
    dyTime t (n + m) l < dyTime t n (ck t x n) ↔ dyTime t n (l / 2 ^ m) < x := by
  rw [dyTime_lt_iff' ht, dy_lt_iff_real ht, mul_comm, ← Nat.div_lt_iff_lt_mul (by positivity)]
  unfold ck
  exact Nat.lt_ceil

lemma dy_floor_le {t : ℝ≥0} (ht : 0 < t) (n m l : ℕ) :
    dyTime t n (l / 2 ^ m) ≤ dyTime t (n + m) l := by
  rw [← not_lt, dyTime_lt_iff' ht, not_lt]
  exact Nat.mul_div_le l (2 ^ m)

lemma dy_ck_pred_lt {t : ℝ≥0} (ht : 0 < t) (x : ℝ≥0) (n c : ℕ) (hc : ck t x n = c + 1) :
    dyTime t n c < x := by
  rw [dy_lt_iff_real ht]
  have : c < ck t x n := by omega
  unfold ck at this
  exact Nat.lt_ceil.1 this

/-- `hmid` of `truncSum_tendsto` as a lemma: masked sums up to a dyadic time converge. -/
theorem trunc_dy_tendsto {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) {t : ℝ≥0} (ht : 0 < t) (n k : ℕ) (hkle : k ≤ 2 ^ n) :
    TendstoInMeasure P (fun m => itoStepSum (fun s ω => W s ω j) t (n + m)
      (cMask H t (n + m) 0 (dyTime t n k))) atTop (J (dyTime t n k)) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
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
  · have hlt' : dyTime t (n + m) l < dyTime t n k := (dyTime_lt_iff' ht n m l k).2 hlt
    rw [if_pos ⟨(by positivity), hlt'⟩, if_pos hlt,
      clampH_eq_of_abs_le H (hHb.trans (show (R1 : ℝ) ≤ ((n + m : ℕ) : ℝ) by
        exact_mod_cast (hm.trans (Nat.le_add_left m n)))),
      clampH_eq_of_abs_le H (hHb.trans (show (R1 : ℝ) ≤ ((m : ℕ) : ℝ) by exact_mod_cast hm))]
  · rw [if_neg (fun h => hlt ((dyTime_lt_iff' ht n m l k).1 h.2)), if_neg hlt]

/-- **Truncation consistency at a random cutoff** `ρ ≤ t` (a stopping time of the completed
Brownian past): masked clamped left-point sums converge in probability to `J ρ`. -/
theorem randSum_tendsto {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) {t : ℝ≥0} (ht : 0 < t) (ρ : Ω → ℝ≥0) (hρt : ∀ ω, ρ ω ≤ t)
    (hρ : ∀ u v : ℝ≥0, v ≤ u →
      MeasurableSet[completedBrownianPast P W (fun _ => x₀) u] {ω | ρ ω ≤ v})
    (hJc : TendstoInMeasure P (fun n ω => J (dyTime t n (ck t (ρ ω) n)) ω) atTop
      (fun ω => J (ρ ω) ω)) :
    TendstoInMeasure P (fun N => itoStepSum (fun s ω => W s ω j) t N
      (fun k ω => cMask H t N 0 (ρ ω) k ω)) atTop (fun ω => J (ρ ω) ω) := by
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
  obtain ⟨R0, hR0⟩ := ((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHae hHc t) q hq0).exists)
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
      P {ω | ε' ≤ dist (J (dyTime t n (ck t (ρ ω) n)) ω) (J (ρ ω) ω)} ≤ q :=
    ENNReal.tendsto_nhds_zero.1 ((tendstoInMeasure_iff_dist.1 hJc) ε' hε'0) q hq0
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  -- the finitely many deterministic truncations
  set cN : ℝ≥0∞ := ((2 ^ n + 1 : ℕ) : ℝ≥0∞) with hcN
  have hcN0 : 0 < q / cN := ENNReal.div_pos hq0.ne' (ENNReal.natCast_ne_top _)
  have hev3 : ∀ᶠ m : ℕ in atTop, ∀ i ∈ Finset.range (2 ^ n + 1),
      P {ω | ε' ≤ dist (itoStepSum S t (n + m) (cMask H t (n + m) 0 (dyTime t n i)) ω)
        (J (dyTime t n i) ω)} ≤ q / cN := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hile : i ≤ 2 ^ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact ENNReal.tendsto_nhds_zero.1 ((tendstoInMeasure_iff_dist.1
      (trunc_dy_tendsto hW x₀ j hHm hHc hJ ht n i hile)) ε' hε'0) _ hcN0
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 hev3
  filter_upwards [eventually_ge_atTop (n + m0)] with N hN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right n m0) hN)
  have hm : m0 ≤ m := by omega
  set ρn : Ω → ℝ≥0 := fun ω => dyTime t n (ck t (ρ ω) n) with hρn
  set TA : Ω → ℝ := fun ω => itoStepSum S t (n + m) (cMask H t (n + m) 0 (ρn ω)) ω with hTA
  set cD : ℕ → Ω → ℝ := fun l ω =>
    if ρ ω ≤ dyTime t (n + m) l ∧ dyTime t n (l / 2 ^ m) < ρ ω then
      clampH H ((n + m : ℕ) : ℝ) (dyTime t (n + m) l) ω else 0 with hcD
  set D : Ω → ℝ := itoStepSum S t (n + m) cD with hD
  have hdec : ∀ ω, TA ω =
      itoStepSum S t (n + m) (fun k ω => cMask H t (n + m) 0 (ρ ω) k ω) ω + D ω := by
    intro ω
    simp only [hTA, hD]
    unfold itoStepSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [split_mask H t (n + m) (le_dy_ck ht (ρ ω) n) l ω, add_mul]
    congr 2
    simp only [hcD, cMask, lt_dy_ck_iff ht n m l (ρ ω)]
  -- Lenglart bound for the cells in `[ρ, ρ^n)`
  have hcheb := itoStepSum_local_chebyshev hW x₀ t (n + m) j cD
    (fun l _ => by
      simp only [hcD]
      refine Measurable.ite ?_ (clampH_measurable (hHm _) _) measurable_const
      have h1 := hρ (dyTime t (n + m) l) (dyTime t (n + m) l) le_rfl
      have h2 := hρ (dyTime t (n + m) l) _ (dy_floor_le ht n m l)
      have : {ω | ρ ω ≤ dyTime t (n + m) l ∧ dyTime t n (l / 2 ^ m) < ρ ω} =
          {ω | ρ ω ≤ dyTime t (n + m) l} ∩ {ω | ρ ω ≤ dyTime t n (l / 2 ^ m)}ᶜ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
      rw [this]
      exact h1.inter h2.compl) ((n + m : ℕ) : ℝ)
    (fun l _ ω => by
      simp only [hcD]
      split_ifs
      · exact abs_clampH_le H (Nat.cast_nonneg _) _ ω
      · simp only [abs_zero]; positivity) hε'0 hδ0.le
  have hsmall : {ω | δ < (∑ l ∈ Finset.range (2 ^ (n + m)), cD l ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ)} ⊆ bigSet H t R0 := by
    intro ω hω
    by_contra hωB
    simp only [Set.mem_setOf_eq] at hω
    rcases Nat.eq_zero_or_eq_succ_pred (ck t (ρ ω) n) with hc0 | hc1
    · -- `ρ^n = 0`: no cells
      have hz : ∀ l ∈ Finset.range (2 ^ (n + m)), cD l ω ^ 2 = 0 := by
        intro l _
        simp only [hcD]
        rw [if_neg]
        · simp
        · rintro ⟨h1, h2⟩
          have h3 := (lt_dy_ck_iff ht n m l (ρ ω)).2 h2
          rw [hc0, dyTime_lt_iff' ht, mul_zero] at h3
          exact Nat.not_lt_zero _ h3
      rw [Finset.sum_eq_zero hz, zero_mul] at hω
      linarith
    set c' := (ck t (ρ ω) n).pred with hc'
    have hpred : dyTime t n c' < ρ ω := dy_ck_pred_lt ht (ρ ω) n c' hc1
    have hterm : ∀ l ∈ Finset.range (2 ^ (n + m)), cD l ω ^ 2 ≤
        if l ∈ Finset.Ico (2 ^ m * c') (2 ^ m * (c' + 1)) then ((R0 : ℕ) : ℝ) ^ 2 else 0 := by
      intro l hl
      have hl' : l ≤ 2 ^ (n + m) := (Finset.mem_range.1 hl).le
      simp only [hcD]
      by_cases hc : ρ ω ≤ dyTime t (n + m) l ∧ dyTime t n (l / 2 ^ m) < ρ ω
      · have hmem : l ∈ Finset.Ico (2 ^ m * c') (2 ^ m * (c' + 1)) := by
          rw [Finset.mem_Ico]
          refine ⟨not_lt.1 fun h => ?_, ?_⟩
          · have := (dyTime_lt_iff' ht n m l c').2 h
            exact absurd (lt_of_lt_of_le hpred hc.1) (not_lt.2 this.le)
          · have h3 := (lt_dy_ck_iff ht n m l (ρ ω)).2 hc.2
            rw [hc1, dyTime_lt_iff' ht] at h3
            exact h3
        rw [if_pos hc, if_pos hmem]
        have h1 := (abs_clampH_le_abs H (Nat.cast_nonneg (n + m)) (dyTime t (n + m) l) ω).trans
          (abs_le_of_not_mem_bigSet hωB hl')
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      · rw [if_neg hc]
        split_ifs
        · exact (zero_pow two_ne_zero : (0 : ℝ) ^ 2 = 0).trans_le (sq_nonneg _)
        · exact (zero_pow two_ne_zero : (0 : ℝ) ^ 2 = 0).le
    have hsum : (∑ l ∈ Finset.range (2 ^ (n + m)), cD l ω ^ 2) ≤
        (2 ^ m : ℝ) * ((R0 : ℕ) : ℝ) ^ 2 := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_ite_mem]
      refine (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        fun _ _ _ => by positivity).trans ?_
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have : 2 ^ m * (c' + 1) - 2 ^ m * c' = 2 ^ m := by
        rw [mul_add, mul_one, Nat.add_sub_cancel_left]
      rw [this]; exact le_of_eq (by push_cast; ring)
    have hh : ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ) = (t : ℝ) / (2 ^ n * 2 ^ m) := by
      push_cast; rw [pow_add]
    have hfin : (∑ l ∈ Finset.range (2 ^ (n + m)), cD l ω ^ 2) *
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
  -- the truncation at `ρ^n`: finitely many deterministic cases
  have hTA_sub : {ω | ε' ≤ dist (TA ω) (J (ρn ω) ω)} ⊆ ⋃ i ∈ Finset.range (2 ^ n + 1),
      {ω | ε' ≤ dist (itoStepSum S t (n + m) (cMask H t (n + m) 0 (dyTime t n i)) ω)
        (J (dyTime t n i) ω)} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨ck t (ρ ω) n, Finset.mem_range.2 (Nat.lt_succ_of_le (ck_le ht (hρt ω) n)), hω⟩
  have hTA_le : P {ω | ε' ≤ dist (TA ω) (J (ρn ω) ω)} ≤ q := by
    refine (measure_mono hTA_sub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun i hi => hm0 m hm i hi).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact ENNReal.mul_div_le
  have hsub : {ω | ε ≤ dist (itoStepSum S t (n + m) (fun k ω => cMask H t (n + m) 0 (ρ ω) k ω) ω)
      (J (ρ ω) ω)} ⊆ ({ω | ε' ≤ |D ω|} ∪ {ω | ε' ≤ dist (TA ω) (J (ρn ω) ω)}) ∪
        {ω | ε' ≤ dist (J (ρn ω) ω) (J (ρ ω) ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq] at hω ⊢
    by_contra hc
    push_neg at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h0 := hdec ω
    have h4a := abs_add_le ((TA ω - J (ρn ω) ω) - D ω) (J (ρn ω) ω - J (ρ ω) ω)
    have h4b : |(TA ω - J (ρn ω) ω) - D ω| ≤ |TA ω - J (ρn ω) ω| + |D ω| := by
      have := abs_add_le (TA ω - J (ρn ω) ω) (-D ω)
      rwa [abs_neg, ← sub_eq_add_neg] at this
    have h4 : |(TA ω - J (ρn ω) ω) - D ω + (J (ρn ω) ω - J (ρ ω) ω)| ≤
        |TA ω - J (ρn ω) ω| + |D ω| + |J (ρn ω) ω - J (ρ ω) ω| := by linarith
    have h5 : itoStepSum S t (n + m) (fun k ω => cMask H t (n + m) 0 (ρ ω) k ω) ω - J (ρ ω) ω =
        (TA ω - J (ρn ω) ω) - D ω + (J (ρn ω) ω - J (ρ ω) ω) := by rw [h0]; ring
    rw [← h5] at h4
    linarith
  calc P {ω | ε ≤ dist (itoStepSum S t (n + m) (fun k ω => cMask H t (n + m) 0 (ρ ω) k ω) ω)
        (J (ρ ω) ω)}
      ≤ P (({ω | ε' ≤ |D ω|} ∪ {ω | ε' ≤ dist (TA ω) (J (ρn ω) ω)}) ∪
        {ω | ε' ≤ dist (J (ρn ω) ω) (J (ρ ω) ω)}) := measure_mono hsub
    _ ≤ P {ω | ε' ≤ |D ω|} + P {ω | ε' ≤ dist (TA ω) (J (ρn ω) ω)} +
        P {ω | ε' ≤ dist (J (ρn ω) ω) (J (ρ ω) ω)} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (q + q) + q + q := add_le_add (add_le_add hD_le hTA_le) hn2
    _ = e := hqq

end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

theorem S1b_tendsto_rand {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (hHc : ∀ ω, Continuous fun s => H s ω)
    (s : Ω → ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (n' : ℕ) {Cθ : ℝ} (hC : 0 ≤ Cθ)
    (hθb : ∀ i ω, |θ i ω| ≤ Cθ) (t : ℝ≥0) :
    TendstoInMeasure P (fun (N : ℕ) ω => ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t N (fun k ω => thetaS (s ω) θ n' (dyTime t N k) ω *
        clampH H N (dyTime t N k) ω) u ω - thetaS (s ω) θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2)
      atTop (fun _ => 0) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht
  · subst ht0
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have : ∀ N : ℕ, {ω : Ω | ε ≤ dist (∫ u in (0 : ℝ)..((0 : ℝ≥0) : ℝ),
      (itoStepValue 0 N (fun k ω => thetaS (s ω) θ n' (dyTime 0 N k) ω *
        clampH H N (dyTime 0 N k) ω) u ω - thetaS (s ω) θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2)
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
      (itoStepValue t N (fun k ω => thetaS (s ω) θ n' (dyTime t N k) ω *
        clampH H N (dyTime t N k) ω) u ω - thetaS (s ω) θ n' u.toNNReal ω * H u.toNNReal ω) ^ 2) 0}
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
            (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u) volume 0 t.val := by
          have h := IntervalIntegrable.sum (Finset.range (n' + 1)) fun l _ =>
            intervalIntegrable_indicator_Ico_const t.val ((s ω l : ℝ))
              ((s ω l : ℝ) + (t : ℝ) / 2 ^ N) 1 htr.le
          rw [Finset.sum_fn] at h
          exact h
        have h2i : IntervalIntegrable (fun u => c2 * (R : ℝ) ^ 2 * ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u) volume 0 t.val := hsi.const_mul _
        have hpt : ∀ u ∈ Set.Ioc (0 : ℝ) t.val,
            (itoStepValue t N (fun k ω => thetaS (s ω) θ n' (dyTime t N k) ω *
              clampH H N (dyTime t N k) ω) u ω - thetaS (s ω) θ n' u.toNNReal ω *
                H u.toNNReal ω) ^ 2 ≤ (fun u => K1 *
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2) u +
              (fun u => c2 * (R : ℝ) ^ 2 * ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u) u := by
          intro u hu
          have hp : (itoStepValue t N (fun k ω => thetaS (s ω) θ n' (dyTime t N k) ω *
              clampH H N (dyTime t N k) ω) u ω - thetaS (s ω) θ n' u.toNNReal ω *
                H u.toNNReal ω) ^ 2 ≤ 2 * ((n' : ℝ) * Cθ) ^ 2 *
              (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2 +
              2 * (2 * (n' : ℝ) * Cθ) ^ 2 * H u.toNNReal ω ^ 2 *
              ∑ l ∈ Finset.range (n' + 1), (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
                (fun _ => (1 : ℝ)) u := S1b_pointwise H (s ω) θ n' hC hθb t N hu ω
          have hS0 : 0 ≤ ∑ l ∈ Finset.range (n' + 1),
              (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
                (fun _ => (1 : ℝ)) u :=
            Finset.sum_nonneg fun l _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
          have hm : c2 * H u.toNNReal ω ^ 2 * ∑ l ∈ Finset.range (n' + 1),
              (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
                (fun _ => (1 : ℝ)) u ≤ c2 * (R : ℝ) ^ 2 * ∑ l ∈ Finset.range (n' + 1),
              (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
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
            (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator (fun _ => (1 : ℝ)) u =
            c2 * (R : ℝ) ^ 2 * ∫ u in (0 : ℝ)..t.val, ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator (fun _ => (1 : ℝ)) u :=
          intervalIntegral.integral_const_mul _ _
        have hint2 : (∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (fun k ω => thetaS (s ω) θ n' (dyTime t N k) ω *
              clampH H N (dyTime t N k) ω) u ω - thetaS (s ω) θ n' u.toNNReal ω *
                H u.toNNReal ω) ^ 2) ≤ K1 * (∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2) +
            c2 * (R : ℝ) ^ 2 * ∫ u in (0 : ℝ)..t.val, ∑ l ∈ Finset.range (n' + 1),
            (Set.Ico ((s ω l : ℝ)) ((s ω l : ℝ) + (t : ℝ) / 2 ^ N)).indicator
              (fun _ => (1 : ℝ)) u := by
          rw [← hc1, ← hc2', ← hsplit]; exact hint_le
        have hind := integral_sum_indicator_Ico_le t.val ((t : ℝ) / 2 ^ N) htr.le (by positivity)
          (fun l => (s ω l : ℝ)) (n' + 1)
        have hA0 : 0 ≤ ∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (leftCoef (clampH H N) t N) u ω - H u.toNNReal ω) ^ 2 :=
          intervalIntegral.integral_nonneg htr.le (fun u _ => sq_nonneg _)
        rw [abs_of_nonneg hA0] at hcA
        have hF0 : 0 ≤ ∫ u in (0 : ℝ)..t.val,
            (itoStepValue t N (fun k ω => thetaS (s ω) θ n' (dyTime t N k) ω *
              clampH H N (dyTime t N k) ω) u ω - thetaS (s ω) θ n' u.toNNReal ω *
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

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The stopped simple strategy. -/
noncomputable def thetaR (s s' : ℝ≥0) (τ : Ω → ℝ≥0) (Y : Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if min s (τ ω) ≤ u ∧ u < min s' (τ ω) then Y ω else 0

/-- Its (random) jump times. -/
noncomputable def sR (s s' : ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω) : ℕ → ℝ≥0 :=
  fun i => if i = 0 then min s (τ ω) else min s' (τ ω)

lemma thetaR_eq (s s' : ℝ≥0) (τ : Ω → ℝ≥0) (Y : Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    thetaR s s' τ Y u ω = thetaS (sR s s' τ ω) (fun _ => Y) 1 u ω := by
  simp [thetaR, thetaS, sR]

lemma abs_thetaR_le (s s' : ℝ≥0) (τ : Ω → ℝ≥0) (Y : Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hYb : ∀ ω, |Y ω| ≤ C) (u : ℝ≥0) (ω : Ω) : |thetaR s s' τ Y u ω| ≤ C := by
  unfold thetaR
  split_ifs
  · exact hYb ω
  · simpa using hC

lemma thetaR_measF (M : Model p Ω) (s s' : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ u, MeasurableSet[M.F u] {ω | τ ω ≤ u}) (Y : Ω → ℝ)
    (hYm : StronglyMeasurable[M.F s] Y) (v : ℝ≥0) :
    Measurable[M.F v] (fun ω => thetaR s s' τ Y v ω) := by
  unfold thetaR
  by_cases hsv : s ≤ v
  · have e : {ω | min s (τ ω) ≤ v ∧ v < min s' (τ ω)} =
        ({ω | s ≤ v} ∪ {ω | τ ω ≤ v}) ∩ ({ω | v < s'} ∩ {ω | τ ω ≤ v}ᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
        min_le_iff, lt_min_iff, not_le]
    have hset : MeasurableSet[M.F v] {ω | min s (τ ω) ≤ v ∧ v < min s' (τ ω)} := by
      rw [e]
      exact ((MeasurableSet.const _).union (hτ v)).inter
        ((MeasurableSet.const _).inter (hτ v).compl)
    exact Measurable.ite hset (hYm.measurable.mono (M.F.mono hsv) le_rfl) measurable_const
  · have h0 : (fun ω => if min s (τ ω) ≤ v ∧ v < min s' (τ ω) then Y ω else 0) =
        fun _ => 0 := by
      funext ω
      refine if_neg fun h => ?_
      rcases min_le_iff.1 h.1 with h1 | h1
      · exact hsv h1
      · exact absurd (lt_of_lt_of_le h.2 (min_le_right _ _)) (not_lt.2 h1)
    rw [h0]; exact measurable_const

/-- Step sums of the stopped strategy split into two random-cutoff truncations. -/
lemma stepSum_thetaR {t : ℝ≥0} (ht : 0 < t) (S H : ℝ≥0 → Ω → ℝ) (s s' : ℝ≥0) (hss : s ≤ s')
    (τ : Ω → ℝ≥0) (Y : Ω → ℝ) (N : ℕ) (ω : Ω) :
    itoStepSum S t N (fun k ω => thetaR s s' τ Y (dyTime t N k) ω * clampH H N (dyTime t N k) ω) ω =
      Y ω * (itoStepSum S t N (fun k ω => cMask H t N 0 (min (min s' (τ ω)) t) k ω) ω -
        itoStepSum S t N (fun k ω => cMask H t N 0 (min (min s (τ ω)) t) k ω) ω) := by
  simp only [itoStepSum_sub]
  unfold itoStepSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 2 ^ N := Finset.mem_range.1 hk
  beta_reduce
  rw [mask_min H N ht _ hk', mask_min H N ht _ hk']
  unfold thetaR cMask
  have hx0 : (0 : ℝ≥0) ≤ dyTime t N k := zero_le
  have hmm : min s (τ ω) ≤ min s' (τ ω) := min_le_min_right _ hss
  by_cases h1 : dyTime t N k < min s (τ ω)
  · have h2 : dyTime t N k < min s' (τ ω) := lt_of_lt_of_le h1 hmm
    rw [if_neg (fun h => absurd h.1 (not_le.2 h1)), if_pos ⟨hx0, h2⟩, if_pos ⟨hx0, h1⟩]
    ring
  · by_cases h2 : dyTime t N k < min s' (τ ω)
    · rw [if_pos ⟨not_lt.1 h1, h2⟩, if_pos ⟨hx0, h2⟩, if_neg (fun h => h1 h.2)]
      ring
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (fun h => h1 h.2)]
      ring

/-- Bounded multiplier times a difference of two in-measure limits. -/
lemma tim_comb {P : Measure Ω} {a b : ℕ → Ω → ℝ} {A B Y : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hY : ∀ ω, |Y ω| ≤ C) (ha : TendstoInMeasure P a atTop A) (hb : TendstoInMeasure P b atTop B) :
    TendstoInMeasure P (fun N ω => Y ω * (a N ω - b N ω)) atTop (fun ω => Y ω * (A ω - B ω)) := by
  rw [tendstoInMeasure_iff_dist] at ha hb ⊢
  intro ε hε
  set ε' : ℝ := ε / (2 * (C + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hsum := (ha ε' hε'0).add (hb ε' hε'0)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    (fun N => ?_)
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq] at hω ⊢
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have e : Y ω * (a N ω - b N ω) - Y ω * (A ω - B ω) = Y ω * ((a N ω - A ω) - (b N ω - B ω)) := by
    ring
  rw [e, abs_mul] at hω
  have h3 : |(a N ω - A ω) - (b N ω - B ω)| ≤ |a N ω - A ω| + |b N ω - B ω| := by
    have := abs_add_le (a N ω - A ω) (-(b N ω - B ω))
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have h4 : |Y ω| * |(a N ω - A ω) - (b N ω - B ω)| ≤ C * (ε' + ε') :=
    mul_le_mul (hY ω) (h3.trans (add_le_add h1.le h2.le)) (abs_nonneg _) hC
  have h5 : C * (ε' + ε') < ε := by
    rw [hε']
    have hC1 : (0 : ℝ) < C + 1 := by linarith
    rw [show C * (ε / (2 * (C + 1)) + ε / (2 * (C + 1))) = C * ε / (C + 1) by field_simp; ring,
      div_lt_iff₀ hC1]
    nlinarith
  linarith


end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma dy_ck_lt {t : ℝ≥0} (ht : 0 < t) (x : ℝ≥0) (n : ℕ) :
    ((dyTime t n (ck t x n) : ℝ≥0) : ℝ) < (x : ℝ) + (t : ℝ) / 2 ^ n := by
  rw [dyTime_real]
  have ht' : (0 : ℝ) < t := ht
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hc : (ck t x n : ℝ) < (x : ℝ) / t * 2 ^ n + 1 := by
    unfold ck; exact Nat.ceil_lt_add_one (by positivity)
  have e : ((x : ℝ) / t * 2 ^ n + 1) * t / 2 ^ n = (x : ℝ) + t / 2 ^ n := by
    field_simp
  calc (ck t x n : ℝ) * t / 2 ^ n < ((x : ℝ) / t * 2 ^ n + 1) * t / 2 ^ n := by gcongr
    _ = (x : ℝ) + t / 2 ^ n := e

lemma tendsto_add_div_pow (a b : ℝ) :
    Tendsto (fun n : ℕ => a + b / 2 ^ n) atTop (nhds a) := by
  have h0 : Tendsto (fun n : ℕ => a + b / 2 ^ n) atTop (nhds (a + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  rwa [add_zero] at h0

lemma dy_ck_tendsto {t : ℝ≥0} (ht : 0 < t) (x : ℝ≥0) :
    Tendsto (fun n => dyTime t n (ck t x n)) atTop (nhds x) := by
  rw [← NNReal.tendsto_coe]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_add_div_pow (x : ℝ) (t : ℝ))
    (fun n => by exact_mod_cast le_dy_ck ht x n) (fun n => (dy_ck_lt ht x n).le)

/-- **O2c**: `J` along dyadic ceilings of a measurable random time `ρ ≤ s' < T` converges
in measure to `J ρ`. -/
theorem hJc_rand (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) {s' : ℝ≥0}
    (hs' : s' < p.T) {t : ℝ≥0} (ht : 0 < t) (ρ : Ω → ℝ≥0) (hρt : ∀ ω, ρ ω ≤ t)
    (hρs : ∀ ω, ρ ω ≤ s') (hρm : ∀ v, MeasurableSet {ω | ρ ω ≤ v}) :
    TendstoInMeasure M.P (fun n ω => M.J (dyTime t n (ck t (ρ ω) n)) ω) atTop
      (fun ω => M.J (ρ ω) ω) := by
  have := hM.prob
  have hρM : Measurable ρ := measurable_of_Iic hρm
  have hev : ∀ᶠ n : ℕ in atTop, (s' : ℝ) + t / 2 ^ n < p.T :=
    (tendsto_add_div_pow (s' : ℝ) (t : ℝ)).eventually (gt_mem_nhds (by exact_mod_cast hs'))
  have hle : ∀ n ω, (s' : ℝ) + t / 2 ^ n < p.T → dyTime t n (ck t (ρ ω) n) ≤ p.T := by
    intro n ω h
    have h1 := dy_ck_lt ht (ρ ω) n
    have h2 : ((ρ ω : ℝ≥0) : ℝ) ≤ s' := by exact_mod_cast hρs ω
    have h3 : ((dyTime t n (ck t (ρ ω) n) : ℝ≥0) : ℝ) ≤ (p.T : ℝ) := by linarith
    exact_mod_cast h3
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl
    (tendstoInMeasure_of_tendsto_ae
      (f := fun n ω => M.J (min (dyTime t n (ck t (ρ ω) n)) p.T) ω) (fun n => ?_) ?_)
  · filter_upwards [hev] with n hn
    exact Eventually.of_forall fun ω => by
      simp only
      rw [min_eq_left (hle n ω hn)]
  · have hck : Measurable fun ω => ck t (ρ ω) n := by
      unfold ck
      exact Nat.measurable_ceil.comp ((hρM.coe_nnreal_real.div_const _).mul_const _)
    have := Finset.aestronglyMeasurable_sum (Finset.range (2 ^ n + 1))
      (fun i _ => (J_memLp M hM h4 (min (dyTime t n i) p.T) (min_le_right _ _)).aestronglyMeasurable.indicator
        (hck (measurableSet_singleton i)))
    convert this using 1
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (ck t (ρ ω) n)]
    · rw [Set.indicator_of_mem]
      simp
    · intro b _ hb
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun h => hb h.symm
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (ck_le ht (hρt ω) n))) h
  · filter_upwards [J_contOn M hM] with ω hω
    have hρT : ρ ω ≤ p.T := (hρs ω).trans hs'.le
    have hlim : Tendsto (fun n => min (dyTime t n (ck t (ρ ω) n)) p.T) atTop (nhds (ρ ω)) := by
      have h := (dy_ck_tendsto ht (ρ ω)).min (tendsto_const_nhds (x := p.T))
      rwa [min_eq_left hρT] at h
    exact (hω (ρ ω) ⟨zero_le, hρT⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => ⟨zero_le, min_le_right _ _⟩⟩)

/-- **O2b+O2c**: the Ito relation of the stopped simple strategy, for `s ≤ s' < T`. -/
theorem S1R_modelT (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (s s' : ℝ≥0)
    (hss : s ≤ s') (hs' : s' < p.T)
    (τ : Ω → ℝ≥0) (hτ : ∀ u, MeasurableSet[M.F u] {ω | τ ω ≤ u}) (Y : Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hYb : ∀ ω, |Y ω| ≤ C) (hYm : StronglyMeasurable[M.F s] Y) :
    HasBrownianItoIntegral M.P (fun t => M.F t) M.B (fun u ω => thetaR s s' τ Y u ω * Hx M u ω)
      (fun t ω => Y ω * (M.J (min (min s' (τ ω)) t) ω - M.J (min (min s (τ ω)) t) ω)) := by
  have := hM.prob
  have hW := isStandardBrownian M hM
  have hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (Hx M) M.J := hasIto_B M hM hM.X_ito
  have hHae : ∀ u, AEStronglyMeasurable (Hx M u) M.P := fun u =>
    (Hx_meas M hM u).aestronglyMeasurable
  refine ⟨fun t ω => ?_, fun t => ?_⟩
  · have e : (fun u : ℝ => (thetaR s s' τ Y u.toNNReal ω * Hx M u.toNNReal ω) ^ 2) =
        fun u : ℝ => (thetaS (sR s s' τ ω) (fun _ => Y) 1 u.toNNReal ω * Hx M u.toNNReal ω) ^ 2 := by
      funext u; rw [thetaR_eq]
    rw [e]
    exact S1_clause1 (Hx_cont M hM) (sR s s' τ ω) (fun _ => Y) 1 hC (fun _ ω => hYb ω) t ω
  refine ⟨fun N k ω => thetaR s s' τ Y (dyTime t N k) ω * clampH (Hx M) N (dyTime t N k) ω,
    ?_, ?_, ?_, ?_⟩
  · intro N k _
    exact (thetaR_measF M s s' τ hτ Y hYm (dyTime t N k)).mul
      (clampH_measurable (Hx_measF M hM _).measurable (N : ℝ))
  · intro N
    refine ⟨C * N, fun k _ ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (abs_thetaR_le s s' τ Y hC hYb _ ω)
      (abs_clampH_le (Hx M) (Nat.cast_nonneg N) _ ω) (abs_nonneg _) hC
  · have e : (fun (N : ℕ) ω => ∫ u in (0 : ℝ)..t.val,
        (itoStepValue t N (fun k ω => thetaR s s' τ Y (dyTime t N k) ω *
          clampH (Hx M) N (dyTime t N k) ω) u ω - thetaR s s' τ Y u.toNNReal ω *
            Hx M u.toNNReal ω) ^ 2) = (fun (N : ℕ) ω => ∫ u in (0 : ℝ)..t.val,
        (itoStepValue t N (fun k ω => thetaS (sR s s' τ ω) (fun _ => Y) 1 (dyTime t N k) ω *
          clampH (Hx M) N (dyTime t N k) ω) u ω - thetaS (sR s s' τ ω) (fun _ => Y) 1
            u.toNNReal ω * Hx M u.toNNReal ω) ^ 2) := by
      funext N ω
      simp only [thetaR_eq]
    rw [e]
    exact S1b_tendsto_rand hHae (Hx_cont M hM) (sR s s' τ) (fun _ => Y) 1 hC
      (fun _ ω => hYb ω) t
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht
    · subst ht0
      refine tendstoInMeasure_of_zero _ (fun N ω => ?_) _ (fun ω => ?_)
      · unfold itoStepSum
        simp
      · simp
    · have hρm : ∀ (b : ℝ≥0), ∀ u v : ℝ≥0, v ≤ u →
          MeasurableSet[M.F u] {ω | min (min b (τ ω)) t ≤ v} := by
        intro b u v hvu
        have e : {ω | min (min b (τ ω)) t ≤ v} =
            ({ω | b ≤ v} ∪ {ω | τ ω ≤ v}) ∪ {ω | t ≤ v} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_union, min_le_iff]
        rw [e]
        exact ((MeasurableSet.const _).union ((M.F.mono hvu) _ (hτ v))).union
          (MeasurableSet.const _)
      have hlim : ∀ b : ℝ≥0, b ≤ s' → TendstoInMeasure M.P (fun N => itoStepSum
          (fun s ω => W M s ω 0) t N
          (fun k ω => cMask (Hx M) t N 0 (min (min b (τ ω)) t) k ω)) atTop
          (fun ω => M.J (min (min b (τ ω)) t) ω) := fun b hb =>
        randSum_tendsto hW 0 0 (Hx_cBP M hM) (Hx_cont M hM) hJ ht
          (fun ω => min (min b (τ ω)) t) (fun ω => min_le_right _ _)
          (fun u v hvu => (F_le_cBP M hM u) _ (hρm b u v hvu))
          (hJc_rand M hM h4 hs' ht _ (fun ω => min_le_right _ _)
            (fun ω => (min_le_left _ _).trans ((min_le_left _ _).trans hb))
            (fun v => M.F.le v _ (hρm b v v le_rfl)))
      refine (tim_comb hC hYb (hlim s' le_rfl) (hlim s hss)).congr_left (fun N => ?_)
      filter_upwards [ae_W M hM] with ω hω
      rw [stepSum_thetaR ht M.B (Hx M) s s' hss τ Y N ω]
      simp only [itoStepSum, fun t => (hω t).1]

end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
































end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/








/-! The clamped approximants as elementary combinations. -/











end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}



end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}




end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

















end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


























end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/


















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}



end Gen






end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






variable {Ic : ℝ≥0 → Ω → ℝ}
















end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω}


end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV







end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge









end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}





end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]


end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of P8c066573M17 (scratch/probe/8c066573_M17.lean): 0/73 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! O7E6 (8c066573 relay 35, O7.6): conclusion of the completeness argument.  Under
`Q2 = (Z_T²/c)·P`, let `g = f/Z_T`.  If `g ⊥_Q2 L∞(G_T)` (`hG`, from `Q2ce` at `t = 0`) and
`g ⊥_Q2 y·ΔB~_cell` for bounded `F_{t_j} ⊔ G_T`-measurable `y` (`hE`, the conclusion of
`StochCalcE5M.E5`), then `E_P[f Z_T ζ e^{i Σ μ_k ΔB~_k}] = 0` for bounded `G_T`-measurable `ζ`
(`StochCalcR1.core` under `Q2`: exponentials of `B~`-grid sums are `L²(Q2)`-limits of constants
plus `F_{t_l} ⊔ G_T`-weighted `B~`-grid sums), hence `f Z_T` is orthogonal to every
`cos/sin ⟪Δ_j, t⟫` (`StochCalcR5.inner_Δ`, `cos (a + b)` split with `a` the `B`-part) and
`StochCalcR2.ae_eq_zero_of_trig` gives `f Z_T = 0`, so `f = 0`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcE6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV Finset
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcE2 StochCalcG4 StochCalcR5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcE6M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! O7HG (8c066573 relay 36): the `hG` input of `StochCalcE6M.E6` from `Q2ce` at `t = 0`.
`F_0` (augmented natural filtration of `(B, B~)` at time `0`) is `P`-trivial since `B_0 = B~_0 = 0`
a.s., so `E_P[f | F_0] = ∫ f = 0`; `Q2ce` at `t = 0` gives `E_Q2[f/Z_T | F_0 ⊔ G_T] = 0`, hence
`∫ f/Z_T · ζ dQ2 = 0` for bounded `G_T`-measurable `ζ`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcHGM

open MeasureTheory ProbabilityTheory Filter HedgePSNV Set
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcZ3
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcHGM

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

/-! O70 support (copied from the accepted cc6d45ce library: StochCalcS2 clR + hasIto_add, StochCalcS3 hasIto_tail,
StochCalcS3M ext_hasIto, StochCalcFe). -/

namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]














end StochCalcS2
namespace StochCalcS3

open EthierKurtz ItoLib StochCalcTC StochCalcS2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcS3
namespace StochCalcS3M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcS3M
namespace StochCalcFe

open Real

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




end line










end StochCalcFe

/-! O7.0 (8c066573 relay 36): `X_t ≠ 0` a.s. in the NON-degenerate model (no `hdeg`, no `QVStatement`):
Ito formula for `f_ε(x) = ½ log(x² + ε)` on `X` frozen at `T` and continued with its drift and
Brownian increments, localized on `σ ≤ Rσ`, `μ ≤ Rμ`; then `μT`-a.e. via Tonelli, and the `hac`
input of `Q2ce`: `a' Xσ + c Xμ = 0 ⇒ a' = -η c`. -/

namespace StochCalcX0

open MeasureTheory ProbabilityTheory Filter Set
open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3 StochCalcS3M StochCalcFe
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




























end StochCalcX0

end StochCalcP6

-- ===== slice of P8c066573M18 (scratch/probe/8c066573_HC.lean): 0/23 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! GQ (8c066573 relay 37): the O7.4 chain for a GENERAL `θ = θB + θ⊥` (relay 37 found that
`Q1model`/`Q2ce` assume `θ` is a pure `B`-integral, but the completeness argument applies them to `f`,
which also has a `B~`-part).  `KshiftG`/`Q1coreG`: `Rep θB a` for the `B`-part only, `hproj` for the
full `θ`, and `E[θ - θB | K_T] = 0`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3


namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcQ2M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! G3/G5 (8c066573 relay 38).  G5: `O6_modelP` = `O6_model` also exporting that `a'` is
predictable (in the closure of the elementaries).  G3: for `θ` in the closure of the elementary
`B~`-integrals, `E[θ | F_t ⊔ G_T] = E[θ | F_t]` (the `B~` increments after `u` are independent of
`F_u ⊔ G_T`). -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcO6M

namespace StochCalcG3

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m1 m2 mG n : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcG3

namespace StochCalcG3M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcKF StochCalcSteinM
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcG3M


namespace StochCalcG4

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]





variable {mF : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcG4


namespace StochCalcG4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcG3M StochCalcG4 StochCalcR1M StochCalcR4 StochCalcR7 StochCalcD2
  StochCalcD3 StochCalcTiltM
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcG4M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! HC (8c066573 relay 38): **M6 hcomp** (completeness) from O3_model, O6_modelP, O70, G4, G3, Z2, Z3,
Q2ceG, E5, hG_glue, E6.  `ContHyp M` (conj 3 of platform theorem 1c98c8e0) is kept as a hypothesis. -/

namespace StochCalcHC

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcO3 StochCalcO3M StochCalcO6M StochCalcG3M StochCalcG4 StochCalcG4M StochCalcKF
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcHC

end StochCalcP6

-- ===== slice of __current__ (scratch/probe/8c066573_K3G.lean): 0/98 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! K2d (relay 3): the finite-grid lower bound under `P^M`, tests `D0 = Z_T - 1`, `D1 = Z_T S`. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK2

/-! K2e (relay 3): the grid weights `Y = a·ĉ_t / max(Z^M_t, ε)` and the bracket bound. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcK2

/-! K2f (relay 3): `ε ↓ 0` in the grid bound; `Z^M_t > 0` `P^M`-a.s. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcK2

/-! K2g (relay 3): `G(u) = E_P[Z_u/Z^M_u δ_u²]`, `G` monotone and bounded. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcK2

/-! K2h (relay 3): Riemann sums and the assembled lower bound K2. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2

/-! K3H (8c066573 relay 11): abstract Hilbert-space glue for the upper bound K3 of HedgePSNV.theorem_1_ii.
E = L²(F_T, P), one = 1, z = Z_T, h = H, A = admissible gains {χ_T}, N = span{Z_T γ ξ_k} (B̃-part of the
dual space).  Completeness `hcomp` (f ⊥ 1, A, N ⇒ f = 0) is the martingale-representation input. -/

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace StochCalcK3H

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]





section Fn

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]



end Fn

end StochCalcK3H

/-! K3M0 (8c066573 relay 11): model-level glue.  `HedgePSNV.theorem_1_ii_upper_bound`'s conclusion from the
obligations M1-M6 of scratch/decomp/8c066573.K3plan.md, stated on `P` (F_T-measurable functions), via
`StochCalcK3H.fn_upper` on `P.trim (F_T ≤ m)`.  Append after K3H.lean (needs Definitions.Def_HedgePSNV_Hedging). -/

namespace StochCalcK3M0

open MeasureTheory ProbabilityTheory HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcK3M0
/-! K3M1 (8c066573 relay 12): the easy obligations of `StochCalcK3M0.K3_of_obl`:
`A_X` contains `0` and is closed under `+` and scalar multiples (linearity of the Ito relation and
of `IsMartingaleOn`), `Z_T`/`H` measurability and `L²`, `E Z_T = 1`, `1 < E Z_T²`, `V0 = E[H Z_T]`,
`E[Z_T χ_T] = 0`.  `K3_of_N` is then K3 from the `N`-class obligations, `hcomp` (M6) and `hbd` (M5).
Append after K3H + K3M0_tail (on top of the K2 dev chain probe/8c066573_K2h.lean). -/

namespace StochCalcK3M1

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]













variable {p : Params}









end StochCalcK3M1
/-! K3M2 (8c066573 relay 12): the class `N` of `Z_T`-weighted `B~`-grid sums
`n = Z_T * Σ_{k<n} Y_k ξ(t_k, t_{k+1})` (uniform grid `t_k = k T / n` of K2, `Y_k` bounded
`F_{t_k}`-measurable) and its obligations in `StochCalcK3M1.K3_of_N`: `L²`, `F_T`-measurability,
`0`, closure under `+` (common refinement `n * n'`) and scalar multiples, orthogonality to the
gains `χ_T` (under `P^M`), to `1` and to `Z_T`.  `K3_of_M56` = K3 from M5 (`hbd`) and M6 (`hcomp`)
for this class.  Append after K3M1_tail. -/

namespace StochCalcK3M2

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


















end StochCalcK3M2
/-! K3M5 (8c066573 relay 13): obligation M5 of `StochCalcK3M2.K3_of_M56`.  For
`f = Z_T * Σ_k Y_k ξ_k` in the grid class `NC`, `(E_P[H f])² ≤ Ψ E_P[f²]` with
`Ψ = ∫_0^T fK` (= the target `∫ E_P[(Z_u/Z^M_u) δ_u²] du`).  Proof: Stein under `P^M` turns
`E_P[H f]` into `Σ (T/n) E^M[a c^M_{t_k} Y_k]`; the tower property turns `E_P[f²]` into
`Σ (T/n) E^M[Z^M_{t_k} Y_k²]`; a weighted AM-GM bound for every `λ > 0` gives Cauchy-Schwarz;
the left Riemann sum of the monotone `fK` is below its integral.  `K3_of_M6` = K3 from M6
(`hcomp`) only.  Append after K3M2_tail. -/

namespace StochCalcK3M5

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2 StochCalcK3M2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcK3M5

/-! K3G (8c066573 relay 39): K3 (upper bound of (21)) from `K3_of_M6` + `hcomp`, with the
continuity hypothesis `ContHyp M` (conjunct 3 of platform theorem 1c98c8e0) kept explicit. -/

namespace StochCalcK3G

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK3G

end StochCalcP6

open MeasureTheory ProbabilityTheory EthierKurtz in
open scoped NNReal in
theorem solution {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (s s' : ℝ≥0)
    (hss : s ≤ s') (hs' : s' < p.T)
    (τ : Ω → ℝ≥0) (hτ : ∀ u, MeasurableSet[M.F u] {ω | τ ω ≤ u}) (Y : Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hYb : ∀ ω, |Y ω| ≤ C) (hYm : StronglyMeasurable[M.F s] Y) :
    HasBrownianItoIntegral M.P (fun t => M.F t) M.B
      (fun u ω => (if min s (τ ω) ≤ u ∧ u < min s' (τ ω) then Y ω else 0) * (M.X u ω * M.σ u ω))
      (fun t ω => Y ω * (M.J (min (min s' (τ ω)) t) ω - M.J (min (min s (τ ω)) t) ω)) := by
  exact StochCalcP6.StochCalcS1R.S1R_modelT M hM h4 s s' hss hs' τ hτ Y hC hYb hYm
