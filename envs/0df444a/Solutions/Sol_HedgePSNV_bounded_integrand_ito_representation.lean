-- Prove2me | solution 1 for HedgePSNV.bounded_integrand_ito_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:25:47.572792+00:00
-- url     : https://prove2.me/submissions/a23ecb4d-4aa4-4d6f-8741-0a8fc0c94e91

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false


-- ===== slice of Solutions.Sol_pv_1558a108 (probe/slice8c/cuts/r_z4m.lean.src/Solutions.Sol_pv_1558a108.lean): 37/153 top-level decls kept =====

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


end M5c


section M6refine



end M6refine


section M6osc










end M6osc


section M6cauchy
variable [MeasurableSpace Ω]


end M6cauchy


section M6limit
variable [MeasurableSpace Ω]



end M6limit


section M6trunc

















end M6trunc

section M6exist
variable [MeasurableSpace Ω]




end M6exist


section M7grid







end M7grid

section M7zero
variable [MeasurableSpace Ω]



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







end M8f2


section M8f3
variable [MeasurableSpace Ω]







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





end M8g5

section M9a
variable [MeasurableSpace Ω]




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


-- ===== slice of P8c066573M16 (probe/slice8c/cuts/r_z4m.lean.src/P8c066573M16.lean): 109/865 top-level decls kept =====

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










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












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

/-- Index set of the "past of coordinate `j`, everything of the others". -/
abbrev PastIdx (d : ℕ) (t₀ : ℝ≥0) (j : Fin d) : Type := {q : ℝ≥0 × Fin d // q.1 ≤ t₀ ∨ q.2 ≠ j}

theorem indep_coord_shift {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) (j : Fin d) :
    IndepFun (fun ω (r : ℝ≥0) => W (t₀ + r) ω j - W t₀ ω j)
      (fun ω (q : PastIdx d t₀ j) => W q.1.1 ω q.1.2) P := by
  have hG := stdBrownian_isGaussianProcess hW
  have hP : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (X := fun (r : ℝ≥0) ω => W (t₀ + r) ω j - W t₀ ω j)
    (Y := fun (q : PastIdx d t₀ j) ω => W q.1.1 ω q.1.2)
  · apply hG.of_isGaussianProcess
    rintro (r | ⟨⟨t, i⟩, hq⟩)
    · exact ⟨{(t₀ + r, j), (t₀, j)},
        { toFun x := x ⟨(t₀ + r, j), by simp⟩ - x ⟨(t₀, j), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(t, i)},
        { toFun x := x ⟨(t, i), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro r; exact ((hm (t₀ + r) j).sub (hm t₀ j)).aemeasurable
  · intro q; exact (hm _ _).aemeasurable
  · rintro r ⟨⟨t, i⟩, hq⟩
    simp only
    rw [covariance_fun_sub_left (stdBrownian_memLp_two hW _ _) (stdBrownian_memLp_two hW _ _)
      (stdBrownian_memLp_two hW _ _), stdBrownian_cov hW, stdBrownian_cov hW]
    by_cases hij : j = i
    · subst hij
      rcases hq with ht | hne
      · have ht' : t ≤ t₀ := ht
        simp only [if_true]
        rw [min_eq_right (ht'.trans (le_add_right le_rfl)), min_eq_right ht', sub_self]
      · exact absurd rfl hne
    · simp [hij]

/-- σ-algebra form: the increments of coordinate `j` after `t₀` are independent of the
a.e.-closure of the past-of-`j`/all-of-the-others σ-algebra. -/
theorem indep_coord_shift_aeClosure {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) (j : Fin d) :
    Indep (aeClosure P (MeasurableSpace.comap
        (fun ω (q : PastIdx d t₀ j) => W q.1.1 ω q.1.2) inferInstance))
      (MeasurableSpace.comap (fun ω (r : ℝ≥0) => W (t₀ + r) ω j - W t₀ ω j) inferInstance) P :=
  indep_aeClosure ((IndepFun_iff_Indep _ _ _).1 (indep_coord_shift hW t₀ j)).symm

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

lemma integrable_exp_mul (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * ξ ω)) P := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) c
  rw [← hξ.map_eq] at h
  exact (integrable_map_measure h.aestronglyMeasurable hm.aemeasurable).1 h









lemma integrable_exp_abs (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * |ξ ω|)) P := by
  refine Integrable.mono' ((integrable_exp_mul hm hξ c).add (integrable_exp_mul hm hξ (-c)))
    (by fun_prop) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 (ξ ω) with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-c * ξ ω)]
  · rw [abs_of_nonpos h]
    have : c * -ξ ω = -c * ξ ω := by ring
    rw [this]; linarith [Real.exp_pos (c * ξ ω)]


/-- The dominating function of the difference quotients. -/
noncomputable def G (ξ : Ω → ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  (|ξ ω| + v) * Real.exp (|ξ ω| + v)


lemma memLp_G (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    MemLp (G ξ v) 2 P := by
  have hmeas : Measurable (G ξ v) := by unfold G; fun_prop
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ?_
  have hint : Integrable (fun ω => 2 * Real.exp (3 * (v : ℝ)) * Real.exp (3 * |ξ ω|)) P :=
    (integrable_exp_abs hm hξ 3).const_mul _
  refine Integrable.mono' hint (by fun_prop) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  set y := |ξ ω| + (v : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hG : G ξ v ω ^ 2 = y ^ 2 * Real.exp (2 * y) := by
    rw [G, ← hy, mul_pow, sq (Real.exp y), ← Real.exp_add, two_mul]
  have he : 2 * Real.exp (3 * (v : ℝ)) * Real.exp (3 * |ξ ω|) = 2 * Real.exp (3 * y) := by
    rw [mul_assoc, ← Real.exp_add, hy]; ring_nf
  rw [hG, he]
  have h3 : Real.exp (3 * y) = Real.exp y * Real.exp (2 * y) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  have hpos := Real.exp_pos (2 * y)
  nlinarith [Real.exp_pos y]


lemma memLp_xi (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) : MemLp ξ 2 P := by
  refine (memLp_G hm hξ).mono hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have h1 : |ξ ω| ≤ |ξ ω| + v := le_add_of_nonneg_right v.2
  have h2 : 1 ≤ Real.exp (|ξ ω| + v) := Real.one_le_exp (by positivity)
  have h3 : 0 ≤ G ξ v ω := by unfold G; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3]
  unfold G
  have h4 : (0 : ℝ) ≤ |ξ ω| + v := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]


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


/-- Its variance. -/
noncomputable def V (u w : ℝ≥0) : ℝ≥0 := nndist (w : ℝ) (u : ℝ)

















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







/-- Independence from `comap f` transfers along an a.e. equality of `f`. -/
lemma indep_comap_congr {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    {P : Measure Ω} (m : MeasurableSpace Ω) {f f' : Ω → β} (hf : f =ᵐ[P] f')
    (h : Indep m (MeasurableSpace.comap f' mβ) P) : Indep m (MeasurableSpace.comap f mβ) P := by
  rw [Indep_iff] at h ⊢
  rintro t1 _ ht1 ⟨S, hS, rfl⟩
  have e : (f ⁻¹' S : Set Ω) =ᵐ[P] f' ⁻¹' S := hf.fun_comp (fun y => y ∈ S)
  rw [measure_congr ((ae_eq_refl t1).inter e), measure_congr e]
  exact h t1 _ ht1 ⟨S, hS, rfl⟩

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

lemma integral_gauss {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    ∫ ω, ξ ω ∂P = 0 := by
  rw [hξ.integral_eq, integral_id_gaussianReal]

lemma integral_sq_gauss {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    ∫ ω, ξ ω ^ 2 ∂P = v := by
  have h := hξ.integral_comp (f := fun x : ℝ => x ^ 2) (continuous_pow 2).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa [integral_id_gaussianReal] using hv


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

/-- `B`-increment. -/
noncomputable def dB (M : Model p Ω) (u w : ℝ≥0) (ω : Ω) : ℝ := M.B w ω - M.B u ω



lemma dB_law (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    HasLaw (dB M u w) (gaussianReal 0 (V u w)) M.P :=
  hM.brownB.hasLaw_sub w u

lemma dB_meas (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) : Measurable (dB M u w) :=
  (B_measurable M hM w).sub (B_measurable M hM u)



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

/-- Past of `B` up to `c`, all of `B~`. -/
noncomputable abbrev YsigB (M : Model p Ω) (c : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (q : PastIdx 2 c 0) => W M q.1.1 ω q.1.2) inferInstance

lemma coordB_meas (M : Model p Ω) (c : ℝ≥0) (q : PastIdx 2 c 0) :
    Measurable[YsigB M c] (fun ω => W M q.1.1 ω q.1.2) := fun S hS =>
  ⟨(fun f : PastIdx 2 c 0 → ℝ => f q) ⁻¹' S, measurable_pi_apply q hS, rfl⟩

lemma pair_aeC0 (M : Model p Ω) (hM : M.Standing) (c s : ℝ≥0) (hs : s ≤ c) :
    MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance ≤
      aeClosure M.P (YsigB M c) := by
  rintro A ⟨S, hS, rfl⟩
  have hq0 : (s, (0 : Fin 2)).1 ≤ c ∨ (s, (0 : Fin 2)).2 ≠ 0 := Or.inl hs
  have hq1 : (s, (1 : Fin 2)).1 ≤ c ∨ (s, (1 : Fin 2)).2 ≠ 0 :=
    Or.inr (show (1 : Fin 2) ≠ 0 by decide)
  have hm : Measurable[YsigB M c] (fun ω => (W M s ω 0, W M s ω 1)) :=
    (coordB_meas M c ⟨(s, 0), hq0⟩).prodMk (coordB_meas M c ⟨(s, 1), hq1⟩)
  refine ⟨(fun ω => (W M s ω 0, W M s ω 1)) ⁻¹' S, hm hS, ?_⟩
  filter_upwards [ae_W M hM] with ω hω
  show ((M.B s ω, M.Bt s ω) ∈ S) = ((W M s ω 0, W M s ω 1) ∈ S)
  rw [(hω s).1, (hω s).2]

lemma null_aeC0 (M : Model p Ω) (c : ℝ≥0) :
    MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ M.P N = 0} ≤
      aeClosure M.P (YsigB M c) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro N ⟨-, hN0⟩
  exact ⟨∅, @MeasurableSet.empty Ω (YsigB M c), ae_eq_empty.2 hN0⟩

lemma F_le0 (M : Model p Ω) (hM : M.Standing) (c : ℝ≥0) :
    M.F c ≤ aeClosure M.P (YsigB M c) := by
  rw [hM.filtF c]
  exact sup_le (iSup₂_le fun s hs => pair_aeC0 M hM c s hs) (null_aeC0 M c)

/-- The `B` increments after `c` are independent of `F_c`. -/
theorem indep_B_incr (M : Model p Ω) (hM : M.Standing) (c : ℝ≥0) :
    Indep (M.F c)
      (MeasurableSpace.comap (fun ω (r : ℝ≥0) => W M (c + r) ω 0 - W M c ω 0) inferInstance)
      M.P :=
  indep_of_indep_of_le_left (indep_coord_shift_aeClosure (isStandardBrownian M hM) c 0)
    (F_le0 M hM c)

lemma dB_ae (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    dB M u w =ᵐ[M.P] fun ω => gB M w ω - gB M u ω := by
  filter_upwards [ae_W M hM] with ω hω
  simp only [dB, ← (hω w).1, ← (hω u).1, W_zero]

lemma indep_dB (M : Model p Ω) (hM : M.Standing) {u w : ℝ≥0} (huw : u ≤ w) :
    Indep (M.F u) (MeasurableSpace.comap (dB M u w) inferInstance) M.P := by
  refine indep_comap_congr _ (dB_ae M hM u w) ?_
  refine indep_of_indep_of_le_right (indep_B_incr M hM u) ?_
  set inc : Ω → ℝ≥0 → ℝ := fun ω r => W M (u + r) ω 0 - W M u ω 0 with hinc
  have heq : (fun ω => gB M w ω - gB M u ω) = (fun f : ℝ≥0 → ℝ => f (w - u)) ∘ inc := by
    funext ω
    simp only [Function.comp, hinc, W_zero, add_tsub_cancel_of_le huw]
  rw [heq]
  exact ((measurable_pi_apply _).comp (comap_measurable inc)).comap_le

lemma B_measF (M : Model p Ω) (hM : M.Standing) {r s : ℝ≥0} (hr : r ≤ s) :
    Measurable[M.F s] (M.B r) := by
  have h : MeasurableSpace.comap (fun ω => (M.B r ω, M.Bt r ω)) inferInstance ≤ M.F s := by
    rw [hM.filtF s]
    exact le_sup_of_le_left (le_iSup₂_of_le r hr le_rfl)
  exact measurable_fst.comp (Measurable.of_comap_le h)













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
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





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











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






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

/-- Increment hypotheses on a real process `W` w.r.t. a family of σ-algebras `m`. -/
structure IncrHyp (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop where
  mono : Monotone m
  le : ∀ t, m t ≤ mΩ
  adapt : ∀ t, Measurable[m t] (W t)
  indep : ∀ u v, u ≤ v →
    Indep (m u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P
  mem2 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P
  mean : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0
  var : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u

variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma dW_meas (hW : IncrHyp m W P) {u v : ℝ≥0} (huv : u ≤ v) :
    Measurable[m v] (fun ω => W v ω - W u ω) :=
  (hW.adapt v).sub ((hW.adapt u).mono (hW.mono huv) le_rfl)

lemma dW_measAmb (hW : IncrHyp m W P) (u v : ℝ≥0) : Measurable (fun ω => W v ω - W u ω) :=
  ((hW.adapt v).mono (hW.le v) le_rfl).sub ((hW.adapt u).mono (hW.le u) le_rfl)

lemma int_mul_dW (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) : ∫ ω, g ω * (W d ω - W c ω) ∂P = 0 := by
  have hind : IndepFun g (fun ω => W d ω - W c ω) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    (dW_measAmb hW c d).aestronglyMeasurable, hW.mean c d hcd, mul_zero]

lemma int_mul_dW_sq (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) :
    ∫ ω, g ω * (W d ω - W c ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * ((d : ℝ) - c) := by
  have hind : IndepFun g (fun ω => (W d ω - W c ω) ^ 2) P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le) ?_
    exact ((comap_measurable (fun ω => W d ω - W c ω)).pow_const 2).comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    ((dW_measAmb hW c d).pow_const 2).aestronglyMeasurable, hW.var c d hcd]

lemma int_mul_dW_dW (hW : IncrHyp m W P) {c x y : ℝ≥0} (hcx : c ≤ x) (hxy : x ≤ y) {g : Ω → ℝ}
    (hg : Measurable[m c] g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * ((W x ω - W c ω) * (W y ω - W c ω)) ∂P = (∫ ω, g ω ∂P) * ((x : ℝ) - c) := by
  have hga : AEStronglyMeasurable g P := (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
  have hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have i1 : Integrable (fun ω => g ω * (W x ω - W c ω) ^ 2) P :=
    (hW.mem2 c x).integrable_sq.bdd_mul hga hgb
  have i2 : Integrable (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W x ω))) P :=
    ((hW.mem2 c x).integrable_mul (hW.mem2 x y)).bdd_mul hga hgb
  have i2' : Integrable (fun ω => g ω * (W x ω - W c ω) * (W y ω - W x ω)) P := by
    simpa only [mul_assoc] using i2
  have e : (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W c ω))) =
      fun ω => g ω * (W x ω - W c ω) ^ 2 + g ω * (W x ω - W c ω) * (W y ω - W x ω) := by
    funext ω; ring
  have hg2 : Measurable[m x] (fun ω => g ω * (W x ω - W c ω)) :=
    (hg.mono (hW.mono hcx) le_rfl).mul (dW_meas hW hcx)
  rw [e, integral_add i1 i2', int_mul_dW_sq hW hcx hg, int_mul_dW hW hxy hg2, add_zero]

/-- Overlap length of `[u,v)` and `[u',v')`. -/
noncomputable def ov (u v u' v' : ℝ≥0) : ℝ := max (min (v : ℝ) v' - max (u : ℝ) u') 0

lemma ov_comm (u v u' v' : ℝ≥0) : ov u v u' v' = ov u' v' u v := by
  unfold ov; rw [min_comm, max_comm (u : ℝ)]

/-- Covariance of two elementary increments (case `u ≤ u'`). -/
lemma cov_le (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    (huu' : u ≤ u') {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  have hYu' : Measurable[m u'] Y := hY.mono (hW.mono huu') le_rfl
  have hYY' : Measurable[m u'] (fun ω => Y ω * Y' ω) := hYu'.mul hY'
  have hbd : ∀ ω, |Y ω * Y' ω| ≤ C * C' := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
  have hu'r : (u : ℝ) ≤ u' := by exact_mod_cast huu'
  rcases le_or_gt v u' with hvu | hu'v
  · have hvu' : (v : ℝ) ≤ u' := by exact_mod_cast hvu
    have hov : ov u v u' v' = 0 := by
      unfold ov
      exact max_eq_right (by linarith [min_le_left (v : ℝ) v', le_max_right (u : ℝ) u'])
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y ω * (W v ω - W u ω) * Y' ω) * (W v' ω - W u' ω) := by
      funext ω; ring
    have hg : Measurable[m u'] (fun ω => Y ω * (W v ω - W u ω) * Y' ω) :=
      (hYu'.mul ((dW_meas hW huv).mono (hW.mono hvu) le_rfl)).mul hY'
    rw [e, int_mul_dW hW hu'v' hg, hov, mul_zero]
  · have hu'v'' : (u' : ℝ) < v := by exact_mod_cast hu'v
    have hu'v1 : u' ≤ v := hu'v.le
    have hga : AEStronglyMeasurable (fun ω => Y ω * Y' ω) P :=
      (hYY'.mono (hW.le u') le_rfl).aestronglyMeasurable
    have hgb : ∀ᵐ ω ∂P, ‖Y ω * Y' ω‖ ≤ C * C' :=
      Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd ω
    have i1 : Integrable (fun ω => Y ω * Y' ω * ((W u' ω - W u ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u u').integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i2 : Integrable (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u' v).integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i1' : Integrable (fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω)) P := by
      simpa only [mul_assoc] using i1
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω) +
          Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω)) := by
      funext ω; ring
    have hg1 : Measurable[m u'] (fun ω => Y ω * Y' ω * (W u' ω - W u ω)) :=
      hYY'.mul (dW_meas hW huu')
    rw [e, integral_add i1' i2, int_mul_dW hW hu'v' hg1, zero_add]
    rcases le_total v v' with hvv | hvv
    · rw [int_mul_dW_dW hW hu'v1 hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v : ℝ) ≤ v' := by exact_mod_cast hvv
      rw [min_eq_left hvv', max_eq_right hu'r, max_eq_left (by linarith)]
    · have e2 : (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) =
          fun ω => Y ω * Y' ω * ((W v' ω - W u' ω) * (W v ω - W u' ω)) := by
        funext ω; ring
      rw [e2, int_mul_dW_dW hW hu'v' hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v' : ℝ) ≤ v := by exact_mod_cast hvv
      have hu'v'r : (u' : ℝ) ≤ v' := by exact_mod_cast hu'v'
      rw [min_eq_right hvv', max_eq_right hu'r, max_eq_left (by linarith)]

lemma cov (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  rcases le_total u u' with h | h
  · exact cov_le hW huv hu'v' h hY hY' hC hC'
  · have := cov_le hW hu'v' huv h hY' hY hC' hC
    have e1 : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y' ω * (W v' ω - W u' ω)) * (Y ω * (W v ω - W u ω)) := by
      funext ω; ring
    have e2 : (fun ω => Y ω * Y' ω) = fun ω => Y' ω * Y ω := by funext ω; ring
    rw [e1, e2, this, ov_comm]

/-- Time indicator of `[u, v)`. -/
noncomputable def ind (u v : ℝ≥0) (r : ℝ) : ℝ := (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) r

lemma ind_mul (u v u' v' : ℝ≥0) (r : ℝ) :
    ind u v r * ind u' v' r =
      (Set.Ico (max (u : ℝ) u') (min (v : ℝ) v')).indicator (fun _ => (1 : ℝ)) r := by
  simp only [ind, Set.indicator_apply, Set.mem_Ico, max_le_iff, lt_min_iff]
  split_ifs <;> simp_all

lemma ind_abs_le (u v : ℝ≥0) (r : ℝ) : |ind u v r| ≤ 1 := by
  unfold ind; rw [Set.indicator_apply]; split_ifs <;> simp

lemma ind_meas (u v : ℝ≥0) : Measurable (ind u v) :=
  (measurable_const.indicator measurableSet_Ico)

/-- The time-space measure `dt|[0,T) ⊗ P`. -/
noncomputable def μT (P : Measure Ω) (T : ℝ≥0) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Ico (0 : ℝ) T)).prod P

instance (T : ℝ≥0) : IsFiniteMeasure (μT P T) := by unfold μT; infer_instance

lemma int_time (T : ℝ≥0) {u v u' v' : ℝ≥0} (hvT : v ≤ T) :
    ∫ r, ind u v r * ind u' v' r ∂(volume.restrict (Set.Ico (0 : ℝ) T)) = ov u v u' v' := by
  unfold ov
  simp_rw [ind_mul]
  have hsub : Set.Ico (max (u : ℝ) u') (min (v : ℝ) v') ⊆ Set.Ico 0 T := fun r hr =>
    ⟨le_trans (le_trans (NNReal.coe_nonneg u) (le_max_left _ _)) hr.1,
      lt_of_lt_of_le hr.2 (le_trans (min_le_left _ _) (by exact_mod_cast hvT))⟩
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 hsub, Real.volume_real_Ico, smul_eq_mul, mul_one]

/-- Elementary adapted processes `Y 1_[u,v)` on `[0,T]`. -/
structure Elem (m : ℝ≥0 → MeasurableSpace Ω) (T : ℝ≥0) where
  u : ℝ≥0
  v : ℝ≥0
  huv : u ≤ v
  hvT : v ≤ T
  Y : Ω → ℝ
  hY : Measurable[m u] Y
  C : ℝ
  hC : ∀ ω, |Y ω| ≤ C

/-- The time-space function of an elementary process. -/
noncomputable def efun {T : ℝ≥0} (i : Elem m T) (z : ℝ × Ω) : ℝ := ind i.u i.v z.1 * i.Y z.2

/-- The elementary stochastic integral. -/
noncomputable def ifun {T : ℝ≥0} (W : ℝ≥0 → Ω → ℝ) (i : Elem m T) (ω : Ω) : ℝ :=
  i.Y ω * (W i.v ω - W i.u ω)

lemma memLp_efun (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i : Elem m T) :
    MemLp (efun i) 2 (μT P T) := by
  have hm : Measurable (efun i) :=
    ((ind_meas i.u i.v).comp measurable_fst).mul ((i.hY.mono (hle i.u) le_rfl).comp measurable_snd)
  refine MemLp.of_bound hm.aestronglyMeasurable i.C (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, efun, abs_mul]
  calc |ind i.u i.v z.1| * |i.Y z.2| ≤ 1 * |i.Y z.2| :=
        mul_le_mul_of_nonneg_right (ind_abs_le _ _ _) (abs_nonneg _)
    _ ≤ i.C := by rw [one_mul]; exact i.hC z.2

lemma memLp_ifun (hW : IncrHyp m W P) {T : ℝ≥0} (i : Elem m T) : MemLp (ifun W i) 2 P := by
  refine ((hW.mem2 i.u i.v).const_mul i.C).of_le
    ((i.hY.mono (hW.le i.u) le_rfl).aestronglyMeasurable.mul (hW.mem2 i.u i.v).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [ifun, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((i.hC ω).trans (le_abs_self _)) (abs_nonneg _)

noncomputable def eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 (μT P T) :=
  (memLp_efun (P := P) hle i).toLp _

noncomputable def eI (hW : IncrHyp m W P) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 P :=
  (memLp_ifun hW i).toLp _

lemma inner_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eE (P := P) hle T i, eE hle T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eE
  rw [L2.inner_def]
  have h1 := (memLp_efun (P := P) hle i).coeFn_toLp
  have h2 := (memLp_efun (P := P) hle j).coeFn_toLp
  have hc : ∫ z, ⟪((memLp_efun (P := P) hle i).toLp _ : ℝ × Ω → ℝ) z,
      ((memLp_efun (P := P) hle j).toLp _ : ℝ × Ω → ℝ) z⟫_ℝ ∂(μT P T) =
      ∫ z, (ind i.u i.v z.1 * ind j.u j.v z.1) * (i.Y z.2 * j.Y z.2) ∂(μT P T) := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, efun, efun]
    ring
  rw [hc, μT, integral_prod_mul (fun r => ind i.u i.v r * ind j.u j.v r)
    (fun ω => i.Y ω * j.Y ω), int_time T i.hvT]

lemma inner_eI (hW : IncrHyp m W P) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eI hW T i, eI hW T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eI
  rw [L2.inner_def]
  have h1 := (memLp_ifun hW i).coeFn_toLp
  have h2 := (memLp_ifun hW j).coeFn_toLp
  have hc : ∫ ω, ⟪((memLp_ifun hW i).toLp _ : Ω → ℝ) ω, ((memLp_ifun hW j).toLp _ : Ω → ℝ) ω⟫_ℝ ∂P =
      ∫ ω, (i.Y ω * (W i.v ω - W i.u ω)) * (j.Y ω * (W j.v ω - W j.u ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, ifun, ifun]
  rw [hc, cov hW i.huv j.huv i.hY j.hY i.hC j.hC, mul_comm]

noncomputable def eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (μT P T) :=
  Finsupp.linearCombination ℝ (eE hle T)

noncomputable def TL (hW : IncrHyp m W P) (T : ℝ≥0) : (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (eI hW T)

lemma inner_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s t : Elem m T →₀ ℝ) :
    ⟪TL hW T s, TL hW T t⟫_ℝ = ⟪eL (P := P) hW.le T s, eL hW.le T t⟫_ℝ := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s1 s2 h1 h2 => simp only [map_add, inner_add_left, h1, h2]
  | single i a =>
    induction t using Finsupp.induction_linear with
    | zero => simp
    | add t1 t2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single j b =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_left,
        real_inner_smul_right, inner_eI, inner_eE]

lemma norm_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    ‖TL hW T s‖ = ‖eL (P := P) hW.le T s‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_TL]



end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma V_eq {u w : ℝ≥0} (huw : u ≤ w) : ((V u w : ℝ≥0) : ℝ) = (w : ℝ) - u := by
  rw [V, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast huw))]

theorem incr_B (M : Model p Ω) (hM : M.Standing) : IncrHyp M.F M.B M.P := by
  have := hM.prob
  exact
  { mono := fun _ _ h => M.F.mono h
    le := M.F.le
    adapt := fun t => B_measF M hM le_rfl
    indep := fun u v huv => indep_dB M hM huv
    mem2 := fun u v => memLp_xi (dB_meas M hM u v) (dB_law M hM u v)
    mean := fun u v _ => integral_gauss (dB_law M hM u v)
    var := fun u v huv => by
      have h := integral_sq_gauss (dB_law M hM u v)
      rw [V_eq huv] at h
      exact h }



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



lemma coe_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (TL hW T s : Ω → ℝ) =ᵐ[P] fun ω => s.sum (fun i c => c * ifun W i ω) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with ω h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (TL hW T s1) (TL hW T s2), h1, h2] with ω h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [TL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eI hW T i), (memLp_ifun hW i).coeFn_toLp] with ω h h'
    rw [h, Pi.smul_apply, eI, h', smul_eq_mul]

lemma coe_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (eL (P := P) hle T s : ℝ × Ω → ℝ) =ᵐ[μT P T] fun z => s.sum (fun i c => c * efun i z) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μT P T)] with z h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (eL (P := P) hle T s1) (eL hle T s2), h1, h2] with z h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [eL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eE (P := P) hle T i),
      (memLp_efun (P := P) hle i).coeFn_toLp] with z h h'
    rw [h, Pi.smul_apply, eE, h', smul_eq_mul]

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

lemma clamp_sub_le {D x y : ℝ} (hy : |y| ≤ D) : |max (-D) (min D x) - y| ≤ |x - y| := by
  have hy' := abs_le.1 hy
  rcases le_total x D with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-D) x with h2 | h2
    · exact le_of_eq (by rw [max_eq_right h2])
    · rw [max_eq_left h2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

lemma clamp_abs_le {D x : ℝ} (hD : 0 ≤ D) : |max (-D) (min D x)| ≤ D :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma cell_uniq {T : ℝ≥0} {n j k : ℕ} {u : ℝ}
    (hj : (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n)
    (hk : (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n) :
    j = k := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hT : (0 : ℝ) ≤ T.val := T.2
  have e1 : (j : ℝ) * T.val < ((k : ℝ) + 1) * T.val :=
    (div_lt_div_iff_of_pos_right h2).1 (lt_of_lt_of_le hj.1 hk.2)
  have e2 : (k : ℝ) * T.val < ((j : ℝ) + 1) * T.val :=
    (div_lt_div_iff_of_pos_right h2).1 (lt_of_lt_of_le hk.1 hj.2)
  have f1 : (j : ℝ) < (k : ℝ) + 1 := lt_of_mul_lt_mul_right e1 hT
  have f2 : (k : ℝ) < (j : ℝ) + 1 := lt_of_mul_lt_mul_right e2 hT
  have g1 : j < k + 1 := by exact_mod_cast f1
  have g2 : k < j + 1 := by exact_mod_cast f2
  omega

lemma stepValue_comp (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) (g : ℝ → ℝ) (hg : g 0 = 0) (u : ℝ)
    (ω : Ω) :
    itoStepValue T n (fun k ω => g (e k ω)) u ω = g (itoStepValue T n e u ω) := by
  unfold itoStepValue
  by_cases h : ∃ k ∈ Finset.range (2 ^ n), (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
      u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n
  · obtain ⟨k, hk, hc⟩ := h
    have key : ∀ v : ℕ → ℝ, ∑ j ∈ Finset.range (2 ^ n), (if (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
        u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n then v j else 0) = v k := by
      intro v
      rw [Finset.sum_eq_single_of_mem k hk
        (fun j _ hjk => if_neg (fun hcj => hjk (cell_uniq hcj hc))), if_pos hc]
    exact (key (fun j => g (e j ω))).trans (congrArg g (key (fun j => e j ω))).symm
  · have z : ∀ v : ℕ → ℝ, ∑ j ∈ Finset.range (2 ^ n), (if (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
        u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n then v j else 0) = 0 :=
      fun v => Finset.sum_eq_zero (fun j hj => if_neg (fun hc => h ⟨j, hj, hc⟩))
    exact (z (fun j => g (e j ω))).trans (hg.symm.trans (congrArg g (z (fun j => e j ω))).symm)

lemma stepValue_meas (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) (ω : Ω) :
    Measurable (fun u => itoStepValue T n e u ω) := by
  have : (fun u => itoStepValue T n e u ω) = fun u => ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * T.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n)).indicator
        (fun _ => e k ω) u := funext fun u => itoStepValue_eq_sum_indicator T n e u ω
  rw [this]
  exact Finset.measurable_sum _ fun k _ => measurable_const.indicator measurableSet_Ioc

lemma err_intervalIntegrable (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) {H : ℝ≥0 → Ω → ℝ} {D : ℝ}
    (hD : ∀ u ω, |H u ω| ≤ D) (hHm : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω)) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue T n e u ω - H u.toNNReal ω) ^ 2) volume 0 T.val := by
  have h1 := itoStepValue_sq_intervalIntegrable T n e ω
  have hc : IntervalIntegrable (fun _ : ℝ => 2 * D ^ 2) volume 0 T.val := intervalIntegrable_const
  refine ((h1.const_mul 2).add hc).mono_fun
    (((stepValue_meas T n e ω).sub (hHm ω)).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD u.toNNReal ω)
  have hH2 : H u.toNNReal ω ^ 2 ≤ D ^ 2 :=
    sq_le_sq.2 (by rw [abs_of_nonneg hD0]; exact hD _ _)
  have hx := sq_nonneg (itoStepValue T n e u ω + H u.toNNReal ω)
  have hs := sq_nonneg (itoStepValue T n e u ω)
  have hid : 2 * itoStepValue T n e u ω ^ 2 + 2 * H u.toNNReal ω ^ 2 -
      (itoStepValue T n e u ω - H u.toNNReal ω) ^ 2 =
      (itoStepValue T n e u ω + H u.toNNReal ω) ^ 2 := by ring
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
  linarith

/-- Bounded nonnegative functions tending to zero in measure have integrals tending to zero. -/
lemma integral_tendsto_zero_of_bdd {F : ℕ → Ω → ℝ} {K : ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) P) (hF0 : ∀ n ω, 0 ≤ F n ω) (hFK : ∀ n ω, F n ω ≤ K)
    (h : TendstoInMeasure P F atTop (fun _ => 0)) :
    Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K' := max K 1 with hK'
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hδ : 0 < ε / 2 := by linarith
  have hm := (tendstoInMeasure_iff_dist.1 h) (ε / 2) hδ
  have hev : ∀ᶠ n in atTop, P {ω | ε / 2 ≤ dist (F n ω) 0} < ENNReal.ofReal (ε / (2 * K')) :=
    (tendsto_order.1 hm).2 _ (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  set S := {ω | ε / 2 ≤ dist (F n ω) 0} with hS
  set S' := toMeasurable P S with hS'
  have hS'm : MeasurableSet S' := measurableSet_toMeasurable P S
  have hPS' : P S' < ENNReal.ofReal (ε / (2 * K')) := by
    rw [hS', measure_toMeasurable]; exact hN n hn
  have hreal : P.real S' < ε / (2 * K') := ENNReal.toReal_lt_of_lt_ofReal hPS'
  have hint : Integrable (F n) P :=
    memLp_one_iff_integrable.1 (MemLp.of_bound (hFm n) K' (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n ω)]
      exact (hFK n ω).trans (le_max_left _ _)))
  have hg : Integrable (fun ω => ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hS'm |>.const_mul K')
  have hle : ∫ ω, F n ω ∂P ≤ ∫ ω, (ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P := by
    refine integral_mono hint hg (fun ω => ?_)
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω, mul_one]
      have := (hFK n ω).trans (le_max_left K 1)
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hωS : ω ∉ S := fun h => hω (subset_toMeasurable P S h)
      simp only [hS, Set.mem_setOf_eq, not_le, Real.dist_eq, sub_zero] at hωS
      rw [abs_of_nonneg (hF0 n ω)] at hωS
      exact hωS.le
  have hval : ∫ ω, (ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P = ε / 2 + K' * P.real S' := by
    rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator hS'm |>.const_mul K'),
      integral_const, integral_const_mul, integral_indicator_const (1 : ℝ) hS'm]
    simp
  have hK'r : K' * P.real S' < ε / 2 := by
    have := mul_lt_mul_of_pos_left hreal hK'pos
    rw [show K' * (ε / (2 * K')) = ε / 2 by field_simp] at this
    exact this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (hF0 n))]
  linarith

/-! The clamped approximants as elementary combinations. -/

/-- Clamped coefficients. -/
noncomputable def clampSeq (D : ℝ) (a0 : ℕ → ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  max (-D) (min D (a0 n k ω))

/-- Difference coefficients. -/
noncomputable def diffSeq (D : ℝ) (a0 : ℕ → ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  a0 n k ω - clampSeq D a0 n k ω

lemma stepSum_diff (T : ℝ≥0) (n : ℕ) (D : ℝ) (a0 : ℕ → ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W T n (diffSeq D a0 n) ω =
      itoStepSum W T n (a0 n) ω - itoStepSum W T n (clampSeq D a0 n) ω := by
  unfold itoStepSum diffSeq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma stepValue_diff (T : ℝ≥0) (n : ℕ) (D : ℝ) (a0 : ℕ → ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue T n (diffSeq D a0 n) u ω =
      itoStepValue T n (a0 n) u ω - itoStepValue T n (clampSeq D a0 n) u ω := by
  unfold itoStepValue diffSeq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma grid_le (T : ℝ≥0) (n k : ℕ) :
    (k : ℝ≥0) * T / (2 : ℝ≥0) ^ n ≤ ((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right le_self_add (by positivity)) (by positivity)

lemma grid_top (T : ℝ≥0) (n k : ℕ) (hk : k < 2 ^ n) :
    ((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n ≤ T := by
  have hk1 : (k : ℝ≥0) + 1 ≤ (2 : ℝ≥0) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk
  rw [div_le_iff₀ (by positivity), mul_comm T]
  exact mul_le_mul_of_nonneg_right hk1 (by positivity)

/-- The grid elementary process `Y 1_[k T/2^n, (k+1) T/2^n)`. -/
noncomputable def gElem (T : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n)) (Y : Ω → ℝ)
    (hY : Measurable[m (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] Y) (C : ℝ)
    (hC : ∀ ω, |Y ω| ≤ C) : Elem m T where
  u := ((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n
  v := (((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n
  huv := grid_le T n k
  hvT := grid_top T n k k.2
  Y := Y
  hY := hY
  C := C
  hC := hC

lemma sum_single_comb {ι : Type*} [Fintype ι] {T : ℝ≥0} (e : ι → Elem m T)
    (g : Elem m T → ℝ → ℝ) (hg0 : ∀ i, g i 0 = 0)
    (hgadd : ∀ i b1 b2, g i (b1 + b2) = g i b1 + g i b2) :
    (∑ k, Finsupp.single (e k) (1 : ℝ)).sum g = ∑ k, g (e k) 1 := by
  rw [← Finsupp.sum_finsetSum_index hg0 hgadd]
  exact Finset.sum_congr rfl fun k _ => Finsupp.sum_single_index (hg0 _)

/-- The left-closed grid step function agrees with `itoStepValue` off the finite grid. -/
lemma ind_grid_eq (T : ℝ≥0) (n k : ℕ) {u : ℝ}
    (hu1 : u ≠ (k : ℝ) * T.val / (2 : ℝ) ^ n) (hu2 : u ≠ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n)
    (y : ℝ) :
    ind ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) (((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) u * y =
      if (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n
        then y else 0 := by
  unfold ind
  simp only [Set.indicator_apply, Set.mem_Ico, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
  have e1 : ((k : ℝ) * (T : ℝ) / 2 ^ n ≤ u ∧ u < ((k : ℝ) + 1) * (T : ℝ) / 2 ^ n) ↔
      ((k : ℝ) * T.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hu1), h2.le⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, lt_of_le_of_ne h2 hu2⟩
  by_cases hc : (k : ℝ) * T.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n
  · rw [if_pos (e1.2 hc), if_pos hc, one_mul]
  · rw [if_neg (fun h => hc (e1.1 h)), if_neg hc, zero_mul]


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












/-- The predictable subspace of `L²(μT)`. -/
noncomputable def Pred (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (μT P T)) :=
  (LinearMap.range (eL (P := P) hle T)).topologicalClosure

lemma mem_Pred_iff (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (x : Lp ℝ 2 (μT P T)) :
    x ∈ Pred (P := P) hle T ↔ x ∈ closure (Set.range (eL (P := P) hle T)) := by
  rw [Pred, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]




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










/-- If `TL x_n → θ` and `a ∈ Pred` represents `θ`, then `eL x_n → a`. -/
theorem eL_tendsto (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T)))
    {x : ℕ → (Elem m T →₀ ℝ)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ)) :
    Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 a) := by
  have hc : CauchySeq fun n => eL (P := P) hW.le T (x n) := by
    have hcu : CauchySeq fun n => TL hW T (x n) := hx.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, ← norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hc
  have hψP : ψ ∈ closure (Set.range (eL (P := P) hW.le T)) :=
    mem_closure_of_tendsto hψ (Eventually.of_forall fun n => ⟨x n, rfl⟩)
  have horth : ∀ y, ⟪a - ψ, eL (P := P) hW.le T y⟫_ℝ = 0 := by
    intro y
    have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
      hx.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
        (𝓝 ⟪ψ, eL (P := P) hW.le T y⟫_ℝ) := hψ.inner tendsto_const_nhds
    simp only [inner_TL] at h1
    rw [inner_sub_left, ← ha y, tendsto_nhds_unique h1 h2, sub_self]
  have hcl : closure (Set.range (eL (P := P) hW.le T)) ⊆ {w | ⟪a - ψ, w⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact horth y)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hmem : a - ψ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
    have := (Pred (P := P) hW.le T).sub_mem ((mem_Pred_iff hW.le T a).2 haP)
      ((mem_Pred_iff hW.le T ψ).2 hψP)
    exact (mem_Pred_iff hW.le T _).1 this
  have h0 : a - ψ = 0 := inner_self_eq_zero.1 (hcl hmem)
  rw [sub_eq_zero.1 h0]
  exact hψ

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

/-- `θ` is the stochastic integral of the predictable integrand `b`. -/
def Rep (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Set.range (TL hW T)) ∧ b ∈ closure (Set.range (eL (P := P) hW.le T)) ∧
    ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪b, eL (P := P) hW.le T x⟫_ℝ

lemma rep_dist (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) (x : Elem m T →₀ ℝ) :
    ‖TL hW T x - θ‖ = ‖eL (P := P) hW.le T x - b‖ := by
  obtain ⟨hθ, hb, hi⟩ := h
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hθ
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by simp_rw [hy]; exact hx
  have hE := eL_tendsto hW T hi hb hx'
  have h1 : Tendsto (fun n => ‖TL hW T x - TL hW T (y n)‖) atTop (𝓝 ‖TL hW T x - θ‖) :=
    (tendsto_const_nhds.sub hx').norm
  have h2 : Tendsto (fun n => ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖) atTop
      (𝓝 ‖eL (P := P) hW.le T x - b‖) := (tendsto_const_nhds.sub hE).norm
  have he : ∀ n, ‖TL hW T x - TL hW T (y n)‖ =
      ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖ := by
    intro n; rw [← map_sub, ← map_sub, norm_TL]
  simp_rw [he] at h1
  exact tendsto_nhds_unique h1 h2
























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
-- ===== slice of RUmod (probe/slice8c/cuts/r_z4m.lean.src/RUmod.lean): 10/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Elementary time-space functions `1_[u,v) Y`, Elem-free. -/
def SE (m : ℝ≥0 → MeasurableSpace Ω) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 (μT P T)) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun z : ℝ × Ω => ind u v z.1 * Y z.2) 2 (μT P T), g = h.toLp _}

/-- Elementary stochastic integrals `Y (W_v - W_u)`, Elem-free. -/
def SI (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 P) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _}

/-- `Rep`, Elem-free. -/
def RepU (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0)
    (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) ∧
    b ∈ closure (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) ∧
    ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y → (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
      ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
        ∫ z, (b : ℝ × Ω → ℝ) z * (ind u v z.1 * Y z.2) ∂(μT P T)



lemma range_eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eE (P := P) hle T) = SE m P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_efun hle i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eI (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (eI hW T) = SI m W P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_ifun hW i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eL (P := P) hle T) = (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) := by
  rw [← LinearMap.coe_range]
  unfold eL
  rw [Finsupp.range_linearCombination, range_eE]

lemma range_TL (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (TL hW T) = (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) := by
  rw [← LinearMap.coe_range]
  unfold TL
  rw [Finsupp.range_linearCombination, range_eI]


lemma int_eI (hW : IncrHyp m W P) {T : ℝ≥0} (θ : Lp ℝ 2 P) (i : Elem m T) :
    ∫ ω, (θ : Ω → ℝ) ω * (i.Y ω * (W i.v ω - W i.u ω)) ∂P = ⟪θ, eI hW T i⟫_ℝ := by
  unfold eI
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_ifun hW i).coeFn_toLp] with ω hω
  rw [hω, ifun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma int_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (b : Lp ℝ 2 (μT P T)) (i : Elem m T) :
    ∫ z, (b : ℝ × Ω → ℝ) z * (ind i.u i.v z.1 * i.Y z.2) ∂(μT P T) = ⟪b, eE (P := P) hle T i⟫_ℝ := by
  unfold eE
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_efun (P := P) hle i).coeFn_toLp] with z hz
  rw [hz, efun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma rep_iff (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) :
    StochCalcO3.Rep hW T θ b ↔ RepU m W P T θ b := by
  unfold StochCalcO3.Rep RepU
  rw [range_TL, range_eL]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩)
  · intro u v huv hvT Y hY hC
    obtain ⟨C, hC⟩ := hC
    let i : Elem m T := ⟨u, v, huv, hvT, Y, hY, C, hC⟩
    have h1 := h (Finsupp.single i 1)
    simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at h1
    rw [int_eI hW θ i, int_eE hW.le b i]
    exact h1
  · intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add s1 s2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single i a =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_right]
      rw [← int_eI hW θ i, ← int_eE hW.le b i, h i.u i.v i.huv i.hvT i.Y i.hY ⟨i.C, i.hC⟩]

end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcZ2 StochCalcZ3 StochCalcO3
open StochCalcZK
open StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcQ2U

end StochCalcP6

-- ===== slice of P8c066573M16c (probe/slice8c/cuts/r_z4m.lean.src/P8c066573M16c.lean): 13/865 top-level decls kept =====

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










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












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
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





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











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






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



lemma rep_lim (hW : IncrHyp m W P) (T : ℝ≥0) {x : ℕ → (Elem m T →₀ ℝ)} {θ : Lp ℝ 2 P}
    {b : Lp ℝ 2 (μT P T)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ))
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) : Rep hW T θ b := by
  refine ⟨mem_closure_of_tendsto hx (Eventually.of_forall fun n => ⟨x n, rfl⟩),
    mem_closure_of_tendsto hb (Eventually.of_forall fun n => ⟨x n, rfl⟩), fun y => ?_⟩
  have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
    hx.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
      (𝓝 ⟪b, eL (P := P) hW.le T y⟫_ℝ) := hb.inner tendsto_const_nhds
  simp only [inner_TL] at h1
  exact tendsto_nhds_unique h1 h2

lemma rep_exists (hW : IncrHyp m W P) (T : ℝ≥0) {b : Lp ℝ 2 (μT P T)}
    (hb : b ∈ closure (Set.range (eL (P := P) hW.le T))) : ∃ θ, Rep hW T θ b := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hb
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  have hc : CauchySeq fun n => TL hW T (y n) := by
    have hcu : CauchySeq fun n => eL (P := P) hW.le T (y n) := hx'.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨θ, hθ⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨θ, rep_lim hW T hθ hx'⟩

lemma rep_conv (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {x : ℕ → (Elem m T →₀ ℝ)}
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) :
    Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
  simp_rw [rep_dist hW T h]
  exact hb





















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

/-- **Z4 (O4rep).** EK step approximants of a bounded jointly measurable integrand `H` whose step
sums converge in probability to `J`: then `J` is (a.e.) the `Rep`-stochastic integral of `H`. -/
theorem O4rep (hW : IncrHyp m W P) (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (a0 : ℕ → ℕ → Ω → ℝ)
    (ha0m : ∀ n k : ℕ, k < 2 ^ n → Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (a0 n k))
    (ha0C : ∀ n, ∃ C : ℝ, ∀ k, k < 2 ^ n → ∀ ω, |a0 n k ω| ≤ C)
    (ha0H : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2) atTop (fun _ => (0 : ℝ)))
    {J : Ω → ℝ} (hJ : TendstoInMeasure P (fun n => itoStepSum W T n (a0 n)) atTop J)
    (hzero : ∀ c : ℕ → ℕ → Ω → ℝ,
      (∀ n k : ℕ, k < 2 ^ n → Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (c n k)) →
      (∀ n, ∃ C : ℝ, ∀ k, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C) →
      TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
        ((T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ)) →
      TendstoInMeasure P (fun n => itoStepSum W T n (c n)) atTop (fun _ => (0 : ℝ))) :
    ∀ hH2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T),
      ∃ θ : Lp ℝ 2 P, (θ : Ω → ℝ) =ᵐ[P] J ∧ Rep hW T θ (hH2.toLp _) := by
  intro hH2
  have hT0 : (0 : ℝ) ≤ T.val := T.2
  have hHm' : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω) :=
    fun ω => hHm.comp (measurable_id.prodMk measurable_const)
  have hcm : ∀ n k : ℕ, k < 2 ^ n →
      Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (clampSeq D a0 n k) :=
    fun n k hk => measurable_const.max (measurable_const.min (ha0m n k hk))
  have hcb : ∀ n k ω, |clampSeq D a0 n k ω| ≤ D := fun n k ω => clamp_abs_le hD0
  have hg0 : max (-D) (min D 0) = 0 := by
    rw [min_eq_right hD0, max_eq_right (neg_nonpos.2 hD0)]
  have hsvc : ∀ n u ω, itoStepValue T n (clampSeq D a0 n) u ω =
      max (-D) (min D (itoStepValue T n (a0 n) u ω)) :=
    fun n u ω => stepValue_comp T n (a0 n) (fun x => max (-D) (min D x)) hg0 u ω
  have herr : ∀ n u ω, (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 ≤
      (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 := fun n u ω => by
    rw [hsvc]; exact sq_le_sq.2 (clamp_sub_le (hD _ _))
  have hEc0 : ∀ n ω, 0 ≤ ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_nonneg hT0 (fun u _ => sq_nonneg _)
  have hEa0 : ∀ n ω, 0 ≤ ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_nonneg hT0 (fun u _ => sq_nonneg _)
  have hEcle : ∀ n ω, (∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ≤
      ∫ u in (0 : ℝ)..T.val, (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_mono_on hT0
      (err_intervalIntegrable T n _ hD hHm' ω) (err_intervalIntegrable T n _ hD hHm' ω)
      (fun u _ => herr n u ω)
  have hEc : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) atTop
      (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_zero_of_abs_le (K := 1) one_pos ha0H ha0H (fun n ω => ?_)
    rw [abs_of_nonneg (hEc0 n ω), abs_of_nonneg (hEa0 n ω)]
    linarith [hEcle n ω, hEa0 n ω]
  -- the clamped step sums still converge to `J`
  have hd : TendstoInMeasure P (fun n => itoStepSum W T n (diffSeq D a0 n)) atTop
      (fun _ => (0 : ℝ)) := by
    refine hzero (diffSeq D a0) (fun n k hk => (ha0m n k hk).sub (hcm n k hk)) (fun n => ?_) ?_
    · obtain ⟨C1, h1⟩ := ha0C n
      refine ⟨C1 + D, fun k hk ω => ?_⟩
      have e1 := abs_le.1 (h1 k hk ω)
      have e2 := abs_le.1 (hcb n k ω)
      exact abs_le.2 ⟨by unfold diffSeq; linarith only [e1.1, e2.2],
        by unfold diffSeq; linarith only [e1.2, e2.1]⟩
    · refine tendstoInMeasure_zero_of_abs_le (K := 2) two_pos ha0H hEc (fun n ω => ?_)
      rw [← itoStepValue_sq_integral]
      have hfa := err_intervalIntegrable T n (a0 n) hD hHm' ω
      have hfb := err_intervalIntegrable T n (clampSeq D a0 n) hD hHm' ω
      have hd0 : 0 ≤ ∫ u in (0 : ℝ)..T.val, (itoStepValue T n (diffSeq D a0 n) u ω) ^ 2 :=
        intervalIntegral.integral_nonneg hT0 (fun u _ => sq_nonneg _)
      rw [abs_of_nonneg hd0, abs_of_nonneg (hEa0 n ω), abs_of_nonneg (hEc0 n ω)]
      calc ∫ u in (0 : ℝ)..T.val, (itoStepValue T n (diffSeq D a0 n) u ω) ^ 2
          ≤ ∫ u in (0 : ℝ)..T.val, (2 * (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 +
              2 * (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) := by
            refine intervalIntegral.integral_mono_on hT0
              (itoStepValue_sq_intervalIntegrable T n (diffSeq D a0 n) ω)
              ((hfa.const_mul 2).add (hfb.const_mul 2)) (fun u _ => ?_)
            rw [stepValue_diff]
            linarith only [sq_nonneg (itoStepValue T n (a0 n) u ω - H u.toNNReal ω +
              (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω))]
        _ = 2 * ((∫ u in (0 : ℝ)..T.val, (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2) +
              ∫ u in (0 : ℝ)..T.val,
                (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) := by
            rw [intervalIntegral.integral_add (hfa.const_mul 2) (hfb.const_mul 2),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
            ring
  have hcJ : TendstoInMeasure P (fun n => itoStepSum W T n (clampSeq D a0 n)) atTop J := by
    have h1 := tendstoInMeasure_sub_real hJ hd
    refine (h1.congr_left (fun n => Eventually.of_forall fun ω => ?_)).congr_right
      (Eventually.of_forall fun ω => sub_zero (J ω))
    show itoStepSum W T n (a0 n) ω - itoStepSum W T n (diffSeq D a0 n) ω =
      itoStepSum W T n (clampSeq D a0 n) ω
    rw [stepSum_diff]; ring
  -- the elementary combinations
  let e : (n : ℕ) → Fin (2 ^ n) → Elem m T := fun n k =>
    gElem T n k (clampSeq D a0 n k) (hcm n k k.2) D (hcb n k)
  let s : ℕ → (Elem m T →₀ ℝ) := fun n => ∑ k, Finsupp.single (e n k) (1 : ℝ)
  have hsI : ∀ n ω, (s n).sum (fun i c => c * ifun W i ω) =
      itoStepSum W T n (clampSeq D a0 n) ω := by
    intro n ω
    show (∑ k, Finsupp.single (e n k) (1 : ℝ)).sum _ = _
    rw [sum_single_comb (e n) (fun i c => c * ifun W i ω) (fun i => zero_mul _)
      (fun i b1 b2 => add_mul _ _ _)]
    simp only [one_mul, ifun, e, gElem]
    exact Fin.sum_univ_eq_sum_range (fun k => clampSeq D a0 n k ω *
      (W (((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) ω - W ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ω)) (2 ^ n)
  have hsE : ∀ n (z : ℝ × Ω), (s n).sum (fun i c => c * efun i z) = ∑ k : Fin (2 ^ n),
      ind (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ((((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) z.1 *
        clampSeq D a0 n k z.2 := by
    intro n z
    show (∑ k, Finsupp.single (e n k) (1 : ℝ)).sum _ = _
    rw [sum_single_comb (e n) (fun i c => c * efun i z) (fun i => zero_mul _)
      (fun i b1 b2 => add_mul _ _ _)]
    simp only [one_mul, efun, e, gElem]
  have hoff : ∀ n (u : ℝ) (ω : Ω),
      u ∉ (fun j : ℕ => (j : ℝ) * T.val / (2 : ℝ) ^ n) '' Set.Iic (2 ^ n) →
      ∑ k : Fin (2 ^ n), ind (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n)
        ((((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) u * clampSeq D a0 n k ω =
      itoStepValue T n (clampSeq D a0 n) u ω := by
    intro n u ω hu
    unfold itoStepValue
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine ind_grid_eq T n k (fun h => hu ⟨k, Set.mem_Iic.2 (le_of_lt k.2), h.symm⟩)
      (fun h => hu ⟨(k : ℕ) + 1, Set.mem_Iic.2 (Nat.succ_le_of_lt k.2), by rw [h]; norm_num⟩) _
  have hGnull : ∀ n, volume ((fun j : ℕ => (j : ℝ) * T.val / (2 : ℝ) ^ n) '' Set.Iic (2 ^ n)) = 0 :=
    fun n => ((Set.finite_Iic _).image _).countable.measure_zero volume
  -- `L²(μT)` convergence
  have hψ2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T) :=
    MemLp.of_bound hHm.aestronglyMeasurable D (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hD _ _)
  have hgL : ∀ n, MemLp (fun z => (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2
      (μT P T) := fun n =>
    ((Lp.memLp (eL (P := P) hW.le T (s n))).ae_eq (coe_eL (P := P) hW.le T (s n))).sub hψ2
  have hinner : ∀ n ω, ∫ u, ((s n).sum (fun i c => c * efun i (u, ω)) - H (u, ω).1.toNNReal
      (u, ω).2) ^ 2 ∂(volume.restrict (Set.Ico (0 : ℝ) T)) = ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 := by
    intro n ω
    rw [intervalIntegral.integral_of_le hT0, ← integral_Ico_eq_integral_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hGnull n))] with u hu
    rw [hsE]
    dsimp only
    rw [hoff n u ω hu]
  have hfub : ∀ n, ∫ z, ((s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) ^ 2 ∂(μT P T) =
      ∫ ω, (∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ∂P := by
    intro n
    rw [show μT P T = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P from rfl,
      integral_prod_symm _ (hgL n).integrable_sq]
    exact integral_congr_ae (Eventually.of_forall fun ω => hinner n ω)
  have hEm : ∀ n, AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) P := by
    intro n
    have hi := (hgL n).integrable_sq.integral_prod_right
    exact hi.aestronglyMeasurable.congr (Eventually.of_forall fun ω => hinner n ω)
  have hEK : ∀ n ω, (∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ≤ T.val * (2 * D) ^ 2 := by
    intro n ω
    calc (∫ u in (0 : ℝ)..T.val,
          (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2)
        ≤ ∫ u in (0 : ℝ)..T.val, (2 * D) ^ 2 := by
          refine intervalIntegral.integral_mono_on hT0 (err_intervalIntegrable T n _ hD hHm' ω)
            intervalIntegrable_const (fun u _ => ?_)
          have h1 : |itoStepValue T n (clampSeq D a0 n) u ω| ≤ D := by
            rw [hsvc]; exact clamp_abs_le hD0
          have h2 := hD u.toNNReal ω
          have h3 := abs_sub (itoStepValue T n (clampSeq D a0 n) u ω) (H u.toNNReal ω)
          exact sq_le_sq.2 (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * D)]; linarith)
      _ = T.val * (2 * D) ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hI : Tendsto (fun n => ∫ z, ((s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) ^ 2
      ∂(μT P T)) atTop (𝓝 0) := by
    simp only [hfub]
    exact integral_tendsto_zero_of_bdd hEm hEc0 hEK hEc
  have hψ : Tendsto (fun n => eLpNorm (fun z => (s n).sum (fun i c => c * efun i z) -
      H z.1.toNNReal z.2) 2 (μT P T)) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm (fun z => (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2
        (μT P T) = ENNReal.ofReal ((∫ z, ((s n).sum (fun i c => c * efun i z) -
          H z.1.toNNReal z.2) ^ 2 ∂(μT P T)) ^ (2 : ℝ)⁻¹) := by
      intro n
      rw [(hgL n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    simp only [e]
    have h0 : ENNReal.ofReal ((0 : ℝ) ^ (2 : ℝ)⁻¹) = 0 := by
      rw [Real.zero_rpow (by norm_num)]; simp
    rw [← h0]
    exact ENNReal.tendsto_ofReal
      ((Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))).tendsto.comp hI)
  have hJ' : TendstoInMeasure P (fun n ω => (s n).sum (fun i c => c * ifun W i ω)) atTop J :=
    TendstoInMeasure.congr_left (fun n => Eventually.of_forall fun ω => (hsI n ω).symm) hcJ
  have hψL : Tendsto (fun n => eL (P := P) hW.le T (s n)) atTop (𝓝 (hH2.toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hψ.congr' (Eventually.of_forall fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [coe_eL (P := P) hW.le T (s n), hH2.coeFn_toLp] with z e1 e2
    simp only [Pi.sub_apply, e1, e2]
  obtain ⟨θ, hθ⟩ := rep_exists hW T
    (mem_closure_of_tendsto hψL (Eventually.of_forall fun n => ⟨s n, rfl⟩))
  have hm1 : TendstoInMeasure P (fun n => (TL hW T (s n) : Ω → ℝ)) atTop θ :=
    tendstoInMeasure_of_tendsto_Lp (rep_conv hW T hθ hψL)
  have hm2 : TendstoInMeasure P (fun n => (TL hW T (s n) : Ω → ℝ)) atTop J :=
    TendstoInMeasure.congr_left (fun n => (coe_TL hW T (s n)).symm) hJ'
  exact ⟨θ, tendstoInMeasure_ae_unique hm1 hm2, hθ⟩


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

/-- A function measurable for the a.e. closure of `G` (`G` containing the measurable null sets)
has a `G`-measurable a.e. version. -/
theorem exists_version_of_aeClosure {G : MeasurableSpace Ω'} {m0 : MeasurableSpace Ω'}
    {P : Measure[m0] Ω'} (hG : G ≤ m0)
    (hG0 : ∀ N : Set Ω', MeasurableSet[m0] N → P N = 0 → MeasurableSet[G] N) {Y : Ω' → ℝ}
    (hY : Measurable[aeClosure P G] Y) : ∃ Y' : Ω' → ℝ, Measurable[G] Y' ∧ Y' =ᵐ[P] Y := by
  have hnull : @NullMeasurable Ω' ℝ G _ Y (P.trim hG) := by
    intro S hS
    obtain ⟨B, hB, hAB⟩ := hY hS
    have h0 : P {x | ¬ ((Y ⁻¹' S) x = B x)} = 0 := ae_iff.1 hAB
    obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
    have hNG := hG0 N hNm hN0
    have hAB' : Y ⁻¹' S =ᵐ[P.trim hG] B := by
      refine ae_iff.2 ?_
      exact measure_mono_null hsub (by rw [trim_measurableSet_eq hG hNG]; exact hN0)
    exact (hB.nullMeasurableSet (μ := P.trim hG)).congr hAB'.symm
  have hae := hnull.aemeasurable
  exact ⟨hae.mk Y, hae.measurable_mk, (ae_eq_of_ae_eq_trim hae.ae_eq_mk).symm⟩

lemma meas_vec {m : MeasurableSpace Ω'} {f g : Ω' → ℝ} (hf : Measurable[m] f)
    (hg : Measurable[m] g) :
    Measurable[m] (fun ω => (WithLp.toLp 2 ![f ω, g ω] : EuclideanSpace ℝ (Fin 2))) := by
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  fin_cases i
  · simpa using hf
  · simpa using hg

end Gen

lemma null_mem_F (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) (N : Set Ω) (hN : MeasurableSet N)
    (hN0 : M.P N = 0) : MeasurableSet[M.F t] N := by
  have h1 : MeasurableSet[MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet N ∧ M.P N = 0}] N :=
    MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩
  have h2 : MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ M.P N = 0} ≤ M.F t := by
    rw [hM.filtF t]; exact le_sup_right
  exact h2 N h1

lemma pair_measF (M : Model p Ω) (hM : M.Standing) {s t : ℝ≥0} (hs : s ≤ t) :
    Measurable[M.F t] (fun ω => (M.B s ω, M.Bt s ω)) := by
  have h2 : MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance ≤ M.F t := by
    rw [hM.filtF t]
    exact le_sup_of_le_left (le_iSup₂ (f := fun s' (_ : s' ≤ t) =>
      MeasurableSpace.comap (fun ω => (M.B s' ω, M.Bt s' ω)) inferInstance) s hs)
  exact Measurable.of_comap_le h2

lemma W_measF (M : Model p Ω) (hM : M.Standing) {s t : ℝ≥0} (hs : s ≤ t) :
    Measurable[M.F t] (W M s) := by
  have hN := null_mem_F M hM t (Nbad M) (Nbad_meas M) (Nbad_null M hM)
  have hB : Measurable[M.F t] (M.B s) := measurable_fst.comp (pair_measF M hM hs)
  have hBt : Measurable[M.F t] (M.Bt s) := measurable_snd.comp (pair_measF M hM hs)
  have h0 : Measurable[M.F t] (gB M s) := Measurable.ite hN measurable_const hB
  have h1 : Measurable[M.F t] (gBt M s) := Measurable.ite hN measurable_const hBt
  exact meas_vec h0 h1

lemma cBP_le_aeF (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    completedBrownianPast M.P (W M) (fun _ => 0) t ≤ aeClosure M.P (M.F t) := by
  have hGW : (⨆ r : Set.Iic t, MeasurableSpace.comap (W M r.val) inferInstance) ≤ M.F t :=
    iSup_le fun r => (W_measF M hM r.2).comap_le
  intro A hA
  obtain ⟨B, hB, hAB⟩ := completedBrownianPast_const_le M.P (W M) 0 t A hA
  exact ⟨B, hGW B hB, hAB⟩

/-- **Z4m-a.** Every completed-Brownian-past measurable variable has an `M.F t`-measurable
a.e. version. -/
theorem hmod_cBP (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) (Y : Ω → ℝ)
    (hY : Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] Y) :
    ∃ Y' : Ω → ℝ, Measurable[M.F t] Y' ∧ Y' =ᵐ[M.P] Y :=
  exists_version_of_aeClosure (M.F.le t) (null_mem_F M hM t) (hY.mono (cBP_le_aeF M hM t) le_rfl)

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

lemma clampC_eq {C x : ℝ} (h : |x| ≤ C) : max (-|C|) (min |C| x) = x := by
  have h1 := (abs_le.mp h)
  have h2 := le_abs_self C
  rw [min_eq_right (by linarith [h1.2]), max_eq_right (by linarith [h1.1])]

/-- **Z4m-b.** -/
theorem Z4m (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] {H J : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ u ω, |H u ω| ≤ D) (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) H J) (T : ℝ≥0)
    (hH2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT M.P T)) :
    ∃ θ : Lp ℝ 2 M.P, (θ : Ω → ℝ) =ᵐ[M.P] J T ∧ StochCalcO3.Rep (incr_B M hM) T θ (hH2.toLp _) := by
  obtain ⟨a, ham, haC, haH, haJ⟩ := hJ.2 T
  have hv : ∀ n k : ℕ, ∃ Y : Ω → ℝ,
      Measurable[M.F ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] Y ∧ (k < 2 ^ n → Y =ᵐ[M.P] a n k) := by
    intro n k
    by_cases hk : k < 2 ^ n
    · obtain ⟨Y, hY, hYe⟩ := hmod_cBP M hM _ (a n k) (ham n k hk)
      exact ⟨Y, hY, fun _ => hYe⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h hk⟩
  choose Y hYm hYe using hv
  choose C hC using haC
  let a' : ℕ → ℕ → Ω → ℝ := fun n k ω => max (-|C n|) (min |C n| (Y n k ω))
  have ha'm : ∀ n k : ℕ, k < 2 ^ n →
      Measurable[M.F ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (a' n k) :=
    fun n k _ => measurable_const.max (measurable_const.min (hYm n k))
  have ha'C : ∀ n, ∃ C' : ℝ, ∀ k, k < 2 ^ n → ∀ ω, |a' n k ω| ≤ C' := by
    intro n
    refine ⟨|C n|, fun k _ ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le (by linarith [abs_nonneg (C n)]) (min_le_left _ _)
  have hall : ∀ᵐ ω ∂M.P, ∀ n k : ℕ, k < 2 ^ n → a' n k ω = a n k ω := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    by_cases hk : k < 2 ^ n
    · filter_upwards [hYe n k hk] with ω hω _
      show max (-|C n|) (min |C n| (Y n k ω)) = a n k ω
      rw [hω]; exact clampC_eq (hC n k hk ω)
    · exact ae_of_all _ (fun ω h => absurd h hk)
  have ha0H : TendstoInMeasure M.P (fun n ω => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (a' n) u ω - H u.toNNReal ω) ^ 2) atTop (fun _ => (0 : ℝ)) := by
    refine TendstoInMeasure.congr_left (fun n => ?_) haH
    filter_upwards [hall] with ω hω
    have e : ∀ u, itoStepValue T n (a n) u ω = itoStepValue T n (a' n) u ω := by
      intro u
      unfold itoStepValue
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [hω n k (Finset.mem_range.mp hk)]
    simp only [e]
  have hJ' : TendstoInMeasure M.P (fun n => itoStepSum M.B T n (a' n)) atTop (J T) := by
    refine TendstoInMeasure.congr_left (fun n => ?_) haJ
    filter_upwards [hall, ae_W M hM] with ω hω hW
    have e : ∀ t, W M t ω 0 = M.B t ω := fun t => (hW t).1
    unfold itoStepSum
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [e, hω n k (Finset.mem_range.mp hk)]
  have hzero : ∀ c : ℕ → ℕ → Ω → ℝ,
      (∀ n k : ℕ, k < 2 ^ n → Measurable[M.F ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (c n k)) →
      (∀ n, ∃ C : ℝ, ∀ k, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C) →
      TendstoInMeasure M.P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
        ((T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ)) →
      TendstoInMeasure M.P (fun n => itoStepSum M.B T n (c n)) atTop (fun _ => (0 : ℝ)) := by
    intro c hc hC' hq
    have h0 := itoStepSum_tendstoInMeasure_zero (isStandardBrownian M hM) 0 T 0 c
      (fun n k hk => (hc n k hk).mono (F_le_cBP M hM _) le_rfl) hC' hq
    refine TendstoInMeasure.congr_left (fun n => ?_) h0
    filter_upwards [ae_W M hM] with ω hω
    have e : ∀ t, W M t ω 0 = M.B t ω := fun t => (hω t).1
    unfold itoStepSum
    simp only [e]
  exact O4rep (incr_B M hM) T hD0 hD hHm a' ha'm ha'C ha0H hJ' hzero hH2

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
-- ===== slice of P8c066573M17 (probe/slice8c/cuts/r_z4m.lean.src/P8c066573M17.lean): 0/73 top-level decls kept =====

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

-- ===== slice of P8c066573M18 (probe/slice8c/cuts/r_z4m.lean.src/P8c066573M18.lean): 0/23 top-level decls kept =====

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

-- ===== slice of RUb (probe/slice8c/cuts/r_z4m.lean.src/RUb.lean): 0/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}














end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2 StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcQ2U

end StochCalcP6

-- ===== slice of __current__ (probe/slice8c/cuts/r_z4m.lean.src/__current__.lean): 0/98 top-level decls kept =====

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
open Classical in
theorem solution {p : HedgePSNV.Params} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) [IsProbabilityMeasure M.P] (W : ℝ≥0 → Ω → SDEState 2)
    (hW : ∀ t ω, W t ω = WithLp.toLp 2
      ![if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.B t ω,
        if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.Bt t ω])
    {H J : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ u ω, |H u ω| ≤ D) (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) H J) (T : ℝ≥0)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) T)).prod M.P)
    (hH2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 μ) :
    ∃ θ : Lp ℝ 2 M.P, (θ : Ω → ℝ) =ᵐ[M.P] J T ∧
      (θ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 M.P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (M.B v ω - M.B u ω)) 2 M.P, g = h.toLp _} : Set (Lp ℝ 2 M.P)) ∧
      hH2.toLp _ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
          ∫ z, (hH2.toLp _ : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) := by
  obtain rfl : W = StochCalcBr.W M := funext fun t => funext fun ω => hW t ω
  subst hμ
  obtain ⟨θ, h1, h2⟩ := StochCalcP6.StochCalcZ4mb.Z4m M hM hD0 hD hHm hJ T hH2
  have h3 := (StochCalcP6.StochCalcRU.rep_iff (StochCalcP6.StochCalcO3M.incr_B M hM) T θ _).1 h2
  unfold StochCalcP6.StochCalcRU.RepU at h3
  exact ⟨θ, h1, h3⟩
