-- Prove2me | solution 1 for HedgePSNV.asset_price_riskneutral_martingale
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T20:33:36.411273+00:00
-- url     : https://prove2.me/submissions/c14ab013-3f8f-4fd3-8da9-a14fdcf270a4

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false

-- ===== slice of Solutions.Sol_pv_1558a108 (probe/slice8c/cuts/r_k1.lean.src/Solutions.Sol_pv_1558a108.lean): 82/153 top-level decls kept =====

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


-- ===== slice of __current__ (probe/slice8c/cuts/r_k1.lean.src/__current__.lean): 195/199 top-level decls kept =====

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

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV

lemma I_zero_ae {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : M.I 0 =ᵐ[M.P] fun _ => (0 : ℝ) := by
  obtain ⟨a, -, -, -, hlim⟩ := hM.I_ito.2 0
  have hsum : ∀ n, EthierKurtz.itoStepSum M.B 0 n (a n) = fun _ => (0 : ℝ) := by
    intro n
    funext ω
    unfold EthierKurtz.itoStepSum
    simp
  have h0 : TendstoInMeasure M.P (fun n => EthierKurtz.itoStepSum M.B 0 n (a n)) Filter.atTop
      (fun _ => (0 : ℝ)) := by
    intro ε hε
    simp [hsum, not_le.mpr hε]
  exact tendstoInMeasure_ae_unique hlim h0

/-- `E[Z_T] = 1` (Assumption 5 martingale property and `Z_0 = 1` a.s.). -/
lemma integral_Z_T {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : ∫ ω, M.Z p.T ω ∂M.P = 1 := by
  have := hM.prob
  have hZ0 : M.Z 0 =ᵐ[M.P] fun _ => (1 : ℝ) := by
    filter_upwards [I_zero_ae M hM] with ω hω
    simp [Model.Z, hω]
  have hce := h5.1.2.2 0 p.T zero_le le_rfl
  rw [← integral_condExp (M.F.le 0)]
  rw [integral_congr_ae (hce.trans hZ0)]
  simp

lemma Z_pos {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (t : ℝ≥0) (ω : Ω) :
    0 < M.Z t ω := Real.exp_pos _

lemma Z_T_measurable {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : Measurable (M.Z p.T) :=
  ((h5.1.1 p.T le_rfl).mono (M.F.le p.T)).measurable



end StochCalcHedge

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal

namespace StochCalcDG

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The exponent of one discrete Girsanov step. -/
noncomputable def ex (lam h a x : ℝ) : ℂ :=
  ((-a * x - a ^ 2 * h / 2 : ℝ) : ℂ) + ((lam * x + lam * a * h : ℝ) : ℂ) * I

lemma norm_cexp_ex (lam h a x : ℝ) :
    ‖cexp (ex lam h a x)‖ = Real.exp (-a * x - a ^ 2 * h / 2) := by
  rw [Complex.norm_exp]
  simp only [ex, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

lemma ex_bound {lam h a x R : ℝ} (hh : 0 ≤ h) (ha : |a| ≤ R) :
    ‖cexp (ex lam h a x)‖ ≤ Real.exp (R * x) + Real.exp (-R * x) := by
  rw [norm_cexp_ex]
  have h1 : Real.exp (-a * x - a ^ 2 * h / 2) ≤ Real.exp (-a * x) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg a])
  refine h1.trans ?_
  rcases le_total 0 x with hx | hx
  · have : -a * x ≤ R * x := by nlinarith [neg_abs_le a, abs_nonneg a]
    exact (Real.exp_le_exp.2 this).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have : -a * x ≤ -R * x := by nlinarith [le_abs_self a, abs_nonneg a]
    exact (Real.exp_le_exp.2 this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- Gaussian inner integral of one step. -/
lemma gauss_step (lam a : ℝ) (v : ℝ≥0) :
    ∫ x, cexp (ex lam v a x) ∂(gaussianReal 0 v) = cexp (-((lam : ℂ) ^ 2 * (v : ℝ) / 2)) := by
  have e : (fun x : ℝ => cexp (ex lam v a x)) = fun x : ℝ =>
      cexp (-((a : ℂ) ^ 2 * (v : ℝ) / 2) + lam * a * (v : ℝ) * I) * cexp ((-(a : ℂ) + lam * I) * (x : ℂ)) := by
    funext x
    rw [← Complex.exp_add]
    congr 1
    simp only [ex]
    push_cast
    ring
  rw [e, integral_const_mul]
  have hm := complexMGF_id_gaussianReal (μ := 0) (v := v) (-(a : ℂ) + lam * I)
  simp only [complexMGF, id] at hm
  rw [hm, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_add]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma integrable_exp_gauss (c : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => Real.exp (c * x)) (gaussianReal 0 v) := by
  have := integrable_exp_mul_gaussianReal (μ := 0) (v := v) c
  simpa using this


end StochCalcDG

/-! DG2 (8c066573 relay 7): the Girsanov step with an INTEGRABLE weight, and its iteration along a
discrete filtration `𝒢` with Gaussian increments `D k` independent of `𝒢 k`. Append after DG.lean. -/

namespace StochCalcDG

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- One discrete Girsanov step with an integrable (not necessarily bounded) weight `ξ`. -/
theorem girsanov_step_int {Q : Measure Ω} [IsProbabilityMeasure Q] {a : Ω → ℝ} {ξ : Ω → ℂ}
    {D : Ω → ℝ} (ha : Measurable a) (hξ : Measurable ξ) (hD : Measurable D)
    (hind : IndepFun (fun ω => (a ω, ξ ω)) D Q) {v : ℝ≥0}
    (hlaw : Q.map D = gaussianReal 0 v) {R : ℝ} (haR : ∀ ω, |a ω| ≤ R)
    (hξi : Integrable ξ Q) (lam : ℝ) :
    Integrable (fun ω => ξ ω * cexp (ex lam v (a ω) (D ω))) Q ∧
    ∫ ω, ξ ω * cexp (ex lam v (a ω) (D ω)) ∂Q =
      cexp (-((lam : ℂ) ^ 2 * (v : ℝ) / 2)) * ∫ ω, ξ ω ∂Q := by
  have hh : 0 ≤ (v : ℝ) := v.2
  set U : Ω → ℝ × ℂ := fun ω => (a ω, ξ ω) with hU
  have hUm : Measurable U := ha.prodMk hξ
  have hmap : Q.map (fun ω => (U ω, D ω)) = (Q.map U).prod (Q.map D) :=
    (indepFun_iff_map_prod_eq_prod_map_map hUm.aemeasurable hD.aemeasurable).1 hind
  set F : (ℝ × ℂ) × ℝ → ℂ := fun z => z.1.2 * cexp (ex lam v z.1.1 z.2) with hF
  have hFc : Continuous F := by
    simp only [hF, ex]
    fun_prop
  have hcomp : (fun ω => ξ ω * cexp (ex lam v (a ω) (D ω))) = F ∘ (fun ω => (U ω, D ω)) := rfl
  haveI : IsProbabilityMeasure (Q.map U) := Measure.isProbabilityMeasure_map hUm.aemeasurable
  haveI : IsProbabilityMeasure (Q.map D) := Measure.isProbabilityMeasure_map hD.aemeasurable
  have hbd : ∀ᵐ z ∂(Q.map U).prod (Q.map D),
      ‖F z‖ ≤ ‖z.1.2‖ * (Real.exp (R * z.2) + Real.exp (-R * z.2)) := by
    have hsupp : ∀ᵐ u ∂(Q.map U), |u.1| ≤ R := by
      rw [ae_map_iff hUm.aemeasurable]
      · exact ae_of_all _ fun ω => haR ω
      · exact measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const
    refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
    · exact measurableSet_le (hFc.norm.measurable) (by fun_prop)
    · filter_upwards [hsupp] with u hu
      refine ae_of_all _ fun x => ?_
      simp only [hF]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (ex_bound hh hu) (norm_nonneg _)
  have hgi : Integrable
      (fun z : (ℝ × ℂ) × ℝ => ‖z.1.2‖ * (Real.exp (R * z.2) + Real.exp (-R * z.2)))
      ((Q.map U).prod (Q.map D)) := by
    have h1 : Integrable (fun x : ℝ => Real.exp (R * x) + Real.exp (-R * x)) (Q.map D) := by
      rw [hlaw]
      exact (integrable_exp_gauss R v).add (integrable_exp_gauss (-R) v)
    have h2 : Integrable (fun u : ℝ × ℂ => ‖u.2‖) (Q.map U) :=
      (integrable_map_measure (continuous_norm.comp continuous_snd).aestronglyMeasurable
        hUm.aemeasurable).2 hξi.norm
    exact h2.mul_prod h1
  have hFi : Integrable F ((Q.map U).prod (Q.map D)) :=
    Integrable.mono' hgi hFc.aestronglyMeasurable hbd
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    rw [← hmap] at hFi
    exact (integrable_map_measure hFc.aestronglyMeasurable (hUm.prodMk hD).aemeasurable).1 hFi
  have hlhs : ∫ ω, ξ ω * cexp (ex lam v (a ω) (D ω)) ∂Q =
      ∫ z, F z ∂(Q.map (fun ω => (U ω, D ω))) := by
    rw [integral_map (hUm.prodMk hD).aemeasurable hFc.aestronglyMeasurable]
  rw [hlhs, hmap, integral_prod F hFi]
  have hin : ∀ u : ℝ × ℂ, ∫ x, F (u, x) ∂(Q.map D) =
      u.2 * cexp (-((lam : ℂ) ^ 2 * (v : ℝ) / 2)) := by
    intro u
    simp only [hF]
    rw [integral_const_mul, hlaw, gauss_step lam u.1 v]
  simp_rw [hin]
  rw [integral_mul_const, integral_map hUm.aemeasurable continuous_snd.aestronglyMeasurable,
    mul_comm]

/-- **Iterated discrete Girsanov identity** along a discrete filtration `𝒢`: Gaussian increments
`D k ~ N(0, h k)` independent of `𝒢 k`, `𝒢 (k+1)`-measurable; bounded `𝒢 k`-measurable coefficients;
per-step frequencies `lam k`. -/
theorem girsanov_iter {Q : Measure Ω} [IsProbabilityMeasure Q] (𝒢 : ℕ → MeasurableSpace Ω)
    (h𝒢 : ∀ k, 𝒢 k ≤ mΩ) (hmono : Monotone 𝒢) (a D : ℕ → Ω → ℝ) (h : ℕ → ℝ≥0)
    (ha : ∀ k, Measurable[𝒢 k] (a k)) (hD : ∀ k, Measurable[𝒢 (k + 1)] (D k))
    (hind : ∀ k (U : Ω → ℝ × ℂ), Measurable[𝒢 k] U → IndepFun U (D k) Q)
    (hlaw : ∀ k, Q.map (D k) = gaussianReal 0 (h k)) {R : ℝ} (haR : ∀ k ω, |a k ω| ≤ R)
    (lam : ℕ → ℝ) (ξ : Ω → ℂ) (hξ : Measurable[𝒢 0] ξ) (hξi : Integrable ξ Q) (n : ℕ) :
    Measurable[𝒢 n]
        (fun ω => ξ ω * ∏ k ∈ Finset.range n, cexp (ex (lam k) (h k) (a k ω) (D k ω))) ∧
      Integrable
        (fun ω => ξ ω * ∏ k ∈ Finset.range n, cexp (ex (lam k) (h k) (a k ω) (D k ω))) Q ∧
      ∫ ω, ξ ω * ∏ k ∈ Finset.range n, cexp (ex (lam k) (h k) (a k ω) (D k ω)) ∂Q =
        cexp (-((∑ k ∈ Finset.range n, (lam k : ℂ) ^ 2 * (h k : ℝ)) / 2)) * ∫ ω, ξ ω ∂Q := by
  induction n with
  | zero => simpa using ⟨hξ, hξi⟩
  | succ n ih =>
    obtain ⟨hm, hi, he⟩ := ih
    have hsplit : (fun ω => ξ ω * ∏ k ∈ Finset.range (n + 1),
        cexp (ex (lam k) (h k) (a k ω) (D k ω))) =
        fun ω => (ξ ω * ∏ k ∈ Finset.range n, cexp (ex (lam k) (h k) (a k ω) (D k ω))) *
          cexp (ex (lam n) (h n) (a n ω) (D n ω)) := by
      funext ω
      rw [Finset.prod_range_succ, mul_assoc]
    have hamn : Measurable[𝒢 (n + 1)] (a n) := (ha n).mono (hmono (Nat.le_succ n)) le_rfl
    have hηm' : Measurable[𝒢 (n + 1)]
        (fun ω => ξ ω * ∏ k ∈ Finset.range n, cexp (ex (lam k) (h k) (a k ω) (D k ω))) :=
      hm.mono (hmono (Nat.le_succ n)) le_rfl
    have hc : Continuous (fun p : ℝ × ℝ => cexp (ex (lam n) (h n) p.1 p.2)) := by
      simp only [ex]
      fun_prop
    have hEm : Measurable[𝒢 (n + 1)] (fun ω => cexp (ex (lam n) (h n) (a n ω) (D n ω))) :=
      hc.measurable.comp (hamn.prodMk (hD n))
    have hUm : Measurable[𝒢 n] (fun ω => (a n ω,
        ξ ω * ∏ k ∈ Finset.range n, cexp (ex (lam k) (h k) (a k ω) (D k ω)))) :=
      (ha n).prodMk hm
    have hI : IndepFun (fun ω => (a n ω,
        ξ ω * ∏ k ∈ Finset.range n, cexp (ex (lam k) (h k) (a k ω) (D k ω)))) (D n) Q := by
      exact hind n _ hUm
    obtain ⟨hi2, he2⟩ := girsanov_step_int ((ha n).mono (h𝒢 n) le_rfl) (hm.mono (h𝒢 n) le_rfl)
      ((hD n).mono (h𝒢 (n + 1)) le_rfl) hI (hlaw n) (haR n) hi (lam n)
    rw [hsplit]
    refine ⟨hηm'.mul hEm, hi2, ?_⟩
    rw [he2, he, ← mul_assoc, ← Complex.exp_add, Finset.sum_range_succ]
    congr 2
    ring

/-- **Window form**: frequencies vanish before step `i`; the weight is `1_A`, `A ∈ 𝒢 i`. -/
theorem girsanov_window {Q : Measure Ω} [IsProbabilityMeasure Q] (𝒢 : ℕ → MeasurableSpace Ω)
    (h𝒢 : ∀ k, 𝒢 k ≤ mΩ) (hmono : Monotone 𝒢) (a D : ℕ → Ω → ℝ) (h : ℕ → ℝ≥0)
    (ha : ∀ k, Measurable[𝒢 k] (a k)) (hD : ∀ k, Measurable[𝒢 (k + 1)] (D k))
    (hind : ∀ k (U : Ω → ℝ × ℂ), Measurable[𝒢 k] U → IndepFun U (D k) Q)
    (hlaw : ∀ k, Q.map (D k) = gaussianReal 0 (h k)) {R : ℝ} (haR : ∀ k ω, |a k ω| ≤ R)
    (lam : ℕ → ℝ) {i N : ℕ} (hiN : i ≤ N) (hlam0 : ∀ k < i, lam k = 0)
    {A : Set Ω} (hA : MeasurableSet[𝒢 i] A) :
    ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω *
        ∏ k ∈ Finset.range N, cexp (ex (lam k) (h k) (a k ω) (D k ω)) ∂Q =
      cexp (-((∑ k ∈ Finset.Ico i N, (lam k : ℂ) ^ 2 * (h k : ℝ)) / 2)) *
        ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω *
          ∏ k ∈ Finset.range i, cexp (ex 0 (h k) (a k ω) (D k ω)) ∂Q := by
  obtain ⟨hYm, hYi, -⟩ := girsanov_iter 𝒢 h𝒢 hmono a D h ha hD hind hlaw haR (fun _ => 0)
    (fun _ => (1 : ℂ)) measurable_const (integrable_const _) i
  simp only [one_mul] at hYm hYi
  set Y : Ω → ℂ := fun ω => ∏ k ∈ Finset.range i, cexp (ex 0 (h k) (a k ω) (D k ω)) with hY
  have hξe : (fun ω => A.indicator (fun _ => (1 : ℂ)) ω * Y ω) = A.indicator Y := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have hξm : Measurable[𝒢 i] (fun ω => A.indicator (fun _ => (1 : ℂ)) ω * Y ω) := by
    rw [hξe]
    exact hYm.indicator hA
  have hξi : Integrable (fun ω => A.indicator (fun _ => (1 : ℂ)) ω * Y ω) Q := by
    rw [hξe]
    exact hYi.indicator (h𝒢 i _ hA)
  obtain ⟨-, -, he⟩ := girsanov_iter (fun l => 𝒢 (i + l)) (fun l => h𝒢 _)
    (fun l l' hll' => hmono (by omega)) (fun l => a (i + l)) (fun l => D (i + l)) (fun l => h (i + l))
    (fun l => ha _) (fun l => by rw [← add_assoc]; exact hD _) (fun l U hU => hind _ U hU) (fun l => hlaw _)
    (fun l ω => haR _ ω) (fun l => lam (i + l)) _ (by simpa using hξm) hξi (N - i)
  have hprod : ∀ ω, ∏ k ∈ Finset.range N, cexp (ex (lam k) (h k) (a k ω) (D k ω)) =
      Y ω * ∏ l ∈ Finset.range (N - i), cexp (ex (lam (i + l)) (h (i + l)) (a (i + l) ω) (D (i + l) ω)) := by
    intro ω
    have hN : N = i + (N - i) := by omega
    conv_lhs => rw [hN]
    rw [Finset.prod_range_add]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [hlam0 k (Finset.mem_range.1 hk)]
  simp_rw [hprod, ← mul_assoc]
  rw [he, Finset.sum_Ico_eq_sum_range]

end StochCalcDG

open MeasureTheory Filter Topology

namespace StochCalcDG3p

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem scheffe {Q : Measure Ω} {G : ℕ → Ω → ℝ} {g : Ω → ℝ} (hG0 : ∀ n ω, 0 ≤ G n ω)
    (hGi : ∀ n, Integrable (G n) Q) (hgi : Integrable g Q)
    (hGg : ∀ᵐ ω ∂Q, Tendsto (fun n => G n ω) atTop (𝓝 (g ω)))
    (hint : Tendsto (fun n => ∫ ω, G n ω ∂Q) atTop (𝓝 (∫ ω, g ω ∂Q))) :
    Tendsto (fun n => ∫ ω, |G n ω - g ω| ∂Q) atTop (𝓝 0) := by
  have hg0 : ∀ᵐ ω ∂Q, 0 ≤ g ω := by
    filter_upwards [hGg] with ω hω
    exact ge_of_tendsto' hω fun n => hG0 n ω
  have hpi : ∀ n, Integrable (fun ω => max (g ω - G n ω) 0) Q := fun n =>
    ((hgi.sub (hGi n)).sup (integrable_zero _ _ _))
  have heq : ∀ n, ∫ ω, |G n ω - g ω| ∂Q =
      (∫ ω, G n ω ∂Q - ∫ ω, g ω ∂Q) + 2 * ∫ ω, max (g ω - G n ω) 0 ∂Q := by
    intro n
    have e1 : (fun ω => |G n ω - g ω|) =
        fun ω => (G n ω - g ω) + 2 * max (g ω - G n ω) 0 := by
      funext ω
      rcases le_total (G n ω) (g ω) with h | h
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
        ring
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
        ring
    rw [e1, integral_add (f := fun ω => G n ω - g ω) (g := fun ω => 2 * max (g ω - G n ω) 0)
      ((hGi n).sub hgi) ((hpi n).const_mul 2), integral_sub (hGi n) hgi, integral_const_mul]
  simp_rw [heq]
  have h1 : Tendsto (fun n => ∫ ω, G n ω ∂Q - ∫ ω, g ω ∂Q) atTop (𝓝 0) := by
    have := hint.sub_const (∫ ω, g ω ∂Q)
    simpa using this
  have h2 : Tendsto (fun n => ∫ ω, max (g ω - G n ω) 0 ∂Q) atTop (𝓝 (∫ ω, (0 : ℝ) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence g (fun n => (hpi n).aestronglyMeasurable)
      hgi (fun n => ?_) ?_
    · filter_upwards [hg0] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hG0 n ω]) hω
    · filter_upwards [hGg] with ω hω
      have := (tendsto_const_nhds (x := g ω)).sub hω
      have h3 := this.max (tendsto_const_nhds (x := (0 : ℝ)))
      simpa using h3
  simp only [integral_zero] at h2
  simpa using h1.add (h2.const_mul 2)

theorem tendsto_integral_weighted {Q : Measure Ω} {G : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hG0 : ∀ n ω, 0 ≤ G n ω) (hGi : ∀ n, Integrable (G n) Q) (hgi : Integrable g Q)
    (hGg : ∀ᵐ ω ∂Q, Tendsto (fun n => G n ω) atTop (𝓝 (g ω)))
    (hint : Tendsto (fun n => ∫ ω, G n ω ∂Q) atTop (𝓝 (∫ ω, g ω ∂Q)))
    {e : ℕ → Ω → ℂ} {E : Ω → ℂ} (hem : ∀ n, AEStronglyMeasurable (e n) Q)
    (hEm : AEStronglyMeasurable E Q) (he1 : ∀ n ω, ‖e n ω‖ ≤ 1) (hE1 : ∀ ω, ‖E ω‖ ≤ 1)
    (heE : ∀ᵐ ω ∂Q, Tendsto (fun n => e n ω) atTop (𝓝 (E ω))) :
    Tendsto (fun n => ∫ ω, (G n ω : ℂ) * e n ω ∂Q) atTop (𝓝 (∫ ω, (g ω : ℂ) * E ω ∂Q)) := by
  have hc : ∀ {f : Ω → ℝ}, Integrable f Q → AEStronglyMeasurable (fun ω => (f ω : ℂ)) Q :=
    fun hf => Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hI1 : ∀ n, Integrable (fun ω => ((G n ω - g ω : ℝ) : ℂ) * e n ω) Q := fun n =>
    Integrable.mono' ((hGi n).sub hgi).norm ((hc ((hGi n).sub hgi)).mul (hem n))
      (ae_of_all _ fun ω => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_of_le_one_right (norm_nonneg _) (he1 n ω))
  have hI2 : ∀ n, Integrable (fun ω => (g ω : ℂ) * (e n ω - E ω)) Q := fun n =>
    Integrable.mono' (hgi.norm.const_mul 2) ((hc hgi).mul ((hem n).sub hEm))
      (ae_of_all _ fun ω => by
        show ‖(g ω : ℂ) * (e n ω - E ω)‖ ≤ 2 * ‖g ω‖
        rw [norm_mul, Complex.norm_real, mul_comm 2]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [he1 n ω, hE1 ω]))
  have hsplit : ∀ n, ∫ ω, (G n ω : ℂ) * e n ω ∂Q - ∫ ω, (g ω : ℂ) * E ω ∂Q =
      ∫ ω, ((G n ω - g ω : ℝ) : ℂ) * e n ω ∂Q + ∫ ω, (g ω : ℂ) * (e n ω - E ω) ∂Q := by
    intro n
    have hA : Integrable (fun ω => (G n ω : ℂ) * e n ω) Q :=
      Integrable.mono' (hGi n).norm ((hc (hGi n)).mul (hem n)) (ae_of_all _ fun ω => by
        show ‖(G n ω : ℂ) * e n ω‖ ≤ ‖G n ω‖
        rw [norm_mul, Complex.norm_real]
        exact mul_le_of_le_one_right (norm_nonneg _) (he1 n ω))
    have hB : Integrable (fun ω => (g ω : ℂ) * E ω) Q :=
      Integrable.mono' hgi.norm ((hc hgi).mul hEm) (ae_of_all _ fun ω => by
        show ‖(g ω : ℂ) * E ω‖ ≤ ‖g ω‖
        rw [norm_mul, Complex.norm_real]
        exact mul_le_of_le_one_right (norm_nonneg _) (hE1 ω))
    rw [← integral_sub hA hB, ← integral_add (hI1 n) (hI2 n)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    push_cast
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hS := scheffe hG0 hGi hgi hGg hint
  have hD : Tendsto (fun n => ∫ ω, (g ω : ℂ) * (e n ω - E ω) ∂Q) atTop
      (𝓝 (∫ ω, (0 : ℂ) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => 2 * ‖g ω‖)
      (fun n => (hI2 n).aestronglyMeasurable) (hgi.norm.const_mul 2) (fun n => ?_) ?_
    · refine ae_of_all _ fun ω => ?_
      rw [norm_mul, Complex.norm_real, mul_comm 2]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by linarith [he1 n ω, hE1 ω])
    · filter_upwards [heE] with ω hω
      have := (hω.sub_const (E ω)).const_mul (g ω : ℂ)
      simpa using this
  simp only [integral_zero] at hD
  refine squeeze_zero (g := fun n => ∫ ω, |G n ω - g ω| ∂Q +
      ‖∫ ω, (g ω : ℂ) * (e n ω - E ω) ∂Q‖) (fun n => norm_nonneg _) (fun n => ?_) ?_
  · rw [hsplit n]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (ae_of_all _ fun ω => norm_nonneg _) (((hGi n).sub hgi).abs) (ae_of_all _ fun ω => ?_))
    show ‖((G n ω - g ω : ℝ) : ℂ) * e n ω‖ ≤ |G n ω - g ω|
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (he1 n ω)
  · simpa using hS.add (tendsto_norm_zero.comp hD)

/-- Left Riemann sums of a continuous function on uniform partitions of `[u, u + L]`. -/
theorem riemann_left {g : ℝ → ℝ} (hg : Continuous g) (u : ℝ) {L : ℝ} (hL : 0 ≤ L)
    {m : ℕ → ℕ} {δ : ℕ → ℝ} (hδ0 : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hmδ : ∀ n, (m n : ℝ) * δ n = L) :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), g (u + k * δ n) * δ n) atTop
      (𝓝 (∫ x in u..u + L, g x)) := by
  have huc : UniformContinuousOn g (Set.Icc u (u + L)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, hdg⟩ := huc (ε / (2 * (L + 1))) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hδ) d hd
  refine ⟨N, fun n hn => ?_⟩
  have hδn : δ n < d := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (hδ0 n)] at this
    exact this
  set c : ℕ → ℝ := fun k => u + k * δ n with hc
  have hadj : ∑ k ∈ Finset.range (m n), ∫ x in c k..c (k + 1), g x = ∫ x in u..u + L, g x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals]
    · simp only [hc, Nat.cast_zero, zero_mul, add_zero]
      rw [hmδ n]
    · intro k _
      exact hg.intervalIntegrable _ _
  rw [Real.dist_eq, ← hadj, ← Finset.sum_sub_distrib]
  have hcell : ∀ k ∈ Finset.range (m n),
      |g (u + k * δ n) * δ n - ∫ x in c k..c (k + 1), g x| ≤ ε / (2 * (L + 1)) * δ n := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ m n := by exact_mod_cast Finset.mem_range.1 hk
    have hck : c (k + 1) = c k + δ n := by simp only [hc]; push_cast; ring
    have hcst : g (u + k * δ n) * δ n = ∫ x in c k..c (k + 1), g (u + k * δ n) := by
      rw [intervalIntegral.integral_const, hck, smul_eq_mul]
      ring
    rw [hcst, ← intervalIntegral.integral_sub intervalIntegrable_const (hg.intervalIntegrable _ _)]
    have hle : ‖∫ x in c k..c (k + 1), (g (u + k * δ n) - g x)‖ ≤
        ε / (2 * (L + 1)) * |c (k + 1) - c k| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      have hlo : c k ≤ c (k + 1) := by rw [hck]; linarith [hδ0 n]
      rw [Set.uIoc_of_le hlo] at hx
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hmem1 : u + k * δ n ∈ Set.Icc u (u + L) := by
        constructor
        · nlinarith [hδ0 n]
        · rw [← hmδ n]; nlinarith [hδ0 n]
      have hmem2 : x ∈ Set.Icc u (u + L) := by
        constructor
        · have : c k = u + k * δ n := rfl
          nlinarith [hδ0 n, hx.1]
        · have h2 : x ≤ c (k + 1) := hx.2
          rw [hck] at h2
          simp only [hc] at h2
          rw [← hmδ n]; nlinarith [hδ0 n]
      have hdist : dist (u + k * δ n) x ≤ d := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
          have : c k = u + k * δ n := rfl
          linarith [hx.1])]
        have h2 : x ≤ c (k + 1) := hx.2
        rw [hck] at h2
        simp only [hc] at h2
        linarith
      have := hdg _ hmem1 _ hmem2 hdist
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this
    rw [Real.norm_eq_abs, hck, add_sub_cancel_left, abs_of_pos (hδ0 n)] at hle
    rw [hck]
    exact hle
  calc |∑ k ∈ Finset.range (m n), (g (u + k * δ n) * δ n - ∫ x in c k..c (k + 1), g x)|
      ≤ ∑ k ∈ Finset.range (m n), |g (u + k * δ n) * δ n - ∫ x in c k..c (k + 1), g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m n), ε / (2 * (L + 1)) * δ n := Finset.sum_le_sum hcell
    _ = ε / (2 * (L + 1)) * L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hmδ n]
        ring
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

end StochCalcDG3p

/-! DG3m (8c066573 relay 7): discrete Girsanov on the dyadic `T`-grid of the model.
Append after Br + S8 + DG + DG2_tail + DG3p (dev file probe/8c066573_DG3m.lean). -/

namespace StochCalcDG3m

open HedgePSNV EthierKurtz ItoLib StochCalcBr StochCalcDG Finset Complex

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Dyadic grid point `k T / 2^n` (the grid of `itoStepSum`). -/
noncomputable def tg (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) * T / (2 : ℝ≥0) ^ n

lemma tg_mono (T : ℝ≥0) (n : ℕ) : Monotone (tg T n) := by
  intro i j hij
  unfold tg
  gcongr

lemma B_measF' (M : Model p Ω) (hM : M.Standing) {r s : ℝ≥0} (hr : r ≤ s) :
    Measurable[M.F s] (M.B r) := by
  have h : MeasurableSpace.comap (fun ω => (M.B r ω, M.Bt r ω)) inferInstance ≤ M.F s := by
    rw [hM.filtF s]
    exact le_sup_of_le_left (le_iSup₂_of_le r hr le_rfl)
  exact measurable_fst.comp (Measurable.of_comap_le h)

lemma G_le_F' (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : M.G t ≤ M.F t := by
  rw [hM.filtG t, hM.filtF t]
  refine sup_le_sup_right (iSup₂_mono fun s _ => ?_) _
  have h : M.B s = Prod.fst ∘ (fun ω => (M.B s ω, M.Bt s ω)) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le

lemma η_measF (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    StronglyMeasurable[M.F s] (M.η s) := by
  have h1 := (hM.μ_adapted s).mono (G_le_F' M hM s)
  have h2 := (hM.σ_adapted s).mono (G_le_F' M hM s)
  exact h1.div h2

/-- Brownian increment on the `k`-th cell. -/
noncomputable def Dn (M : Model p Ω) (n k : ℕ) (ω : Ω) : ℝ :=
  M.B (tg p.T n (k + 1)) ω - M.B (tg p.T n k) ω

/-- Clamped left-point coefficient (the ItoLib `leftCoef (clampH η n) T n k`). -/
noncomputable def an (M : Model p Ω) (n k : ℕ) (ω : Ω) : ℝ := clampH M.η n (tg p.T n k) ω

/-- Cell variance. -/
noncomputable def hn (p : Params) (n k : ℕ) : ℝ≥0 :=
  nndist (tg p.T n (k + 1)).1 (tg p.T n k).1

lemma Dn_law (M : Model p Ω) (hM : M.Standing) (n k : ℕ) :
    M.P.map (Dn M n k) = gaussianReal 0 (hn p n k) :=
  (hM.brownB.toIsPreBrownianReal.hasLaw_sub _ _).map_eq

lemma Dn_meas (M : Model p Ω) (hM : M.Standing) (n k : ℕ) :
    Measurable[M.F (tg p.T n (k + 1))] (Dn M n k) :=
  (B_measF' M hM le_rfl).sub (B_measF' M hM (tg_mono _ _ (Nat.le_succ k)))

lemma an_meas (M : Model p Ω) (hM : M.Standing) (n k : ℕ) :
    Measurable[M.F (tg p.T n k)] (an M n k) :=
  clampH_measurable (η_measF M hM _).measurable _

lemma an_bdd (M : Model p Ω) (n k : ℕ) (ω : Ω) : |an M n k ω| ≤ n :=
  abs_clampH_le M.η (Nat.cast_nonneg n) _ ω

lemma Dn_indep (M : Model p Ω) (hM : M.Standing) (n k : ℕ) (U : Ω → ℝ × ℂ)
    (hU : Measurable[M.F (tg p.T n k)] U) : IndepFun U (Dn M n k) M.P := by
  have hW := isStandardBrownian M hM
  have hsh : tg p.T n k + (tg p.T n (k + 1) - tg p.T n k) = tg p.T n (k + 1) :=
    add_tsub_cancel_of_le (tg_mono _ _ (Nat.le_succ k))
  have hUc : Measurable[completedBrownianPast M.P (W M) (fun _ => 0) (tg p.T n k)] U :=
    hU.mono (F_le_cBP M hM _) le_rfl
  have h1 : IndepFun U (fun ω => W M (tg p.T n k + (tg p.T n (k + 1) - tg p.T n k)) ω 0 -
      W M (tg p.T n k) ω 0) M.P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
      (stdBrownian_indep_completedPast hW 0 (tg p.T n k)) hUc.comap_le) ?_
    have hm : Measurable[MeasurableSpace.comap
        (fun ω (q : ℝ≥0 × Fin 2) => W M (tg p.T n k + q.1) ω q.2 - W M (tg p.T n k) ω q.2)
          inferInstance]
        (fun ω => W M (tg p.T n k + (tg p.T n (k + 1) - tg p.T n k)) ω 0 -
          W M (tg p.T n k) ω 0) := by
      have := (measurable_pi_apply ((tg p.T n (k + 1) - tg p.T n k), (0 : Fin 2)) :
          Measurable fun f : ℝ≥0 × Fin 2 → ℝ => f ((tg p.T n (k + 1) - tg p.T n k), 0)).comp
        (comap_measurable (fun ω (q : ℝ≥0 × Fin 2) =>
          W M (tg p.T n k + q.1) ω q.2 - W M (tg p.T n k) ω q.2))
      exact this
    exact hm.comap_le
  refine h1.congr (ae_of_all _ fun _ => rfl) ?_
  filter_upwards [ae_W M hM] with ω hω
  have hω0 : ∀ t, W M t ω 0 = M.B t ω := fun t => (hω t).1
  simp only [Dn, hsh, hω0]

/-- **Discrete Girsanov identity on the model grid**: frequency `lam` on the cells `[i, j)`. -/
theorem discrete_identity (M : Model p Ω) (hM : M.Standing) (n i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ 2 ^ n) {A : Set Ω} (hA : MeasurableSet[M.F (tg p.T n i)] A) (lam : ℝ) :
    ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω * ∏ k ∈ range (2 ^ n),
        cexp (ex (if i ≤ k ∧ k < j then lam else 0) (hn p n k) (an M n k ω) (Dn M n k ω)) ∂M.P =
      cexp (-((∑ k ∈ Ico i j, (lam : ℂ) ^ 2 * (hn p n k : ℝ)) / 2)) *
      ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω * ∏ k ∈ range (2 ^ n),
        cexp (ex 0 (hn p n k) (an M n k ω) (Dn M n k ω)) ∂M.P := by
  haveI := hM.prob
  have hw := fun (lam' : ℕ → ℝ) (h0 : ∀ k < i, lam' k = 0) =>
    girsanov_window (fun k => M.F (tg p.T n k)) (fun k => M.F.le _)
      (fun a b hab => M.F.mono (tg_mono _ _ hab)) (an M n) (Dn M n) (hn p n)
      (fun k => an_meas M hM n k) (fun k => Dn_meas M hM n k)
      (fun k U hU => Dn_indep M hM n k U hU) (fun k => Dn_law M hM n k)
      (fun k ω => an_bdd M n k ω) lam' (le_trans hij hj) h0 hA
  have e1 := hw (fun k => if i ≤ k ∧ k < j then lam else 0)
    (fun k hk => if_neg (by omega))
  have e2 := hw (fun _ => 0) (fun _ _ => rfl)
  beta_reduce at e1 e2
  rw [e1, e2, ← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← Finset.sum_Ico_consecutive _ hij hj]
  have h2 : ∑ k ∈ Ico j (2 ^ n),
      (((if i ≤ k ∧ k < j then lam else 0 : ℝ)) : ℂ) ^ 2 * (hn p n k : ℝ) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [Finset.mem_Ico] at hk
      rw [if_neg (by omega)]
      simp
  have h1 : ∑ k ∈ Ico i j, (((if i ≤ k ∧ k < j then lam else 0 : ℝ)) : ℂ) ^ 2 * (hn p n k : ℝ) =
      ∑ k ∈ Ico i j, (lam : ℂ) ^ 2 * (hn p n k : ℝ) :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_Ico] at hk
      rw [if_pos (by omega)]
  rw [h2, h1]
  simp

/-- Product of step exponentials = density factor times a unimodular phase. -/
lemma prod_ex (s : Finset ℕ) (lam : ℕ → ℝ) (h : ℕ → ℝ≥0) (a D : ℕ → ℝ) :
    ∏ k ∈ s, cexp (ex (lam k) (h k) (a k) (D k)) =
      (Real.exp (∑ k ∈ s, (-a k * D k - a k ^ 2 * (h k : ℝ) / 2)) : ℂ) *
        cexp ((∑ k ∈ s, lam k * (D k + a k * (h k : ℝ)) : ℝ) * I) := by
  rw [← Complex.exp_sum, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [ex]
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => by ring)
    (congrArg (· * I) (Finset.sum_congr rfl fun k _ => by ring))

end StochCalcDG3m
/-! DG3n (8c066573 relay 8): Part B, the limit `n → ∞` of the discrete Girsanov identity.
Append after DG3m_tail (dev file probe/8c066573_DG3n.lean). -/

namespace StochCalcDG3m

open HedgePSNV EthierKurtz ItoLib StochCalcBr StochCalcDG StochCalcDG3p Finset Complex
open MeasureTheory Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma tg_coe (T : ℝ≥0) (n k : ℕ) : (tg T n k : ℝ) = k * ((T : ℝ) / 2 ^ n) := by
  unfold tg; push_cast; ring

lemma tg_scale (T : ℝ≥0) (N r i : ℕ) : tg T (N + r) (i * 2 ^ r) = tg T N i := by
  apply NNReal.eq
  rw [tg_coe, tg_coe, pow_add]
  push_cast
  field_simp
  try ring

lemma tg_le_T (T : ℝ≥0) {n k : ℕ} (hk : k ≤ 2 ^ n) : tg T n k ≤ T := by
  rw [← NNReal.coe_le_coe, tg_coe]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hk' : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
  rw [mul_div_assoc', div_le_iff₀ h2]
  nlinarith [mul_le_mul_of_nonneg_right hk' (NNReal.coe_nonneg T)]

lemma hn_coe (p : Params) (n k : ℕ) :
    (hn p n k : ℝ) = (tg p.T n (k + 1) : ℝ) - tg p.T n k := by
  unfold hn
  rw [coe_nndist, Real.dist_eq]
  exact abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (tg_mono _ _ (Nat.le_succ k))))

lemma hn_val (p : Params) (n k : ℕ) : (hn p n k : ℝ) = (p.T : ℝ) / 2 ^ n := by
  rw [hn_coe, tg_coe, tg_coe]; push_cast; ring

lemma sum_Ico_tele (f : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) :
    ∑ k ∈ Ico i j, (f (k + 1) - f k) = f j - f i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih => rw [Finset.sum_Ico_succ_top hij, ih]; ring

lemma window_sum (lam : ℝ) (X : ℕ → ℝ) {i j m : ℕ} (hj : j ≤ m) :
    ∑ k ∈ range m, (if i ≤ k ∧ k < j then lam else 0) * X k = lam * ∑ k ∈ Ico i j, X k := by
  rw [Finset.mul_sum]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨by omega, h⟩

/-- Discrete density `exp(Σ -a D - a² h / 2)` on the level-`n` grid. -/
noncomputable def Zn (M : Model p Ω) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ k ∈ range (2 ^ n),
    (-an M n k ω * Dn M n k ω - an M n k ω ^ 2 * (hn p n k : ℝ) / 2))

/-- Discrete `B^M` increment on the cells `[i, j)`. -/
noncomputable def thn (M : Model p Ω) (n i j : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Ico i j, (Dn M n k ω + an M n k ω * (hn p n k : ℝ))

/-- Clamped left-point Ito sum. -/
noncomputable def Sn (M : Model p Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range (2 ^ n), an M n k ω * Dn M n k ω

/-- Continuum version of `B^M` (same body as `G1.BM`). -/
noncomputable def BMx (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M.B t ω + ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω

lemma Zn_nonneg (M : Model p Ω) (n : ℕ) (ω : Ω) : 0 ≤ Zn M n ω := (Real.exp_pos _).le

theorem ident_n (M : Model p Ω) (hM : M.Standing) (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ 2 ^ n)
    {A : Set Ω} (hA : MeasurableSet[M.F (tg p.T n i)] A) (lam : ℝ) :
    ∫ ω, (Zn M n ω : ℂ) * (A.indicator (fun _ => (1 : ℂ)) ω *
        cexp ((lam * thn M n i j ω : ℝ) * I)) ∂M.P =
      cexp (-((lam : ℂ) ^ 2 * ((tg p.T n j : ℝ) - tg p.T n i) / 2)) *
      ∫ ω, (Zn M n ω : ℂ) * A.indicator (fun _ => (1 : ℂ)) ω ∂M.P := by
  have h := discrete_identity M hM n i j hij hj hA lam
  have e1 : ∀ ω, A.indicator (fun _ => (1 : ℂ)) ω * ∏ k ∈ range (2 ^ n),
        cexp (ex (if i ≤ k ∧ k < j then lam else 0) (hn p n k) (an M n k ω) (Dn M n k ω)) =
      (Zn M n ω : ℂ) * (A.indicator (fun _ => (1 : ℂ)) ω *
        cexp ((lam * thn M n i j ω : ℝ) * I)) := by
    intro ω
    have hp := prod_ex (range (2 ^ n)) (fun k => if i ≤ k ∧ k < j then lam else 0) (hn p n)
      (fun k => an M n k ω) (fun k => Dn M n k ω)
    have hw := window_sum lam (fun k => Dn M n k ω + an M n k ω * (hn p n k : ℝ)) (i := i) hj
    beta_reduce at hp hw
    rw [hp, hw]
    simp only [Zn, thn]
    ring
  have e0 : ∀ ω, A.indicator (fun _ => (1 : ℂ)) ω * ∏ k ∈ range (2 ^ n),
        cexp (ex 0 (hn p n k) (an M n k ω) (Dn M n k ω)) =
      (Zn M n ω : ℂ) * A.indicator (fun _ => (1 : ℂ)) ω := by
    intro ω
    have hp := prod_ex (range (2 ^ n)) (fun _ => 0) (hn p n)
      (fun k => an M n k ω) (fun k => Dn M n k ω)
    beta_reduce at hp
    rw [hp]
    simp only [Zn, zero_mul, Finset.sum_const_zero, ofReal_zero, Complex.exp_zero, mul_one]
    ring
  simp_rw [e1, e0] at h
  have hs0 : ∑ k ∈ Ico i j, (hn p n k : ℝ) = (tg p.T n j : ℝ) - tg p.T n i := by
    rw [← sum_Ico_tele (fun k => (tg p.T n k : ℝ)) hij]
    exact Finset.sum_congr rfl fun k _ => hn_coe p n k
  have hs : ∑ k ∈ Ico i j, (lam : ℂ) ^ 2 * (hn p n k : ℝ) =
      (lam : ℂ) ^ 2 * ((tg p.T n j : ℝ) - tg p.T n i) := by
    rw [← Finset.mul_sum]
    congr 1
    exact_mod_cast hs0
  rw [h, hs]

lemma Zn_int (M : Model p Ω) (hM : M.Standing) (n : ℕ) :
    Integrable (Zn M n) M.P ∧ ∫ ω, Zn M n ω ∂M.P = 1 := by
  haveI := hM.prob
  obtain ⟨-, hi, he⟩ := girsanov_iter (fun k => M.F (tg p.T n k)) (fun k => M.F.le _)
      (fun a b hab => M.F.mono (tg_mono _ _ hab)) (an M n) (Dn M n) (hn p n)
      (fun k => an_meas M hM n k) (fun k => Dn_meas M hM n k)
      (fun k U hU => Dn_indep M hM n k U hU) (fun k => Dn_law M hM n k)
      (fun k ω => an_bdd M n k ω) (fun _ => 0) (fun _ => (1 : ℂ)) measurable_const
      (integrable_const _) (2 ^ n)
  have hZ : ∀ ω, (1 : ℂ) * ∏ k ∈ range (2 ^ n),
      cexp (ex 0 (hn p n k) (an M n k ω) (Dn M n k ω)) = (Zn M n ω : ℂ) := by
    intro ω
    have hp := prod_ex (range (2 ^ n)) (fun _ => 0) (hn p n)
      (fun k => an M n k ω) (fun k => Dn M n k ω)
    beta_reduce at hp
    rw [one_mul, hp]
    simp only [Zn, zero_mul, Finset.sum_const_zero, ofReal_zero, Complex.exp_zero, mul_one]
  beta_reduce at hi he
  simp_rw [hZ] at hi he
  refine ⟨by simpa using hi.re, ?_⟩
  have h2 : ((∫ ω, Zn M n ω ∂M.P : ℝ) : ℂ) = 1 := by
    rw [← _root_.integral_complex_ofReal, he]
    simp
  exact_mod_cast h2

lemma Zn_integral (M : Model p Ω) (hM : M.Standing) (n : ℕ) : ∫ ω, Zn M n ω ∂M.P = 1 :=
  (Zn_int M hM n).2

lemma η_cont' (M : Model p Ω) (hM : M.Standing) (ω : Ω) : Continuous (fun t => M.η t ω) := by
  unfold Model.η
  exact (hM.μ_cont ω).div (hM.σ_cont ω) (fun t => (hM.σ_pos t ω).ne')

lemma η_bdd (M : Model p Ω) (hM : M.Standing) (ω : Ω) :
    ∃ C : ℝ, ∀ s ≤ p.T, |M.η s ω| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := p.T)).exists_bound_of_continuousOn
    (η_cont' M hM ω).continuousOn
  exact ⟨C, fun s hs => by simpa [Real.norm_eq_abs] using hC s ⟨zero_le, hs⟩⟩

lemma an_eventually (M : Model p Ω) (hM : M.Standing) (ω : Ω) :
    ∀ᶠ n in atTop, ∀ k ≤ 2 ^ n, an M n k ω = M.η (tg p.T n k) ω := by
  obtain ⟨C, hC⟩ := η_bdd M hM ω
  obtain ⟨n0, hn0⟩ := exists_nat_ge C
  filter_upwards [eventually_ge_atTop n0] with n hn' k hk
  exact clampH_eq_of_abs_le M.η
    ((hC _ (tg_le_T p.T hk)).trans (hn0.trans (by exact_mod_cast hn')))

lemma R_tendsto (M : Model p Ω) (hM : M.Standing) (ω : Ω) :
    Tendsto (fun n => ∑ k ∈ range (2 ^ n), an M n k ω ^ 2 * (hn p n k : ℝ)) atTop
      (𝓝 (∫ u in (0 : ℝ)..(p.T : ℝ), M.η u.toNNReal ω ^ 2)) := by
  have hg : Continuous fun x : ℝ => M.η x.toNNReal ω ^ 2 :=
    ((η_cont' M hM ω).comp continuous_real_toNNReal).pow 2
  have hT : (0 : ℝ) < p.T := NNReal.coe_pos.mpr p.hT
  have hδ0 : ∀ n : ℕ, 0 < (p.T : ℝ) / 2 ^ n := fun n => div_pos hT (by positivity)
  have hδ : Tendsto (fun n : ℕ => (p.T : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hmδ : ∀ n : ℕ, ((2 ^ n : ℕ) : ℝ) * ((p.T : ℝ) / 2 ^ n) = p.T := fun n => by
    push_cast; field_simp
  have hR := riemann_left hg 0 hT.le (m := fun n => 2 ^ n) hδ0 hδ hmδ
  beta_reduce at hR
  rw [zero_add] at hR
  refine hR.congr' ?_
  filter_upwards [an_eventually M hM ω] with n hev
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hev k (Finset.mem_range.mp hk).le, hn_val, zero_add, ← tg_coe, Real.toNNReal_coe]

lemma window_tendsto (M : Model p Ω) (hM : M.Standing) (ω : Ω) (N i0 j0 : ℕ) (hij : i0 ≤ j0)
    (hj : j0 ≤ 2 ^ N) :
    Tendsto (fun r => ∑ k ∈ Ico (i0 * 2 ^ r) (j0 * 2 ^ r),
        an M (N + r) k ω * (hn p (N + r) k : ℝ)) atTop
      (𝓝 (∫ x in (tg p.T N i0 : ℝ)..(tg p.T N j0 : ℝ), M.η x.toNNReal ω)) := by
  have hg : Continuous fun x : ℝ => M.η x.toNNReal ω :=
    (η_cont' M hM ω).comp continuous_real_toNNReal
  have hT : (0 : ℝ) < p.T := NNReal.coe_pos.mpr p.hT
  have hL : (0 : ℝ) ≤ (tg p.T N j0 : ℝ) - tg p.T N i0 :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr (tg_mono _ _ hij))
  have hsh : Tendsto (fun r : ℕ => N + r) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun r hr => by omega⟩
  have hδ0 : ∀ r : ℕ, 0 < (p.T : ℝ) / 2 ^ (N + r) := fun r => div_pos hT (by positivity)
  have hδ : Tendsto (fun r : ℕ => (p.T : ℝ) / 2 ^ (N + r)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp hsh)
  have hmδ : ∀ r : ℕ, (((j0 - i0) * 2 ^ r : ℕ) : ℝ) * ((p.T : ℝ) / 2 ^ (N + r)) =
      (tg p.T N j0 : ℝ) - tg p.T N i0 := by
    intro r
    rw [tg_coe, tg_coe, Nat.cast_mul, Nat.cast_sub hij, pow_add]
    push_cast
    field_simp
    try ring
  have hR := riemann_left hg (tg p.T N i0 : ℝ) hL (m := fun r => (j0 - i0) * 2 ^ r) hδ0 hδ hmδ
  beta_reduce at hR
  rw [add_sub_cancel] at hR
  refine hR.congr' ?_
  filter_upwards [hsh.eventually (an_eventually M hM ω)] with r hev
  rw [Finset.sum_Ico_eq_sum_range, ← Nat.sub_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : i0 * 2 ^ r + k ≤ 2 ^ (N + r) := by
    calc i0 * 2 ^ r + k ≤ i0 * 2 ^ r + (j0 - i0) * 2 ^ r :=
          Nat.add_le_add_left (Finset.mem_range.mp hk).le _
      _ = j0 * 2 ^ r := by rw [← Nat.add_mul, Nat.add_sub_cancel' hij]
      _ ≤ 2 ^ N * 2 ^ r := Nat.mul_le_mul_right _ hj
      _ = 2 ^ (N + r) := (pow_add 2 N r).symm
  have ht : (tg p.T N i0 : ℝ) + k * ((p.T : ℝ) / 2 ^ (N + r)) =
      (tg p.T (N + r) (i0 * 2 ^ r + k) : ℝ) := by
    rw [← tg_scale p.T N r i0, tg_coe, tg_coe]; push_cast; ring
  rw [hev _ hk', hn_val, ht, Real.toNNReal_coe]

lemma S_inmeas (M : Model p Ω) (hM : M.Standing) :
    TendstoInMeasure M.P (fun n => Sn M n) atTop (M.I p.T) := by
  have h := clampLeft_tendsto_of_hasBrownianItoIntegral (isStandardBrownian M hM) 0 0
    (meas_cBP_of_F M hM (η_measF M hM)) (η_cont' M hM) (hasIto_B M hM hM.I_ito) p.T
  refine h.congr_left fun n => ?_
  filter_upwards [ae_W M hM] with ω hω
  have hω0 : ∀ t, W M t ω 0 = M.B t ω := fun t => (hω t).1
  unfold itoStepSum Sn
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [leftCoef, dyTime, hω0, an, Dn, tg, Nat.cast_add, Nat.cast_one]

lemma Zn_eq (M : Model p Ω) (n : ℕ) (ω : Ω) :
    Zn M n ω = Real.exp (-(Sn M n ω) -
      (1 / 2) * ∑ k ∈ range (2 ^ n), an M n k ω ^ 2 * (hn p n k : ℝ)) := by
  unfold Zn Sn
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Girsanov on dyadic windows**: under `Z_T · P`, the increment `B^M v - B^M u` has the
`N(0, v-u)` characteristic function against `F_u`-events. -/
theorem girsanov_dyadic (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (N i0 j0 : ℕ) (hij : i0 ≤ j0) (hj : j0 ≤ 2 ^ N) {A : Set Ω}
    (hA : MeasurableSet[M.F (tg p.T N i0)] A) (lam : ℝ) :
    ∫ ω, (M.Z p.T ω : ℂ) * (A.indicator (fun _ => (1 : ℂ)) ω *
        cexp ((lam * (BMx M (tg p.T N j0) ω - BMx M (tg p.T N i0) ω) : ℝ) * I)) ∂M.P =
      cexp (-((lam : ℂ) ^ 2 * ((tg p.T N j0 : ℝ) - tg p.T N i0) / 2)) *
      ∫ ω, (M.Z p.T ω : ℂ) * A.indicator (fun _ => (1 : ℂ)) ω ∂M.P := by
  haveI := hM.prob
  have hsh : Tendsto (fun r : ℕ => N + r) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun r hr => by omega⟩
  have hSm : TendstoInMeasure M.P (fun r => Sn M (N + r)) atTop (M.I p.T) :=
    fun ε hε => ((S_inmeas M hM) ε hε).comp hsh
  obtain ⟨ns, hns, hnsae⟩ := hSm.exists_seq_tendsto_ae
  have hns' : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hZT : Integrable (M.Z p.T) M.P := (h5.2 p.T le_rfl).integrable one_le_two
  have hZ1 := StochCalcHedge.integral_Z_T M hM h5
  have hGg : ∀ᵐ ω ∂M.P, Tendsto (fun r => Zn M (N + ns r) ω) atTop (𝓝 (M.Z p.T ω)) := by
    filter_upwards [hnsae] with ω hω
    have hR := (R_tendsto M hM ω).comp (hsh.comp hns')
    simp only [Zn_eq, Model.Z]
    exact (Real.continuous_exp.tendsto _).comp (hω.neg.sub (hR.const_mul (1 / 2)))
  have hint : Tendsto (fun r => ∫ ω, Zn M (N + ns r) ω ∂M.P) atTop
      (𝓝 (∫ ω, M.Z p.T ω ∂M.P)) := by
    rw [hZ1]
    simp only [Zn_integral M hM]
    exact tendsto_const_nhds
  have hAm : MeasurableSet A := M.F.le _ _ hA
  have hindm : Measurable (A.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hAm
  have hind1 : ∀ ω, ‖A.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [h]
  have hthm : ∀ n i j, Measurable (thn M n i j) := by
    intro n i j
    unfold thn
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((Dn_meas M hM n k).mono (M.F.le _) le_rfl).add
      (((an_meas M hM n k).mono (M.F.le _) le_rfl).mul measurable_const)
  have hth : ∀ ω, Tendsto (fun r => thn M (N + r) (i0 * 2 ^ r) (j0 * 2 ^ r) ω) atTop
      (𝓝 (BMx M (tg p.T N j0) ω - BMx M (tg p.T N i0) ω)) := by
    intro ω
    have hW := window_tendsto M hM ω N i0 j0 hij hj
    have hD : ∀ r, ∑ k ∈ Ico (i0 * 2 ^ r) (j0 * 2 ^ r), Dn M (N + r) k ω =
        M.B (tg p.T N j0) ω - M.B (tg p.T N i0) ω := by
      intro r
      rw [← tg_scale p.T N r j0, ← tg_scale p.T N r i0]
      exact sum_Ico_tele (fun k => M.B (tg p.T (N + r) k) ω) (Nat.mul_le_mul_right _ hij)
    have hg : Continuous fun x : ℝ => M.η x.toNNReal ω :=
      (η_cont' M hM ω).comp continuous_real_toNNReal
    have hsub := intervalIntegral.integral_interval_sub_left
      (hg.intervalIntegrable (μ := volume) 0 (tg p.T N j0 : ℝ))
      (hg.intervalIntegrable (μ := volume) 0 (tg p.T N i0 : ℝ))
    have hBM : BMx M (tg p.T N j0) ω - BMx M (tg p.T N i0) ω =
        (M.B (tg p.T N j0) ω - M.B (tg p.T N i0) ω) +
          ∫ x in (tg p.T N i0 : ℝ)..(tg p.T N j0 : ℝ), M.η x.toNNReal ω := by
      unfold BMx
      rw [← hsub]
      ring
    rw [hBM]
    simp only [thn, Finset.sum_add_distrib, hD]
    exact tendsto_const_nhds.add hW
  have hexp1 : ∀ x : ℝ, ‖cexp (x * I)‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I x
  have hem : ∀ r, Measurable (fun ω => A.indicator (fun _ => (1 : ℂ)) ω *
      cexp ((lam * thn M (N + ns r) (i0 * 2 ^ ns r) (j0 * 2 ^ ns r) ω : ℝ) * I)) := fun r =>
    hindm.mul (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul (hthm _ _ _))).mul measurable_const))
  have heE : ∀ ω, Tendsto (fun r => A.indicator (fun _ => (1 : ℂ)) ω *
      cexp ((lam * thn M (N + ns r) (i0 * 2 ^ ns r) (j0 * 2 ^ ns r) ω : ℝ) * I)) atTop
      (𝓝 (A.indicator (fun _ => (1 : ℂ)) ω *
        cexp ((lam * (BMx M (tg p.T N j0) ω - BMx M (tg p.T N i0) ω) : ℝ) * I))) := by
    intro ω
    have hc : Continuous fun x : ℝ =>
        A.indicator (fun _ => (1 : ℂ)) ω * cexp ((lam * x : ℝ) * I) := by fun_prop
    exact (hc.tendsto _).comp ((hth ω).comp hns')
  have hEm := aestronglyMeasurable_of_tendsto_ae (μ := M.P) atTop (fun r => (hem r).aestronglyMeasurable)
    (ae_of_all _ heE)
  have hL := tendsto_integral_weighted (Q := M.P) (G := fun r => Zn M (N + ns r))
    (g := M.Z p.T) (fun r ω => Zn_nonneg M _ ω) (fun r => (Zn_int M hM _).1) hZT hGg hint
    (fun r => (hem r).aestronglyMeasurable) hEm
    (fun r ω => by rw [norm_mul, hexp1, mul_one]; exact hind1 ω)
    (fun ω => by rw [norm_mul, hexp1, mul_one]; exact hind1 ω) (ae_of_all _ heE)
  have hRl := tendsto_integral_weighted (Q := M.P) (G := fun r => Zn M (N + ns r))
    (g := M.Z p.T) (fun r ω => Zn_nonneg M _ ω) (fun r => (Zn_int M hM _).1) hZT hGg hint
    (e := fun _ ω => A.indicator (fun _ => (1 : ℂ)) ω)
    (E := fun ω => A.indicator (fun _ => (1 : ℂ)) ω)
    (fun _ => hindm.aestronglyMeasurable) hindm.aestronglyMeasurable (fun _ => hind1) hind1
    (ae_of_all _ fun ω => tendsto_const_nhds)
  have hid : ∀ r, ∫ ω, (Zn M (N + ns r) ω : ℂ) * (A.indicator (fun _ => (1 : ℂ)) ω *
        cexp ((lam * thn M (N + ns r) (i0 * 2 ^ ns r) (j0 * 2 ^ ns r) ω : ℝ) * I)) ∂M.P =
      cexp (-((lam : ℂ) ^ 2 * ((tg p.T N j0 : ℝ) - tg p.T N i0) / 2)) *
      ∫ ω, (Zn M (N + ns r) ω : ℂ) * A.indicator (fun _ => (1 : ℂ)) ω ∂M.P := by
    intro r
    have h := ident_n M hM (N + ns r) (i0 * 2 ^ ns r) (j0 * 2 ^ ns r)
      (Nat.mul_le_mul_right _ hij) (by rw [pow_add]; exact Nat.mul_le_mul_right _ hj)
      (A := A) (by rw [tg_scale]; exact hA) lam
    rwa [tg_scale, tg_scale] at h
  beta_reduce at hL hRl
  simp only [hid] at hL
  exact tendsto_nhds_unique hL (hRl.const_mul _)

end StochCalcDG3m

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcG3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Abstract martingale increments with conditional variance at most `h k`. -/
structure IncrHyp (Q : Measure Ω) (𝒢 : ℕ → MeasurableSpace Ω) (D : ℕ → Ω → ℝ) (h : ℕ → ℝ) :
    Prop where
  le : ∀ k, 𝒢 k ≤ mΩ
  mono : Monotone 𝒢
  meas : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (D k)
  memLp : ∀ k, MemLp (D k) 2 Q
  h_nonneg : ∀ k, 0 ≤ h k
  mean : ∀ k (ξ : Ω → ℝ), StronglyMeasurable[𝒢 k] ξ → MemLp ξ 2 Q →
    ∫ ω, ξ ω * D k ω ∂Q = 0
  var : ∀ k (ξ : Ω → ℝ), StronglyMeasurable[𝒢 k] ξ → (∀ ω, 0 ≤ ξ ω) → (∃ C, ∀ ω, ξ ω ≤ C) →
    ∫ ω, ξ ω * D k ω ^ 2 ∂Q ≤ h k * ∫ ω, ξ ω ∂Q

lemma capped_sum_le (A : ℕ → ℝ) (hA0 : A 0 = 0) (hmono : Monotone A) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ N : ℕ, ∑ k ∈ range N, (if A (k + 1) ≤ δ then A (k + 1) - A k else 0) ≤ min (A N) δ := by
  intro N
  induction N with
  | zero => simp [hA0, hδ]
  | succ n ih =>
    rw [sum_range_succ]
    split_ifs with h
    · rw [min_eq_left h]
      have := min_le_left (A n) δ
      linarith
    · have h1 : min (A n) δ ≤ min (A (n + 1)) δ := min_le_min_right _ (hmono (Nat.le_succ n))
      linarith

lemma abs_mul_le_half (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]

lemma abs_sq_le {x C : ℝ} (h : |x| ≤ C) : |x ^ 2| ≤ C ^ 2 := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg x) h 2

lemma integrable_mul_of_memLp {Q : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 Q) (hg : MemLp g 2 Q) :
    Integrable (fun ω => f ω * g ω) Q := by
  refine Integrable.mono' ((hf.integrable_sq.add hg.integrable_sq).div_const 2)
    (hf.1.mul hg.1) (Eventually.of_forall fun ω => ?_)
  simpa [Real.norm_eq_abs] using abs_mul_le_half (f ω) (g ω)

lemma memLp_bdd_mul {Q : Measure Ω} {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {b f : Ω → ℝ}
    (hb : StronglyMeasurable[m] b) {C : ℝ} (hbC : ∀ ω, |b ω| ≤ C) (hf : MemLp f 2 Q) :
    MemLp (fun ω => b ω * f ω) 2 Q := by
  refine hf.of_le_mul ((hb.mono hm).aestronglyMeasurable.mul hf.1) (c := C)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbC ω) (abs_nonneg _)

lemma integrable_bdd {Q : Measure Ω} [IsFiniteMeasure Q] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m] f) {C : ℝ} (hfC : ∀ ω, |f ω| ≤ C) :
    Integrable f Q :=
  Integrable.mono' (integrable_const C) (hf.mono hm).aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hfC ω)

/-- `L²` bound for step sums: `E S_N² ≤ E ∑_{k<N} h_k b_k²`. -/
lemma sq_le {Q : Measure Ω} [IsFiniteMeasure Q] {𝒢 : ℕ → MeasurableSpace Ω}
    {D : ℕ → Ω → ℝ} {h : ℕ → ℝ} (H : IncrHyp Q 𝒢 D h) (b : ℕ → Ω → ℝ)
    (hb : ∀ k, StronglyMeasurable[𝒢 k] (b k)) (hbC : ∀ k, ∃ C, ∀ ω, |b k ω| ≤ C) :
    ∀ N : ℕ, StronglyMeasurable[𝒢 N] (fun ω => ∑ k ∈ range N, b k ω * D k ω) ∧
      MemLp (fun ω => ∑ k ∈ range N, b k ω * D k ω) 2 Q ∧
      ∫ ω, (∑ k ∈ range N, b k ω * D k ω) ^ 2 ∂Q ≤ ∫ ω, ∑ k ∈ range N, h k * b k ω ^ 2 ∂Q := by
  intro N
  induction N with
  | zero => simp [stronglyMeasurable_const]
  | succ n ih =>
    obtain ⟨hSm, hSL, hSsq⟩ := ih
    obtain ⟨C, hC⟩ := hbC n
    set S : Ω → ℝ := fun ω => ∑ k ∈ range n, b k ω * D k ω with hSdef
    have hYL : MemLp (fun ω => b n ω * D n ω) 2 Q := memLp_bdd_mul (H.le n) (hb n) hC (H.memLp n)
    have hSbm : StronglyMeasurable[𝒢 n] (fun ω => S ω * b n ω) := hSm.mul (hb n)
    have hSbL : MemLp (fun ω => S ω * b n ω) 2 Q := by
      have := memLp_bdd_mul (H.le n) (hb n) hC hSL
      simpa [mul_comm] using this
    have hmean := H.mean n _ hSbm hSbL
    have hb2m : StronglyMeasurable[𝒢 n] (fun ω => b n ω ^ 2) := (hb n).pow 2
    have hb2C : ∀ ω, b n ω ^ 2 ≤ C ^ 2 := fun ω => by
      have := hC ω
      have h0 := abs_nonneg (b n ω)
      nlinarith [sq_abs (b n ω)]
    have hvar := H.var n _ hb2m (fun ω => sq_nonneg _) ⟨C ^ 2, hb2C⟩
    have hb2int : Integrable (fun ω => b n ω ^ 2) Q :=
      integrable_bdd (H.le n) hb2m (C := C ^ 2) fun ω => by
        rw [abs_of_nonneg (sq_nonneg _)]; exact hb2C ω
    have hsumint : ∀ m : ℕ, Integrable (fun ω => ∑ k ∈ range m, h k * b k ω ^ 2) Q := by
      intro m
      refine integrable_finset_sum _ fun k _ => ?_
      obtain ⟨Ck, hCk⟩ := hbC k
      have hk2 : Integrable (fun ω => b k ω ^ 2) Q :=
        integrable_bdd (H.le k) ((hb k).pow 2) (C := Ck ^ 2) fun ω => by
          simpa [Pi.pow_apply] using abs_sq_le (hCk ω)
      exact hk2.const_mul (h k)
    refine ⟨?_, ?_, ?_⟩
    · simp only [sum_range_succ]
      exact (hSm.mono (H.mono (Nat.le_succ n))).add
        (((hb n).mono (H.mono (Nat.le_succ n))).mul (H.meas n))
    · simp only [sum_range_succ]
      exact hSL.add hYL
    · have hpt : (fun ω => (∑ k ∈ range (n + 1), b k ω * D k ω) ^ 2) =
          fun ω => (S ω ^ 2 + 2 * (S ω * b n ω * D n ω)) + b n ω ^ 2 * D n ω ^ 2 := by
        funext ω; simp only [sum_range_succ, hSdef]; ring
      have hrhs : (fun ω => ∑ k ∈ range (n + 1), h k * b k ω ^ 2) =
          fun ω => (∑ k ∈ range n, h k * b k ω ^ 2) + h n * b n ω ^ 2 := by
        funext ω; simp only [sum_range_succ]
      have i1 : Integrable (fun ω => S ω ^ 2) Q := hSL.integrable_sq
      have i2 : Integrable (fun ω => 2 * (S ω * b n ω * D n ω)) Q :=
        (integrable_mul_of_memLp hSbL (H.memLp n)).const_mul 2
      have i3 : Integrable (fun ω => b n ω ^ 2 * D n ω ^ 2) Q := by
        have := hYL.integrable_sq
        refine this.congr (Eventually.of_forall fun ω => ?_)
        simp only; ring
      have i12 : Integrable (fun ω => S ω ^ 2 + 2 * (S ω * b n ω * D n ω)) Q := i1.add i2
      have i4 : Integrable (fun ω => h n * b n ω ^ 2) Q := hb2int.const_mul (h n)
      rw [hpt, hrhs, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
        hmean, integral_add (hsumint n) i4, integral_const_mul]
      linarith

/-- The predictable quadratic variation of the step sum `∑ a_k D_k`. -/
noncomputable def Aseq (h : ℕ → ℝ) (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range n, h k * a k ω ^ 2

lemma Aseq_succ (h : ℕ → ℝ) (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Aseq h a (n + 1) ω = Aseq h a n ω + h n * a n ω ^ 2 := by
  simp [Aseq, sum_range_succ]

lemma Aseq_mono (h : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (a : ℕ → Ω → ℝ) (ω : Ω) :
    Monotone fun n => Aseq h a n ω := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [Aseq_succ]
  have := mul_nonneg (hh n) (sq_nonneg (a n ω))
  linarith

lemma Aseq_nonneg (h : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ Aseq h a n ω :=
  sum_nonneg fun k _ => mul_nonneg (hh k) (sq_nonneg _)

lemma Aseq_meas {𝒢 : ℕ → MeasurableSpace Ω} (hmono : Monotone 𝒢) (h : ℕ → ℝ)
    (a : ℕ → Ω → ℝ) (ha : ∀ k, StronglyMeasurable[𝒢 k] (a k)) (k : ℕ) :
    StronglyMeasurable[𝒢 k] (Aseq h a (k + 1)) := by
  have : Aseq h a (k + 1) = ∑ j ∈ range (k + 1), fun ω => h j * a j ω ^ 2 := by
    funext ω; simp [Aseq, Finset.sum_apply]
  rw [this]
  refine Finset.stronglyMeasurable_sum _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  exact stronglyMeasurable_const.mul (((ha j).mono (hmono hjk)).pow 2)

/-- **Discrete Lenglart tail bound.** `Q(c ≤ |∑_{k<N} a_k D_k|) ≤ Q(δ < A_N) + E[min(A_N, δ)]/c²`. -/
theorem tail_le {Q : Measure Ω} [IsFiniteMeasure Q] {𝒢 : ℕ → MeasurableSpace Ω}
    {D : ℕ → Ω → ℝ} {h : ℕ → ℝ} (H : IncrHyp Q 𝒢 D h) (a : ℕ → Ω → ℝ)
    (ha : ∀ k, StronglyMeasurable[𝒢 k] (a k)) (haC : ∀ k, ∃ C, ∀ ω, |a k ω| ≤ C) (N : ℕ)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) :
    Q {ω | c ≤ |∑ k ∈ range N, a k ω * D k ω|} ≤
      Q {ω | δ < Aseq h a N ω} + ENNReal.ofReal ((∫ ω, min (Aseq h a N ω) δ ∂Q) / c ^ 2) := by
  classical
  set b : ℕ → Ω → ℝ := fun k ω => if Aseq h a (k + 1) ω ≤ δ then a k ω else 0 with hbdef
  have hbm : ∀ k, StronglyMeasurable[𝒢 k] (b k) := by
    intro k
    have hs : MeasurableSet[𝒢 k] {ω | Aseq h a (k + 1) ω ≤ δ} :=
      measurableSet_le (Aseq_meas H.mono h a ha k).measurable measurable_const
    exact StronglyMeasurable.ite hs (ha k) stronglyMeasurable_const
  have hbC : ∀ k, ∃ C, ∀ ω, |b k ω| ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := haC k
    refine ⟨|C|, fun ω => ?_⟩
    simp only [hbdef]
    split_ifs
    · exact (hC ω).trans (le_abs_self C)
    · simp
  obtain ⟨-, hS'L, hS'sq⟩ := sq_le H b hbm hbC N
  -- pointwise: ∑ h_k b_k² ≤ min(A_N, δ)
  have hpt : ∀ ω, ∑ k ∈ range N, h k * b k ω ^ 2 ≤ min (Aseq h a N ω) δ := by
    intro ω
    have heq : ∀ k, h k * b k ω ^ 2 = (if Aseq h a (k + 1) ω ≤ δ then
        Aseq h a (k + 1) ω - Aseq h a k ω else 0) := by
      intro k
      simp only [hbdef]
      split_ifs
      · rw [Aseq_succ]; ring
      · ring
    simp_rw [heq]
    exact capped_sum_le (fun n => Aseq h a n ω) (by simp [Aseq]) (Aseq_mono h H.h_nonneg a ω)
      δ hδ N
  have hAN : StronglyMeasurable (Aseq h a N) := by
    cases N with
    | zero =>
      have h0 : Aseq h a 0 = fun _ => (0 : ℝ) := by funext ω; simp [Aseq]
      rw [h0]; exact stronglyMeasurable_const
    | succ n => exact (Aseq_meas H.mono h a ha n).mono (H.le n)
  have hminint : Integrable (fun ω => min (Aseq h a N ω) δ) Q := by
    refine Integrable.mono' (integrable_const δ)
      (hAN.measurable.min measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Aseq_nonneg h H.h_nonneg a N ω) hδ)]
    exact min_le_right _ _
  have hS'le : ∫ ω, (∑ k ∈ range N, b k ω * D k ω) ^ 2 ∂Q ≤
      ∫ ω, min (Aseq h a N ω) δ ∂Q := by
    refine hS'sq.trans (integral_mono_of_nonneg ?_ hminint (Eventually.of_forall hpt))
    exact Eventually.of_forall fun ω =>
      sum_nonneg fun k _ => mul_nonneg (H.h_nonneg k) (sq_nonneg _)
  -- set inclusion
  have hsub : {ω | c ≤ |∑ k ∈ range N, a k ω * D k ω|} ⊆
      {ω | δ < Aseq h a N ω} ∪ {ω | c ^ 2 ≤ (∑ k ∈ range N, b k ω * D k ω) ^ 2} := by
    intro ω hω
    by_cases hA : δ < Aseq h a N ω
    · exact Or.inl hA
    · right
      push Not at hA
      have hsum : ∑ k ∈ range N, b k ω * D k ω = ∑ k ∈ range N, a k ω * D k ω := by
        refine sum_congr rfl fun k hk => ?_
        have hk' : k + 1 ≤ N := mem_range.mp hk
        have : Aseq h a (k + 1) ω ≤ δ := (Aseq_mono h H.h_nonneg a ω hk').trans hA
        simp only [hbdef, if_pos this]
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [hsum]
      calc c ^ 2 ≤ |∑ k ∈ range N, a k ω * D k ω| ^ 2 := pow_le_pow_left₀ hc.le hω 2
        _ = (∑ k ∈ range N, a k ω * D k ω) ^ 2 := sq_abs _
  have hcheb : Q {ω | c ^ 2 ≤ (∑ k ∈ range N, b k ω * D k ω) ^ 2} ≤
      ENNReal.ofReal ((∫ ω, min (Aseq h a N ω) δ ∂Q) / c ^ 2) := by
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := Q)
      (Eventually.of_forall fun ω => sq_nonneg (∑ k ∈ range N, b k ω * D k ω))
      hS'L.integrable_sq (c ^ 2)
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity)]
    have hm' : c ^ 2 * (Q {ω | c ^ 2 ≤ (∑ k ∈ range N, b k ω * D k ω) ^ 2}).toReal ≤
        ∫ ω, (∑ k ∈ range N, b k ω * D k ω) ^ 2 ∂Q := hm
    nlinarith
  calc Q {ω | c ≤ |∑ k ∈ range N, a k ω * D k ω|}
      ≤ Q ({ω | δ < Aseq h a N ω} ∪ {ω | c ^ 2 ≤ (∑ k ∈ range N, b k ω * D k ω) ^ 2}) :=
        measure_mono hsub
    _ ≤ Q {ω | δ < Aseq h a N ω} + Q {ω | c ^ 2 ≤ (∑ k ∈ range N, b k ω * D k ω) ^ 2} :=
        measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hcheb

/-! ## G3b: uniform integrability from uniform dyadic tail bounds
If every member satisfies `Q(2^j ≤ |S_i|) ≤ 2 E[min(1, V/4^j)]` (what `tail_le` gives with
`δ = c² = 4^j` and `A_N ≤ V`) and `√V` is integrable, the family is uniformly integrable. -/

noncomputable def phiT (s y : ℝ) : ℝ := 2 * min y s - 2 * s ^ 2 / max y s

lemma tele_step {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    min x (s ^ 2 / x) ≤ phiT s (2 * x) - phiT s x := by
  unfold phiT
  rcases le_total (2 * x) s with h1 | h1
  · have hspos : 0 < s := by linarith
    have hxs : x ≤ s := by linarith
    rw [min_eq_left h1, max_eq_right h1, min_eq_left hxs, max_eq_right hxs]
    have hm := min_le_left x (s ^ 2 / x)
    linarith
  · rcases le_total s x with h2 | h2
    · rw [min_eq_right h1, max_eq_left h1, min_eq_right h2, max_eq_left h2]
      have e : 2 * s ^ 2 / (2 * x) = s ^ 2 / x := by field_simp
      have e2 : 2 * s ^ 2 / x = 2 * (s ^ 2 / x) := by ring
      rw [e, e2]
      have hm := min_le_right x (s ^ 2 / x)
      linarith
    · have hspos : 0 < s := lt_of_lt_of_le hx h2
      rw [min_eq_right h1, max_eq_left h1, min_eq_left h2, max_eq_right h2]
      have e : 2 * s ^ 2 / (2 * x) = s ^ 2 / x := by field_simp
      have e3 : 2 * s ^ 2 / s = 2 * s := by field_simp
      rw [e, e3]
      have key : s ^ 2 / x ≤ 4 * s - 3 * x := by
        rw [div_le_iff₀ hx]
        nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0:ℝ) ≤ 3 * x - s)]
      have hm := min_le_left x (s ^ 2 / x)
      linarith

lemma geo_sum_le {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∑ j ∈ range n, (2:ℝ) ^ j * min 1 (s ^ 2 / 4 ^ j) ≤ 4 * s := by
  have hterm : ∀ j : ℕ, (2:ℝ) ^ j * min 1 (s ^ 2 / 4 ^ j) ≤
      phiT s (2 ^ (j + 1)) - phiT s (2 ^ j) := by
    intro j
    have hx : (0:ℝ) < 2 ^ j := by positivity
    have e : (2:ℝ) ^ j * min 1 (s ^ 2 / 4 ^ j) = min (2 ^ j) (s ^ 2 / 2 ^ j) := by
      rw [mul_min_of_nonneg _ _ hx.le, mul_one]
      congr 1
      rw [show (4:ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
      field_simp
    rw [e, show (2:ℝ) ^ (j + 1) = 2 * 2 ^ j by ring]
    exact tele_step hs hx
  calc ∑ j ∈ range n, (2:ℝ) ^ j * min 1 (s ^ 2 / 4 ^ j)
      ≤ ∑ j ∈ range n, (phiT s (2 ^ (j + 1)) - phiT s (2 ^ j)) :=
        sum_le_sum fun j _ => hterm j
    _ = phiT s (2 ^ n) - phiT s (2 ^ 0) := sum_range_sub (fun j => phiT s (2 ^ j)) n
    _ ≤ 4 * s := by
      unfold phiT
      simp only [pow_zero]
      have h1 : min ((2:ℝ) ^ n) s ≤ s := min_le_right _ _
      have h2 : 0 ≤ s ^ 2 / max ((2:ℝ) ^ n) s := by positivity
      have h3 : 0 ≤ min (1:ℝ) s := le_min zero_le_one hs
      have h4 : s ^ 2 / max 1 s ≤ s := by
        rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left 1 s))]
        nlinarith [le_max_right 1 s]
      have e1 : 2 * s ^ 2 / max ((2:ℝ) ^ n) s = 2 * (s ^ 2 / max ((2:ℝ) ^ n) s) := by ring
      have e2 : 2 * s ^ 2 / max (1:ℝ) s = 2 * (s ^ 2 / max (1:ℝ) s) := by ring
      rw [e1, e2]
      linarith

theorem unifIntegrable_of_dyadic_tail {Q : Measure Ω} [IsFiniteMeasure Q] {ι : Type*}
    (S : ι → Ω → ℝ) (hSm : ∀ i, Measurable (S i)) (V : Ω → ℝ) (hVm : Measurable V)
    (hV0 : ∀ ω, 0 ≤ V ω) (hVi : Integrable (fun ω => Real.sqrt (V ω)) Q)
    (hT : ∀ i (j : ℕ), Q {ω | (2:ℝ) ^ j ≤ |S i ω|} ≤
      2 * ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q) :
    UnifIntegrable S 1 Q := by
  set ψ : ℕ → Ω → ℝ≥0∞ := fun j ω => ENNReal.ofReal (2 ^ j * min 1 (V ω / 4 ^ j)) with hψ
  have hψm : ∀ j, Measurable (ψ j) := fun j =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.min (hVm.div_const _)))
  have hpt : ∀ ω, ∑' j, ψ j ω ≤ ENNReal.ofReal (4 * Real.sqrt (V ω)) := by
    intro ω
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (by positivity)
      (le_min zero_le_one (div_nonneg (hV0 ω) (by positivity))))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := geo_sum_le (Real.sqrt_nonneg (V ω)) n
    rwa [Real.sq_sqrt (hV0 ω)] at this
  have hfin : ∑' j, ∫⁻ ω, ψ j ω ∂Q ≠ ∞ := by
    rw [← lintegral_tsum fun j => (hψm j).aemeasurable]
    exact ne_of_lt (lt_of_le_of_lt (lintegral_mono hpt) (hVi.const_mul 4).lintegral_lt_top)
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun i => (hSm i).aestronglyMeasurable)
    fun ε hε => ?_
  have hpos : (0:ℝ≥0∞) < ENNReal.ofReal ε / 4 :=
    ENNReal.div_pos (ENNReal.ofReal_pos.2 hε).ne' (by norm_num)
  obtain ⟨m, hm⟩ := ((ENNReal.tendsto_sum_nat_add (fun j => ∫⁻ ω, ψ j ω ∂Q) hfin).eventually
    (gt_mem_nhds hpos)).exists
  refine ⟨(2:ℝ≥0) ^ m, fun i => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hmeasS : ∀ j : ℕ, MeasurableSet {x | (2:ℝ) ^ j ≤ |S i x|} := fun j =>
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hSm i))
  have hptS : ∀ ω, ‖{x | (2:ℝ≥0) ^ m ≤ ‖S i x‖₊}.indicator (S i) ω‖ₑ ≤
      ∑' k, {x | (2:ℝ) ^ (k + m) ≤ |S i x|}.indicator (fun _ => (2:ℝ≥0∞) ^ (k + m + 1)) ω := by
    intro ω
    by_cases hω : (2:ℝ≥0) ^ m ≤ ‖S i ω‖₊
    · rw [Set.indicator_of_mem (by exact hω)]
      have hge : (2:ℝ) ^ m ≤ |S i ω| := by
        have := NNReal.coe_le_coe.mpr hω
        simpa [Real.norm_eq_abs] using this
      set F := ⌊|S i ω|⌋₊ with hF
      have hF1 : 2 ^ m ≤ F := by
        rw [hF]; apply Nat.le_floor; exact_mod_cast hge
      have hF0 : F ≠ 0 := by
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        omega
      set j0 := Nat.log 2 F with hj0
      have hmj : m ≤ j0 := Nat.le_log_of_pow_le (by norm_num) hF1
      have hlow : (2:ℝ) ^ j0 ≤ |S i ω| := by
        have h1 : 2 ^ j0 ≤ F := Nat.pow_log_le_self 2 hF0
        have h2 : (F : ℝ) ≤ |S i ω| := Nat.floor_le (abs_nonneg _)
        have h1' : ((2 ^ j0 : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast h1
        push_cast at h1'
        linarith
      have hup : |S i ω| ≤ (2:ℝ) ^ (j0 + 1) := by
        have h1 : F < 2 ^ (j0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) F
        have h2 : |S i ω| < F + 1 := Nat.lt_floor_add_one _
        have h3 : (F : ℝ) + 1 ≤ ((2 ^ (j0 + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h3
        linarith
      refine le_trans ?_ (ENNReal.le_tsum (j0 - m))
      beta_reduce
      rw [Nat.sub_add_cancel hmj, Set.indicator_of_mem (by exact hlow), Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal |S i ω| ≤ ENNReal.ofReal ((2:ℝ) ^ (j0 + 1)) :=
            ENNReal.ofReal_le_ofReal hup
        _ = (2:ℝ≥0∞) ^ (j0 + 1) := by rw [ENNReal.ofReal_pow (by norm_num)]; simp
    · rw [Set.indicator_of_notMem (by exact hω)]
      simp
  have hψint : ∀ j : ℕ, ∫⁻ ω, ψ j ω ∂Q =
      (2:ℝ≥0∞) ^ j * ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q := by
    intro j
    rw [← lintegral_const_mul' ((2:ℝ≥0∞) ^ j) _ (ENNReal.pow_ne_top (by norm_num))]
    congr 1
    funext ω
    simp only [hψ]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  calc ∫⁻ ω, ‖{x | (2:ℝ≥0) ^ m ≤ ‖S i x‖₊}.indicator (S i) ω‖ₑ ∂Q
      ≤ ∫⁻ ω, ∑' k, {x | (2:ℝ) ^ (k + m) ≤ |S i x|}.indicator
          (fun _ => (2:ℝ≥0∞) ^ (k + m + 1)) ω ∂Q := lintegral_mono hptS
    _ = ∑' k, (2:ℝ≥0∞) ^ (k + m + 1) * Q {x | (2:ℝ) ^ (k + m) ≤ |S i x|} := by
        rw [lintegral_tsum fun k => (measurable_const.indicator (hmeasS (k + m))).aemeasurable]
        congr 1
        funext k
        exact lintegral_indicator_const (hmeasS (k + m)) _
    _ ≤ ∑' k, 4 * ∫⁻ ω, ψ (k + m) ω ∂Q := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [hψint (k + m)]
        calc (2:ℝ≥0∞) ^ (k + m + 1) * Q {x | (2:ℝ) ^ (k + m) ≤ |S i x|}
            ≤ (2:ℝ≥0∞) ^ (k + m + 1) *
                (2 * ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ (k + m))) ∂Q) :=
              mul_le_mul' le_rfl (hT i (k + m))
          _ = 4 * ((2:ℝ≥0∞) ^ (k + m) *
                ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ (k + m))) ∂Q) := by ring
    _ = 4 * ∑' k, ∫⁻ ω, ψ (k + m) ω ∂Q := ENNReal.tsum_mul_left
    _ ≤ 4 * (ENNReal.ofReal ε / 4) := mul_le_mul' le_rfl hm.le
    _ = ENNReal.ofReal ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end StochCalcG3
/-! G2c (8c066573 relay 8): characteristic functions on `F_u`-events => the `B^M` increment is
`N(0, v-u)` and independent of `F_u` under `P^M`; hence `IncrHyp P^M` on dyadic `T`-grid partitions.
Append after DG3n_tail + G3 (dev file probe/8c066573_DG4c.lean). -/

namespace StochCalcG2c

open MeasureTheory ProbabilityTheory Complex

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

lemma ind_mul (A : Set Ω) (g : Ω → ℂ) (ω : Ω) :
    A.indicator (fun _ => (1 : ℂ)) ω * g ω = A.indicator g ω := by
  by_cases h : ω ∈ A <;> simp [h]

/-- Pure: conditional characteristic function => conditional law. -/
theorem restrict_map_eq {Q : Measure Ω} [IsProbabilityMeasure Q]
    (h𝒢 : 𝒢 ≤ mΩ) {Δ : Ω → ℝ} (hΔ : Measurable Δ) (v : ℝ≥0)
    (hcf : ∀ A, MeasurableSet[𝒢] A → ∀ lam : ℝ,
      ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω * cexp ((lam * Δ ω : ℝ) * I) ∂Q =
        cexp (-((lam : ℂ) ^ 2 * ((v : ℝ) : ℂ) / 2)) * ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω ∂Q)
    (A : Set Ω) (hA : MeasurableSet[𝒢] A) :
    (Q.restrict A).map Δ = Q A • gaussianReal 0 v := by
  have hAm : MeasurableSet A := h𝒢 _ hA
  haveI : IsFiniteMeasure (Q A • gaussianReal 0 v) :=
    ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact measure_lt_top Q A⟩
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have e1 : charFun ((Q.restrict A).map Δ) t =
      ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω * cexp ((t * Δ ω : ℝ) * I) ∂Q := by
    rw [charFun_apply_real, integral_map hΔ.aemeasurable
      ((by fun_prop : Continuous fun x : ℝ => cexp (t * x * I)).aestronglyMeasurable),
      ← integral_indicator hAm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    push_cast
    exact (ind_mul A (fun x => cexp (↑t * ↑(Δ x) * I)) ω).symm
  have e2 : charFun (Q A • gaussianReal 0 v) t =
      (Q A).toReal * cexp (-((t : ℂ) ^ 2 * ((v : ℝ) : ℂ) / 2)) := by
    rw [charFun_apply_real, integral_smul_measure, ← charFun_apply_real, charFun_gaussianReal]
    simp only [ofReal_zero, mul_zero, zero_mul, zero_sub, Complex.real_smul]
    ring_nf
  rw [e1, e2, hcf A hA t, integral_indicator_const _ hAm, Measure.real_def]
  simp only [Complex.real_smul, mul_one]
  ring

/-- Pure: law and independence. -/
theorem law_indep {Q : Measure Ω} [IsProbabilityMeasure Q]
    (h𝒢 : 𝒢 ≤ mΩ) {Δ : Ω → ℝ} (hΔ : Measurable Δ) (v : ℝ≥0)
    (hcf : ∀ A, MeasurableSet[𝒢] A → ∀ lam : ℝ,
      ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω * cexp ((lam * Δ ω : ℝ) * I) ∂Q =
        cexp (-((lam : ℂ) ^ 2 * ((v : ℝ) : ℂ) / 2)) * ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω ∂Q) :
    Q.map Δ = gaussianReal 0 v ∧ Indep 𝒢 (MeasurableSpace.comap Δ inferInstance) Q := by
  have hrm := restrict_map_eq h𝒢 hΔ v hcf
  have hlaw : Q.map Δ = gaussianReal 0 v := by
    have := hrm Set.univ MeasurableSet.univ
    rwa [Measure.restrict_univ, measure_univ, one_smul] at this
  refine ⟨hlaw, ?_⟩
  rw [Indep_iff]
  intro t1 t2 ht1 ht2
  obtain ⟨B, hB, rfl⟩ := ht2
  have h1 := congrArg (fun μ : Measure ℝ => μ B) (hrm t1 ht1)
  simp only [Measure.map_apply hΔ hB, Measure.restrict_apply (hΔ hB), Measure.smul_apply,
    smul_eq_mul] at h1
  have h2 : Q (Δ ⁻¹' B) = gaussianReal 0 v B := by rw [← hlaw, Measure.map_apply hΔ hB]
  rw [Set.inter_comm, h1, h2]

/-- Pure: the increment properties used by `IncrHyp`. -/
theorem incr_props {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Δ : Ω → ℝ} (hΔ : Measurable Δ) (v : ℝ≥0)
    (hlaw : Q.map Δ = gaussianReal 0 v) (hind : Indep 𝒢 (MeasurableSpace.comap Δ inferInstance) Q)
    (h𝒢 : 𝒢 ≤ mΩ) :
    MemLp Δ 2 Q ∧ (∀ ξ : Ω → ℝ, StronglyMeasurable[𝒢] ξ → ∫ ω, ξ ω * Δ ω ∂Q = 0) ∧
      (∀ ξ : Ω → ℝ, StronglyMeasurable[𝒢] ξ → ∫ ω, ξ ω * Δ ω ^ 2 ∂Q = v * ∫ ω, ξ ω ∂Q) := by
  have hmem : MemLp Δ 2 Q := by
    have h0 : MemLp id 2 (Q.map Δ) := by rw [hlaw]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id hΔ.aemeasurable).mp h0
  have hE : ∫ ω, Δ ω ∂Q = 0 := by
    have := integral_map hΔ.aemeasurable
      (aestronglyMeasurable_id : AEStronglyMeasurable (id : ℝ → ℝ) (Q.map Δ))
    rw [hlaw] at this
    simp only [id] at this
    rw [integral_id_gaussianReal] at this
    exact this.symm
  have hE2 : ∫ ω, Δ ω ^ 2 ∂Q = v := by
    have hN : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
      have h := variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := id) aemeasurable_id
        integral_id_gaussianReal
      rw [variance_id_gaussianReal] at h
      exact h.symm
    have := integral_map hΔ.aemeasurable
      ((by fun_prop : Continuous fun x : ℝ => x ^ 2).aestronglyMeasurable :
        AEStronglyMeasurable (fun x : ℝ => x ^ 2) (Q.map Δ))
    rw [hlaw] at this
    rw [← hN, this]
  have hindξ : ∀ ξ : Ω → ℝ, StronglyMeasurable[𝒢] ξ → IndepFun ξ Δ Q := by
    intro ξ hξ
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind hξ.measurable.comap_le
  refine ⟨hmem, fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · have := (hindξ ξ hξ).integral_mul_eq_mul_integral
      ((hξ.mono h𝒢).aestronglyMeasurable) hΔ.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hE, mul_zero]
  · have hi := ((hindξ ξ hξ).comp measurable_id (measurable_id.pow_const 2))
    have := hi.integral_mul_eq_mul_integral ((hξ.mono h𝒢).aestronglyMeasurable)
      (hΔ.pow_const 2).aestronglyMeasurable
    simp only [Pi.mul_apply, Function.comp_apply, id] at this
    rw [this, hE2, mul_comm]

end StochCalcG2c

namespace StochCalcDG3m

open HedgePSNV EthierKurtz ItoLib StochCalcBr StochCalcDG StochCalcDG3p Finset Complex
open MeasureTheory ProbabilityTheory Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma intη_measF (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    StronglyMeasurable[M.F t] (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω) := by
  by_cases ht0 : t = 0
  · subst ht0
    simp only [NNReal.coe_zero, intervalIntegral.integral_same]
    exact stronglyMeasurable_const
  have hT : (0 : ℝ) < t := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun n ω => ∑ k ∈ range (2 ^ n), M.η (tg t n k) ω * ((t : ℝ) / 2 ^ n)) ?_ ?_
  · intro n
    refine Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_
    exact ((η_measF M hM _).mono (M.F.mono (tg_le_T t (Finset.mem_range.mp hk).le))).mul_const _
  · refine tendsto_pi_nhds.mpr fun ω => ?_
    have hg : Continuous fun x : ℝ => M.η x.toNNReal ω :=
      (η_cont' M hM ω).comp continuous_real_toNNReal
    have hR := riemann_left hg 0 hT.le (m := fun n => 2 ^ n) (δ := fun n => (t : ℝ) / 2 ^ n)
      (fun n => div_pos hT (by positivity))
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
      (fun n => by push_cast; field_simp)
    beta_reduce at hR
    rw [zero_add] at hR
    refine hR.congr fun n => Finset.sum_congr rfl fun k _ => ?_
    rw [zero_add, ← tg_coe, Real.toNNReal_coe]

lemma BMx_measF (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    StronglyMeasurable[M.F t] (BMx M t) :=
  (B_measF' M hM le_rfl).stronglyMeasurable.add (intη_measF M hM t)

lemma PM_eq (M : Model p Ω) (h5 : M.Assumption5) (g : Ω → ℂ) :
    ∫ ω, g ω ∂M.PM = ∫ ω, (M.Z p.T ω : ℂ) * g ω ∂M.P := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (StochCalcHedge.Z_T_measurable M h5).real_toNNReal
  unfold Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (StochCalcHedge.Z_pos M p.T ω).le,
    Complex.real_smul]

lemma PM_prob (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) :
    IsProbabilityMeasure M.PM := by
  haveI := hM.prob
  constructor
  unfold Model.PM
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((h5.2 p.T le_rfl).integrable one_le_two)
      (Filter.Eventually.of_forall fun ω => (StochCalcHedge.Z_pos M p.T ω).le),
    StochCalcHedge.integral_Z_T M hM h5, ENNReal.ofReal_one]

theorem girsanov_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (N i0 j0 : ℕ) (hij : i0 ≤ j0) (hj : j0 ≤ 2 ^ N) {A : Set Ω}
    (hA : MeasurableSet[M.F (tg p.T N i0)] A) (lam : ℝ) :
    ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω *
        cexp ((lam * (BMx M (tg p.T N j0) ω - BMx M (tg p.T N i0) ω) : ℝ) * I) ∂M.PM =
      cexp (-((lam : ℂ) ^ 2 * (((tg p.T N j0 - tg p.T N i0 : ℝ≥0) : ℝ) : ℂ) / 2)) *
      ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω ∂M.PM := by
  rw [PM_eq M h5, PM_eq M h5, NNReal.coe_sub (tg_mono _ _ hij)]
  have h := girsanov_dyadic M hM h5 N i0 j0 hij hj hA lam
  push_cast at h ⊢
  exact h

/-- **G2c**: `B^M` increments on a dyadic `T`-grid partition satisfy `IncrHyp` under `P^M`. -/
theorem incrHyp_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (N : ℕ)
    (ι : ℕ → ℕ) (hι : Monotone ι) (hιN : ∀ k, ι k ≤ 2 ^ N) :
    StochCalcG3.IncrHyp M.PM (fun k => M.F (tg p.T N (ι k)))
      (fun k ω => BMx M (tg p.T N (ι (k + 1))) ω - BMx M (tg p.T N (ι k)) ω)
      (fun k => (tg p.T N (ι (k + 1)) : ℝ) - tg p.T N (ι k)) := by
  haveI := PM_prob M hM h5
  have hkey : ∀ k, Measurable (fun ω => BMx M (tg p.T N (ι (k + 1))) ω -
        BMx M (tg p.T N (ι k)) ω) ∧
      M.PM.map (fun ω => BMx M (tg p.T N (ι (k + 1))) ω - BMx M (tg p.T N (ι k)) ω) =
        gaussianReal 0 (tg p.T N (ι (k + 1)) - tg p.T N (ι k)) ∧
      Indep (M.F (tg p.T N (ι k))) (MeasurableSpace.comap (fun ω =>
        BMx M (tg p.T N (ι (k + 1))) ω - BMx M (tg p.T N (ι k)) ω) inferInstance) M.PM := by
    intro k
    have hm : Measurable (fun ω => BMx M (tg p.T N (ι (k + 1))) ω - BMx M (tg p.T N (ι k)) ω) :=
      ((BMx_measF M hM _).measurable.mono (M.F.le _) le_rfl).sub
        ((BMx_measF M hM _).measurable.mono (M.F.le _) le_rfl)
    exact ⟨hm, StochCalcG2c.law_indep (M.F.le _) hm _
      (fun A hA lam => girsanov_PM M hM h5 N (ι k) (ι (k + 1)) (hι (Nat.le_succ k)) (hιN _) hA lam)⟩
  have hsub : ∀ k, (((tg p.T N (ι (k + 1)) - tg p.T N (ι k) : ℝ≥0)) : ℝ) =
      (tg p.T N (ι (k + 1)) : ℝ) - tg p.T N (ι k) := fun k =>
    NNReal.coe_sub (tg_mono _ _ (hι (Nat.le_succ k)))
  refine ⟨fun k => M.F.le _, fun a b hab => M.F.mono (tg_mono _ _ (hι hab)), fun k => ?_,
    fun k => ?_, fun k => ?_, fun k ξ hξ _ => ?_, fun k ξ hξ _ _ => ?_⟩
  · exact (BMx_measF M hM _).sub
      ((BMx_measF M hM _).mono (M.F.mono (tg_mono _ _ (hι (Nat.le_succ k)))))
  · exact (StochCalcG2c.incr_props (hkey k).1 _ (hkey k).2.1 (hkey k).2.2 (M.F.le _)).1
  · exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (tg_mono _ _ (hι (Nat.le_succ k))))
  · exact (StochCalcG2c.incr_props (hkey k).1 _ (hkey k).2.1 (hkey k).2.2 (M.F.le _)).2.1 ξ hξ
  · rw [(StochCalcG2c.incr_props (hkey k).1 _ (hkey k).2.1 (hkey k).2.2 (M.F.le _)).2.2 ξ hξ,
      hsub k]

end StochCalcDG3m

/-! G4 (8c066573 relay 9): cell-average step sums for `∫ Xσ dB^M`.
Coefficient on cell `l` of the level-`L` `T`-grid: `cf L R l = clamp_R (average of Xσ on cell l-1)`
(`cf L R 0 = 0`). It is `F(t_l)`-measurable, bounded by `R`, and `Σ h cf² ≤ ∫_0^T (Xσ)²`. -/

namespace StochCalcG4

open HedgePSNV EthierKurtz ItoLib StochCalcBr StochCalcDG3m Finset
open MeasureTheory ProbabilityTheory Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The integrand `Xσ`. -/
noncomputable def Y (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ := M.X t ω * M.σ t ω

lemma Y_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) : Continuous fun t => Y M t ω :=
  (hM.X_cont ω).mul (hM.σ_cont ω)

lemma Yr_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) :
    Continuous fun u : ℝ => Y M u.toNNReal ω :=
  (Y_cont M hM ω).comp continuous_real_toNNReal

lemma Y_measF (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) :
    StronglyMeasurable[M.F s] (Y M s) :=
  ((hM.X_adapted s).mono (G_le_F' M hM s)).mul ((hM.σ_adapted s).mono (G_le_F' M hM s))

lemma intY_measF (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    StronglyMeasurable[M.F t] (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), Y M u.toNNReal ω) := by
  by_cases ht0 : t = 0
  · subst ht0
    simp only [NNReal.coe_zero, intervalIntegral.integral_same]
    exact stronglyMeasurable_const
  have hT : (0 : ℝ) < t := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun n ω => ∑ k ∈ range (2 ^ n), Y M (tg t n k) ω * ((t : ℝ) / 2 ^ n)) ?_ ?_
  · intro n
    refine Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_
    exact ((Y_measF M hM _).mono (M.F.mono (tg_le_T t (Finset.mem_range.mp hk).le))).mul_const _
  · refine tendsto_pi_nhds.mpr fun ω => ?_
    have hg : Continuous fun x : ℝ => Y M x.toNNReal ω := Yr_cont M hM ω
    have hR := StochCalcDG3p.riemann_left hg 0 hT.le (m := fun n => 2 ^ n)
      (δ := fun n => (t : ℝ) / 2 ^ n)
      (fun n => div_pos hT (by positivity))
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
      (fun n => by push_cast; field_simp)
    beta_reduce at hR
    rw [zero_add] at hR
    refine hR.congr fun n => Finset.sum_congr rfl fun k _ => ?_
    rw [zero_add, ← tg_coe, Real.toNNReal_coe]

/-- Integral of `Xσ` over cell `l` of the level-`L` grid. -/
noncomputable def cint (M : Model p Ω) (L l : ℕ) (ω : Ω) : ℝ :=
  ∫ u in (tg p.T L l : ℝ)..(tg p.T L (l + 1) : ℝ), Y M u.toNNReal ω

lemma cint_eq (M : Model p Ω) (hM : M.Standing) (L l : ℕ) (ω : Ω) :
    cint M L l ω = (∫ u in (0 : ℝ)..(tg p.T L (l + 1) : ℝ), Y M u.toNNReal ω) -
      ∫ u in (0 : ℝ)..(tg p.T L l : ℝ), Y M u.toNNReal ω := by
  unfold cint
  exact (intervalIntegral.integral_interval_sub_left ((Yr_cont M hM ω).intervalIntegrable _ _)
    ((Yr_cont M hM ω).intervalIntegrable _ _)).symm

lemma cint_measF (M : Model p Ω) (hM : M.Standing) (L l : ℕ) :
    StronglyMeasurable[M.F (tg p.T L (l + 1))] (cint M L l) := by
  have e : cint M L l = fun ω => (∫ u in (0 : ℝ)..(tg p.T L (l + 1) : ℝ), Y M u.toNNReal ω) -
      ∫ u in (0 : ℝ)..(tg p.T L l : ℝ), Y M u.toNNReal ω := funext (cint_eq M hM L l)
  rw [e]
  exact (intY_measF M hM _).sub
    ((intY_measF M hM _).mono (M.F.mono (tg_mono _ _ (Nat.le_succ l))))

/-- Grid step. -/
noncomputable def hL (p : Params) (L : ℕ) : ℝ := (p.T : ℝ) / 2 ^ L

lemma hL_nonneg (p : Params) (L : ℕ) : 0 ≤ hL p L := by unfold hL; positivity

lemma tg_succ_sub (T : ℝ≥0) (L l : ℕ) :
    (tg T L (l + 1) : ℝ) - tg T L l = (T : ℝ) / 2 ^ L := by
  rw [tg_coe, tg_coe]; push_cast; ring

/-- Cell-average coefficient (clamped at `R`), using the PREVIOUS cell. -/
noncomputable def cf (M : Model p Ω) (L : ℕ) (R : ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  if l = 0 then 0 else max (-R) (min (cint M L (l - 1) ω / hL p L) R)

lemma cf_zero (M : Model p Ω) (L : ℕ) (R : ℝ) (ω : Ω) : cf M L R 0 ω = 0 := by
  simp [cf]

lemma cf_measF (M : Model p Ω) (hM : M.Standing) (L : ℕ) (R : ℝ) (l : ℕ) :
    StronglyMeasurable[M.F (tg p.T L l)] (cf M L R l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have e : cf M L R 0 = fun _ => 0 := funext (cf_zero M L R)
    rw [e]; exact stronglyMeasurable_const
  · have hl' : l - 1 + 1 = l := Nat.sub_add_cancel hl
    have h := cint_measF M hM L (l - 1)
    rw [hl'] at h
    have e : cf M L R l = fun ω => max (-R) (min (cint M L (l - 1) ω / hL p L) R) := by
      funext ω; simp [cf, Nat.pos_iff_ne_zero.mp hl]
    rw [e]
    have hm : Measurable[M.F (tg p.T L l)]
        (fun ω => max (-R) (min (cint M L (l - 1) ω / hL p L) R)) :=
      measurable_const.max ((h.measurable.div_const _).min measurable_const)
    exact hm.stronglyMeasurable

lemma abs_clamp_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |max (-R) (min x R)| ≤ R :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma abs_clamp_le_abs {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |max (-R) (min x R)| ≤ |x| := by
  refine abs_le.mpr ⟨?_, max_le (by linarith [abs_nonneg x]) ((min_le_left _ _).trans (le_abs_self x))⟩
  exact (le_min (neg_abs_le x) (by linarith [abs_nonneg x])).trans (le_max_right _ _)

lemma abs_clamp_sub_le (R x y : ℝ) :
    |max (-R) (min x R) - max (-R) (min y R)| ≤ |x - y| := by
  have h1 : |max (-R) (min x R) - max (-R) (min y R)| ≤ |min x R - min y R| := by
    simpa using abs_max_sub_max_le_max (-R) (min x R) (-R) (min y R)
  have h2 : |min x R - min y R| ≤ |x - y| := by
    simpa using abs_min_sub_min_le_max x R y R
  exact h1.trans h2

lemma cf_bdd (M : Model p Ω) (L : ℕ) {R : ℝ} (hR : 0 ≤ R) (l : ℕ) (ω : Ω) :
    |cf M L R l ω| ≤ R := by
  unfold cf
  split_ifs
  · simpa using hR
  · exact abs_clamp_le hR _

/-- Cauchy-Schwarz on one interval. -/
lemma cs_cell {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ u in a..b, f u) ^ 2 ≤ (b - a) * ∫ u in a..b, f u ^ 2 := by
  set I := ∫ u in a..b, f u
  set S := ∫ u in a..b, f u ^ 2
  have hq : ∀ x : ℝ, 0 ≤ (b - a) * (x * x) + (-2 * I) * x + S := by
    intro x
    have h0 : 0 ≤ ∫ u in a..b, (f u - x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
    have hfun : (fun u => (f u - x) ^ 2) = fun u => (x * x + (-2 * x) * f u) + f u ^ 2 := by
      funext u; ring
    have i1 : IntervalIntegrable (fun u => f u) MeasureTheory.volume a b := hf.intervalIntegrable a b
    have i2 : IntervalIntegrable (fun u => f u ^ 2) MeasureTheory.volume a b :=
      (hf.pow 2).intervalIntegrable a b
    rw [hfun, intervalIntegral.integral_add (intervalIntegrable_const.add (i1.const_mul _)) i2,
      intervalIntegral.integral_add intervalIntegrable_const (i1.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at h0
    nlinarith [h0]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

lemma cf_sq_le (M : Model p Ω) (hM : M.Standing) (L : ℕ) {R : ℝ} (hR : 0 ≤ R) (l : ℕ) (ω : Ω) :
    hL p L * cf M L R (l + 1) ω ^ 2 ≤
      ∫ u in (tg p.T L l : ℝ)..(tg p.T L (l + 1) : ℝ), (Y M u.toNNReal ω) ^ 2 := by
  have hab : (tg p.T L l : ℝ) ≤ tg p.T L (l + 1) :=
    NNReal.coe_le_coe.mpr (tg_mono _ _ (Nat.le_succ l))
  have hint0 : 0 ≤ ∫ u in (tg p.T L l : ℝ)..(tg p.T L (l + 1) : ℝ), (Y M u.toNNReal ω) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
  have hcs := cs_cell (Yr_cont M hM ω) hab
  rw [tg_succ_sub] at hcs
  have hcf : |cf M L R (l + 1) ω| ≤ |cint M L l ω / hL p L| := by
    simp only [cf, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    exact abs_clamp_le_abs hR _
  have hsq : cf M L R (l + 1) ω ^ 2 ≤ (cint M L l ω / hL p L) ^ 2 := sq_le_sq.mpr hcf
  rcases (hL_nonneg p L).eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hint0
  · calc hL p L * cf M L R (l + 1) ω ^ 2 ≤ hL p L * (cint M L l ω / hL p L) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hpos.le
      _ = (cint M L l ω) ^ 2 / hL p L := by field_simp
      _ ≤ (hL p L * ∫ u in (tg p.T L l : ℝ)..(tg p.T L (l + 1) : ℝ), (Y M u.toNNReal ω) ^ 2) /
            hL p L := by
          apply div_le_div_of_nonneg_right _ hpos.le
          unfold cint hL; exact hcs
      _ = _ := by field_simp

/-- `Σ_{k ≤ K} h cf_k² ≤ ∫_0^{t_K} (Xσ)²`. -/
lemma sum_cf_sq_le (M : Model p Ω) (hM : M.Standing) (L : ℕ) {R : ℝ} (hR : 0 ≤ R) (ω : Ω) (K : ℕ) :
    ∑ k ∈ range (K + 1), hL p L * cf M L R k ω ^ 2 ≤
      ∫ u in (0 : ℝ)..(tg p.T L K : ℝ), (Y M u.toNNReal ω) ^ 2 := by
  induction K with
  | zero => simp [cf_zero, tg]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hii : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => (Y M u.toNNReal ω) ^ 2)
        MeasureTheory.volume a b := fun a b => ((Yr_cont M hM ω).pow 2).intervalIntegrable a b
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 (tg p.T L K)) (hii _ _)]
    exact add_le_add ih (cf_sq_le M hM L hR K ω)

/-- The dominating variable `V = ∫_0^T (Xσ)²`. -/
noncomputable def V (M : Model p Ω) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..(p.T : ℝ), (Y M u.toNNReal ω) ^ 2

lemma V_nonneg (M : Model p Ω) (ω : Ω) : 0 ≤ V M ω :=
  intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) (fun u _ => sq_nonneg _)

lemma int_le_V (M : Model p Ω) (hM : M.Standing) (ω : Ω) {s : ℝ≥0} (hs : s ≤ p.T) :
    ∫ u in (0 : ℝ)..(s : ℝ), (Y M u.toNNReal ω) ^ 2 ≤ V M ω := by
  unfold V
  exact intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg _)
    (NNReal.coe_le_coe.mpr hs) (Eventually.of_forall fun u => sq_nonneg _)
    (((Yr_cont M hM ω).pow 2).intervalIntegrable _ _)

/-- Main A-bound: any coefficients dominated by `cf` have `Σ h a² ≤ V` over the whole grid. -/
lemma Aseq_le_V (M : Model p Ω) (hM : M.Standing) (L : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (a : ℕ → Ω → ℝ) (ha : ∀ k ω, |a k ω| ≤ |cf M L R k ω|) (ω : Ω) :
    ∑ k ∈ range (2 ^ L + 1), hL p L * a k ω ^ 2 ≤ V M ω := by
  refine (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (sq_le_sq.mpr (ha k ω))
    (hL_nonneg p L)).trans ((sum_cf_sq_le M hM L hR ω (2 ^ L)).trans
      (int_le_V M hM ω (tg_le_T _ le_rfl)))

/-! ### G4b: under `P`, the cell-average sums against `B` converge to `J` at dyadic times. -/

lemma hL_pos (p : Params) (L : ℕ) : 0 < hL p L := by
  unfold hL; exact div_pos (NNReal.coe_pos.mpr p.hT) (by positivity)

lemma hL_tendsto (p : Params) : Tendsto (fun L => hL p L) atTop (𝓝 0) := by
  unfold hL
  exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Pathwise: cell averages approach the right-end values uniformly on the grid. -/
lemma gap_path (M : Model p Ω) (hM : M.Standing) (ω : Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ∀ l, l + 1 ≤ 2 ^ L →
      |cint M L l ω / hL p L - Y M (tg p.T L (l + 1)) ω| ≤ ε := by
  have huc : UniformContinuousOn (fun u : ℝ => Y M u.toNNReal ω) (Set.Icc 0 (p.T : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (Yr_cont M hM ω).continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc ε hε
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp ((hL_tendsto p).eventually (gt_mem_nhds hδ))
  refine ⟨L0, fun L hLL l hl => ?_⟩
  have hh := hL_pos p L
  have hab : (tg p.T L l : ℝ) ≤ tg p.T L (l + 1) :=
    NNReal.coe_le_coe.mpr (tg_mono _ _ (Nat.le_succ l))
  have hba : (tg p.T L (l + 1) : ℝ) - tg p.T L l = hL p L := tg_succ_sub _ _ _
  have hbT : (tg p.T L (l + 1) : ℝ) ≤ p.T := NNReal.coe_le_coe.mpr (tg_le_T _ hl)
  have ha0 : (0 : ℝ) ≤ tg p.T L l := NNReal.coe_nonneg _
  have hYb : Y M (tg p.T L (l + 1)) ω = Y M ((tg p.T L (l + 1) : ℝ)).toNNReal ω := by
    rw [Real.toNNReal_coe]
  have hint : cint M L l ω - hL p L * Y M (tg p.T L (l + 1)) ω =
      ∫ u in (tg p.T L l : ℝ)..(tg p.T L (l + 1) : ℝ),
        (Y M u.toNNReal ω - Y M ((tg p.T L (l + 1) : ℝ)).toNNReal ω) := by
    rw [intervalIntegral.integral_sub ((Yr_cont M hM ω).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, hba, ← hYb]
    rfl
  have hbound : |∫ u in (tg p.T L l : ℝ)..(tg p.T L (l + 1) : ℝ),
        (Y M u.toNNReal ω - Y M ((tg p.T L (l + 1) : ℝ)).toNNReal ω)| ≤ ε * hL p L := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (tg p.T L l : ℝ))
      (b := (tg p.T L (l + 1) : ℝ)) (C := ε)
      (f := fun u => Y M u.toNNReal ω - Y M ((tg p.T L (l + 1) : ℝ)).toNNReal ω) ?_
    · rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), hba] at this
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    refine hδc x ⟨by linarith [hx.1], by linarith [hx.2]⟩ _ ⟨by linarith, hbT⟩ ?_
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1, (hL0 L hLL).le]
  have e : cint M L l ω / hL p L - Y M (tg p.T L (l + 1)) ω =
      (cint M L l ω - hL p L * Y M (tg p.T L (l + 1)) ω) / hL p L := by
    field_simp
  rw [e, hint, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  exact hbound

/-- Truncated cell-average step sum against an integrator `Z` (cells `l < 2^m k`, level `N+m`). -/
noncomputable def SS (M : Model p Ω) (N k m : ℕ) (Z : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ l ∈ range (2 ^ (N + m)), (if l < 2 ^ m * k then cf M (N + m) m l ω else 0) *
    (Z (tg p.T (N + m) (l + 1)) ω - Z (tg p.T (N + m) l) ω)

/-- Gap coefficients: cell averages minus truncated left points. -/
noncomputable def Dg (M : Model p Ω) (N k m l : ℕ) (ω : Ω) : ℝ :=
  if 0 < l ∧ l < 2 ^ m * k then cf M (N + m) m l ω - clampH (Y M) m (tg p.T (N + m) l) ω else 0

lemma Dg_measF (M : Model p Ω) (hM : M.Standing) (N k m l : ℕ) :
    Measurable[M.F (tg p.T (N + m) l)] (Dg M N k m l) := by
  unfold Dg
  split_ifs
  · exact (cf_measF M hM _ _ l).measurable.sub (clampH_measurable (Y_measF M hM _).measurable _)
  · exact measurable_const

lemma Dg_path (M : Model p Ω) (hM : M.Standing) {N k : ℕ} (hk : k ≤ 2 ^ N) (ω : Ω) {ε : ℝ}
    (hε : 0 < ε) : ∃ m0 : ℕ, ∀ m ≥ m0, ∀ l, |Dg M N k m l ω| ≤ ε := by
  obtain ⟨L0, hL0⟩ := gap_path M hM ω hε
  refine ⟨L0, fun m hm l => ?_⟩
  unfold Dg
  split_ifs with h
  · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, (Nat.sub_add_cancel h.1).symm⟩
    have hl : l' + 1 ≤ 2 ^ (N + m) := by
      have : 2 ^ m * k ≤ 2 ^ (N + m) := by
        rw [pow_add, mul_comm (2 ^ N)]; exact Nat.mul_le_mul_left _ hk
      omega
    have hc : cf M (N + m) m (l' + 1) ω = max (-(m : ℝ)) (min (cint M (N + m) l' ω / hL p (N + m)) m) := by
      simp [cf]
    rw [hc]
    exact (abs_clamp_sub_le _ _ _).trans (hL0 (N + m) (by omega) l' hl)
  · simpa using hε.le

lemma Dg_small (M : Model p Ω) (hM : M.Standing) {N k : ℕ} (hk : k ≤ 2 ^ N) {ε : ℝ}
    (hε : 0 < ε) : ∃ A : ℕ → Set Ω, Tendsto (fun m => M.P (A m)) atTop (𝓝 0) ∧
      ∀ m ω, ω ∉ A m → ∀ l < 2 ^ (N + m), |Dg M N k m l ω| ≤ ε := by
  haveI := hM.prob
  set A' : ℕ → Set Ω := fun m => ⋃ l : ℕ, {ω | ε < |Dg M N k m l ω|} with hA'
  set A : ℕ → Set Ω := fun m => ⋃ m' : ℕ, ⋃ (_ : m ≤ m'), A' m' with hA
  have hA'm : ∀ m, MeasurableSet (A' m) := fun m => MeasurableSet.iUnion fun l =>
    measurableSet_lt measurable_const
      (((Dg_measF M hM N k m l).mono (M.F.le _) le_rfl).abs)
  have hAm : ∀ m, MeasurableSet (A m) := fun m =>
    MeasurableSet.iUnion fun m' => MeasurableSet.iUnion fun _ => hA'm m'
  have hanti : Antitone A := fun a b hab =>
    Set.iUnion_mono fun m' => Set.iUnion_subset fun h => Set.subset_iUnion_of_subset (hab.trans h) subset_rfl
  have hempty : (⋂ m, A m) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨m0, hm0⟩ := Dg_path M hM hk ω hε
    refine ⟨m0, ?_⟩
    simp only [hA, hA', Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt]
    intro m' hm' l
    exact hm0 m' hm' l
  refine ⟨A, ?_, fun m ω hω l _ => ?_⟩
  · have := tendsto_measure_iInter_atTop (μ := M.P) (fun m => (hAm m).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rwa [hempty, measure_empty] at this
  · by_contra hc
    exact hω (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨le_rfl,
      Set.mem_iUnion.mpr ⟨l, lt_of_not_ge hc⟩⟩⟩)

lemma tg_one_tendsto (p : Params) (N : ℕ) :
    Tendsto (fun m : ℕ => tg p.T (N + m) 1) atTop (𝓝 0) := by
  rw [← NNReal.tendsto_coe]
  simp only [tg_coe, Nat.cast_one, one_mul, NNReal.coe_zero]
  exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
    (tendsto_atTop_mono (fun m => Nat.le_add_left m N) tendsto_id))

/-- **G4b**: cell-average sums against `B` converge in `P`-probability to `J` at grid time `t^N_k`. -/
theorem SS_B_tendsto (M : Model p Ω) (hM : M.Standing) {N k : ℕ} (hk : k ≤ 2 ^ N) :
    TendstoInMeasure M.P (fun m => SS M N k m M.B) atTop (M.J (tg p.T N k)) := by
  haveI := hM.prob
  have hW := isStandardBrownian M hM
  have hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (Y M) M.J := hasIto_B M hM hM.X_ito
  have hpart := partialSum_tendsto_of_hasBrownianItoIntegral hW 0 0
    (meas_cBP_of_F M hM (Y_measF M hM)) (Y_cont M hM) hJ p.T N k hk
  have hD := itoStepSum_tendstoInMeasure_zero_of_small hW 0 p.T 0 (fun m => N + m)
    (fun m => Dg M N k m) (fun m l _ => (Dg_measF M hM N k m l).mono (F_le_cBP M hM _) le_rfl)
    (fun m => ⟨2 * m, fun l _ ω => by
      unfold Dg
      split_ifs
      · have h1 := cf_bdd M (N + m) (Nat.cast_nonneg (α := ℝ) m) l ω
        have h2 := abs_clampH_le (Y M) (Nat.cast_nonneg (α := ℝ) m) (tg p.T (N + m) l) ω
        calc _ ≤ |cf M (N + m) m l ω| + |clampH (Y M) m (tg p.T (N + m) l) ω| := abs_sub _ _
          _ ≤ _ := by linarith
      · rw [abs_zero]; positivity⟩)
    (fun ε hε => Dg_small M hM hk hε)
  -- the cell-0 left-point term
  set c0 : ℕ → Ω → ℝ := fun m ω =>
    if 0 < 2 ^ m * k then clampH (Y M) m (dyTime p.T (N + m) 0) ω else 0 with hc0
  have hE : TendstoInMeasure M.P (fun m ω => c0 m ω *
      (gB M (tg p.T (N + m) 1) ω - gB M (tg p.T (N + m) 0) ω)) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun m => ?_) (Eventually.of_forall fun ω => ?_)
    · refine (Measurable.mul ?_ ((gB_measurable M hM _).sub (gB_measurable M hM _))).aestronglyMeasurable
      simp only [hc0]
      split_ifs
      · exact clampH_measurable ((Y_measF M hM _).measurable.mono (M.F.le _) le_rfl) _
      · exact measurable_const
    · have hg : Tendsto (fun m => gB M (tg p.T (N + m) 1) ω - gB M (tg p.T (N + m) 0) ω)
          atTop (𝓝 0) := by
        have h1 := ((gB_cont M ω).tendsto 0).comp (tg_one_tendsto p N)
        have h0 : ∀ m, tg p.T (N + m) 0 = 0 := fun m => by simp [tg]
        simp only [h0]
        simpa using h1.sub_const (gB M 0 ω)
      have hb : ∀ m, |c0 m ω| ≤ |Y M 0 ω| := fun m => by
        simp only [hc0]
        split_ifs
        · simpa [clampH, dyTime] using abs_clamp_le_abs (Nat.cast_nonneg (α := ℝ) m) (Y M 0 ω)
        · simp
      refine squeeze_zero_norm (fun m => ?_) (by simpa using hg.abs.const_mul |Y M 0 ω|)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb m) (abs_nonneg _)
  have hsum := tendstoInMeasure_sub_real (tendstoInMeasure_add_real hpart hD) hE
  refine TendstoInMeasure.congr' (Eventually.of_forall fun m => ?_)
    (Eventually.of_forall fun ω => by simp only [add_zero, sub_zero]; rfl) hsum
  filter_upwards [ae_W M hM] with ω hω
  have hB : ∀ t, M.B t ω = gB M t ω := fun t => by rw [← (hω t).1, W_zero]
  have h0mem : 0 ∈ range (2 ^ (N + m)) := Finset.mem_range.mpr (by positivity)
  simp only [itoStepSum, SS, hB, W_zero]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.add_sum_erase _ _ h0mem, ← Finset.add_sum_erase _ _ h0mem]
  have hsd : ∀ l ∈ (range (2 ^ (N + m))).erase 0,
      (if l < 2 ^ m * k then clampH (Y M) (↑m) (dyTime p.T (N + m) l) ω else 0) *
          (gB M (((l : ℝ≥0) + 1) * p.T / 2 ^ (N + m)) ω - gB M ((l : ℝ≥0) * p.T / 2 ^ (N + m)) ω) +
        Dg M N k m l ω *
          (gB M (((l : ℝ≥0) + 1) * p.T / 2 ^ (N + m)) ω - gB M ((l : ℝ≥0) * p.T / 2 ^ (N + m)) ω) =
      (if l < 2 ^ m * k then cf M (N + m) (↑m) l ω else 0) *
          (gB M (tg p.T (N + m) (l + 1)) ω - gB M (tg p.T (N + m) l) ω) := by
    intro l hl
    have hl0 : 0 < l := Nat.pos_of_ne_zero (Finset.mem_erase.mp hl).1
    have ht1 : tg p.T (N + m) (l + 1) = ((l : ℝ≥0) + 1) * p.T / 2 ^ (N + m) := by
      simp [tg]
    have ht0 : tg p.T (N + m) l = (l : ℝ≥0) * p.T / 2 ^ (N + m) := rfl
    rw [ht1, ht0, ← add_mul]
    congr 1
    unfold Dg
    by_cases h1 : l < 2 ^ m * k
    · simp only [h1, hl0, and_self, if_true, dyTime, tg]; ring
    · simp [h1]
  rw [Finset.sum_congr rfl hsd]
  simp only [hc0, Dg, lt_irrefl, false_and, if_false, cf_zero, ite_self, zero_mul, add_zero,
    zero_add, dyTime, tg, Nat.cast_zero, zero_mul, zero_div, Nat.cast_add, Nat.cast_one]
  ring

/-! ### G4c: the drift sums converge pathwise. -/

lemma er_cont (M : Model p Ω) (hM : M.Standing) (ω : Ω) :
    Continuous fun u : ℝ => M.η u.toNNReal ω := (η_cont' M hM ω).comp continuous_real_toNNReal

lemma sum_ite_range {n K : ℕ} (hK : K ≤ n) (f : ℕ → ℝ) :
    ∑ l ∈ range n, (if l < K then f l else 0) = ∑ l ∈ range K, f l := by
  rw [← Finset.sum_range_add_sum_Ico _ hK]
  have h1 : ∑ l ∈ range K, (if l < K then f l else 0) = ∑ l ∈ range K, f l :=
    Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_range.mp hl)
  have h2 : ∑ l ∈ Ico K n, (if l < K then f l else 0) = 0 :=
    Finset.sum_eq_zero fun l hl => if_neg (not_lt.mpr (Finset.mem_Ico.mp hl).1)
  rw [h1, h2, add_zero]

lemma K_le (N k m : ℕ) (hk : k ≤ 2 ^ N) : 2 ^ m * k ≤ 2 ^ (N + m) := by
  rw [pow_add, mul_comm (2 ^ N)]; exact Nat.mul_le_mul_left _ hk

lemma tg_K (T : ℝ≥0) (N k m : ℕ) : tg T (N + m) (2 ^ m * k) = tg T N k := by
  rw [mul_comm]; exact tg_scale T N m k

/-- Uniform cell error of the cell-average coefficients on cells `l + 1 ≥ 1`. -/
lemma cell_err (M : Model p Ω) (hM : M.Standing) (N : ℕ) (ω : Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ m ≥ m0, ∀ l, l + 2 ≤ 2 ^ (N + m) →
      ∀ u ∈ Set.Icc (tg p.T (N + m) (l + 1) : ℝ) (tg p.T (N + m) (l + 2)),
        |cf M (N + m) m (l + 1) ω - Y M u.toNNReal ω| ≤ 2 * ε := by
  have huc : UniformContinuousOn (fun u : ℝ => Y M u.toNNReal ω) (Set.Icc 0 (p.T : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (Yr_cont M hM ω).continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc ε hε
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (p.T : ℝ))).exists_bound_of_continuousOn
    (Yr_cont M hM ω).continuousOn
  obtain ⟨L0, hL0⟩ := gap_path M hM ω hε
  obtain ⟨L1, hL1⟩ := eventually_atTop.mp ((hL_tendsto p).eventually (gt_mem_nhds hδ))
  refine ⟨max (max L0 L1) ⌈S⌉₊, fun m hm l hl u hu => ?_⟩
  have hm0 : L0 ≤ N + m := by
    have := le_max_left L0 L1; have := le_max_left (max L0 L1) ⌈S⌉₊; omega
  have hm1 : L1 ≤ N + m := by
    have := le_max_right L0 L1; have := le_max_left (max L0 L1) ⌈S⌉₊; omega
  have hmS : S ≤ m := (Nat.le_ceil S).trans (by exact_mod_cast (le_max_right _ _).trans hm)
  have hh := hL_pos p (N + m)
  have hab : (tg p.T (N + m) l : ℝ) ≤ tg p.T (N + m) (l + 1) :=
    NNReal.coe_le_coe.mpr (tg_mono _ _ (Nat.le_succ l))
  have hb1T : (tg p.T (N + m) (l + 1) : ℝ) ≤ p.T := NNReal.coe_le_coe.mpr (tg_le_T _ (by omega))
  have hb2T : (tg p.T (N + m) (l + 2) : ℝ) ≤ p.T := NNReal.coe_le_coe.mpr (tg_le_T _ hl)
  have havg : |cint M (N + m) l ω / hL p (N + m)| ≤ S := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (tg p.T (N + m) l : ℝ))
      (b := (tg p.T (N + m) (l + 1) : ℝ)) (C := S) (f := fun u => Y M u.toNNReal ω) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), tg_succ_sub] at this
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).mpr this
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    exact hS x ⟨(NNReal.coe_nonneg _).trans hx.1.le, hx.2.trans hb1T⟩
  have hcf : cf M (N + m) m (l + 1) ω = cint M (N + m) l ω / hL p (N + m) := by
    simp only [cf, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have h' := abs_le.mp (havg.trans hmS)
    rw [min_eq_left h'.2, max_eq_right h'.1]
  rw [hcf]
  have h1 := hL0 (N + m) hm0 l (by omega)
  have h3 : (tg p.T (N + m) (l + 2) : ℝ) - tg p.T (N + m) (l + 1) = hL p (N + m) :=
    tg_succ_sub p.T (N + m) (l + 1)
  have h2 : |Y M (tg p.T (N + m) (l + 1)) ω - Y M u.toNNReal ω| ≤ ε := by
    have hYb : Y M (tg p.T (N + m) (l + 1)) ω =
        Y M ((tg p.T (N + m) (l + 1) : ℝ)).toNNReal ω := by rw [Real.toNNReal_coe]
    rw [hYb, ← Real.dist_eq]
    refine hδc _ ⟨NNReal.coe_nonneg _, hb1T⟩ u
      ⟨le_trans (le_trans (NNReal.coe_nonneg _) hab) hu.1, hu.2.trans hb2T⟩ ?_
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]
    linarith [hu.2, (hL1 (N + m) hm1).le]
  calc _ ≤ |cint M (N + m) l ω / hL p (N + m) - Y M (tg p.T (N + m) (l + 1)) ω| +
        |Y M (tg p.T (N + m) (l + 1)) ω - Y M u.toNNReal ω| := abs_sub_le _ _ _
    _ ≤ ε + ε := add_le_add h1 h2
    _ = 2 * ε := by ring

/-- **G4c**: pathwise convergence of the drift sums to `∫_0^{t^N_k} Xσ η`. -/
theorem SS_drift (M : Model p Ω) (hM : M.Standing) {N k : ℕ} (hk : k ≤ 2 ^ N) (ω : Ω) :
    Tendsto (fun m => SS M N k m (fun t ω => ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω) ω)
      atTop (𝓝 (∫ u in (0 : ℝ)..(tg p.T N k : ℝ), Y M u.toNNReal ω * M.η u.toNNReal ω)) := by
  have hT : (0 : ℝ) < p.T := NNReal.coe_pos.mpr p.hT
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (p.T : ℝ))).exists_bound_of_continuousOn
    (Yr_cont M hM ω).continuousOn
  obtain ⟨E, hE⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (p.T : ℝ))).exists_bound_of_continuousOn
    (er_cont M hM ω).continuousOn
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 ⟨le_rfl, hT.le⟩)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0 ⟨le_rfl, hT.le⟩)
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  have hpos : 0 < 4 * (E * p.T + 1) := by positivity
  set ε := ε' / (4 * (E * p.T + 1)) with hεdef
  have hε : 0 < ε := div_pos hε' hpos
  have hε'eq : ε' = ε * (4 * (E * p.T + 1)) := by rw [hεdef]; field_simp
  obtain ⟨m0, hm0⟩ := cell_err M hM N ω hε
  have hlim : Tendsto (fun m : ℕ => S * E * hL p (N + m)) atTop (𝓝 0) := by
    have := (hL_tendsto p).comp (tendsto_atTop_mono (fun m => Nat.le_add_left m N) tendsto_id)
    simpa using this.const_mul (S * E)
  obtain ⟨m1, hm1⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hε')))
  refine ⟨max m0 m1, fun m hm => ?_⟩
  have hmm0 : m0 ≤ m := (le_max_left _ _).trans hm
  have hmm1 : m1 ≤ m := (le_max_right _ _).trans hm
  have hKL : 2 ^ m * k ≤ 2 ^ (N + m) := K_le N k m hk
  have hh := hL_pos p (N + m)
  have hinc : ∀ l, (∫ u in (0 : ℝ)..(tg p.T (N + m) (l + 1) : ℝ), M.η u.toNNReal ω) -
      ∫ u in (0 : ℝ)..(tg p.T (N + m) l : ℝ), M.η u.toNNReal ω =
      ∫ u in (tg p.T (N + m) l : ℝ)..(tg p.T (N + m) (l + 1) : ℝ), M.η u.toNNReal ω := fun l =>
    intervalIntegral.integral_interval_sub_left ((er_cont M hM ω).intervalIntegrable _ _)
      ((er_cont M hM ω).intervalIntegrable _ _)
  have hSS : SS M N k m (fun t ω => ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω) ω =
      ∑ l ∈ range (2 ^ m * k), cf M (N + m) m l ω *
        ∫ u in (tg p.T (N + m) l : ℝ)..(tg p.T (N + m) (l + 1) : ℝ), M.η u.toNNReal ω := by
    unfold SS
    simp only [hinc, ite_mul, zero_mul]
    exact sum_ite_range hKL _
  have htarget : ∫ u in (0 : ℝ)..(tg p.T N k : ℝ), Y M u.toNNReal ω * M.η u.toNNReal ω =
      ∑ l ∈ range (2 ^ m * k), ∫ u in (tg p.T (N + m) l : ℝ)..(tg p.T (N + m) (l + 1) : ℝ),
        Y M u.toNNReal ω * M.η u.toNNReal ω := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun l => (tg p.T (N + m) l : ℝ))
      (f := fun u => Y M u.toNNReal ω * M.η u.toNNReal ω)
      (fun l _ => by exact ((Yr_cont M hM ω).mul (er_cont M hM ω)).intervalIntegrable _ _)]
    have h0 : (tg p.T (N + m) 0 : ℝ) = 0 := by simp [tg]
    simp only [h0, tg_K]
  have hterm : ∀ l, cf M (N + m) m l ω *
        (∫ u in (tg p.T (N + m) l : ℝ)..(tg p.T (N + m) (l + 1) : ℝ), M.η u.toNNReal ω) -
      ∫ u in (tg p.T (N + m) l : ℝ)..(tg p.T (N + m) (l + 1) : ℝ),
        Y M u.toNNReal ω * M.η u.toNNReal ω =
      ∫ u in (tg p.T (N + m) l : ℝ)..(tg p.T (N + m) (l + 1) : ℝ),
        (cf M (N + m) m l ω - Y M u.toNNReal ω) * M.η u.toNNReal ω := by
    intro l
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (f := fun u => cf M (N + m) m l ω * M.η u.toNNReal ω)
      (g := fun u => Y M u.toNNReal ω * M.η u.toNNReal ω)
      (by exact ((er_cont M hM ω).const_mul _).intervalIntegrable _ _)
      (by exact ((Yr_cont M hM ω).mul (er_cont M hM ω)).intervalIntegrable _ _)]
    congr 1; funext u; ring
  have hbound : ∀ l < 2 ^ m * k,
      |∫ u in (tg p.T (N + m) l : ℝ)..(tg p.T (N + m) (l + 1) : ℝ),
        (cf M (N + m) m l ω - Y M u.toNNReal ω) * M.η u.toNNReal ω| ≤
      (if l = 0 then S * E * hL p (N + m) else 0) + 2 * ε * E * hL p (N + m) := by
    intro l hl
    have hab : (tg p.T (N + m) l : ℝ) ≤ tg p.T (N + m) (l + 1) :=
      NNReal.coe_le_coe.mpr (tg_mono _ _ (Nat.le_succ l))
    have hbT : (tg p.T (N + m) (l + 1) : ℝ) ≤ p.T :=
      NNReal.coe_le_coe.mpr (tg_le_T _ (by omega))
    have hlen : |(tg p.T (N + m) (l + 1) : ℝ) - tg p.T (N + m) l| = hL p (N + m) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]; exact tg_succ_sub _ _ _
    have hIcc : ∀ x ∈ Set.uIoc (tg p.T (N + m) l : ℝ) (tg p.T (N + m) (l + 1)),
        x ∈ Set.Icc (0 : ℝ) p.T := by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      exact ⟨(NNReal.coe_nonneg _).trans hx.1.le, hx.2.trans hbT⟩
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (C := S * E)
        (a := (tg p.T (N + m) 0 : ℝ)) (b := (tg p.T (N + m) (0 + 1) : ℝ))
        (f := fun u => (cf M (N + m) m 0 ω - Y M u.toNNReal ω) * M.η u.toNNReal ω) ?_
      · rw [Real.norm_eq_abs, hlen] at this
        simp only [if_true]
        have : 0 ≤ 2 * ε * E * hL p (N + m) := by positivity
        linarith
      intro x hx
      have hx' := hIcc x hx
      rw [cf_zero, zero_sub, norm_mul, norm_neg]
      exact mul_le_mul (hS x hx') (hE x hx') (norm_nonneg _) hS0
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, (Nat.sub_add_cancel hl0).symm⟩
      have := intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * ε * E)
        (a := (tg p.T (N + m) (l' + 1) : ℝ)) (b := (tg p.T (N + m) (l' + 1 + 1) : ℝ))
        (f := fun u => (cf M (N + m) m (l' + 1) ω - Y M u.toNNReal ω) * M.η u.toNNReal ω) ?_
      · rw [Real.norm_eq_abs, hlen] at this
        simp only [Nat.add_one_ne_zero, if_false, zero_add]
        exact this
      intro x hx
      have hx' := hIcc x hx
      rw [Set.uIoc_of_le hab] at hx
      rw [norm_mul, Real.norm_eq_abs]
      have h1 := hm0 m hmm0 l' (by omega) x ⟨hx.1.le, hx.2⟩
      exact mul_le_mul h1 (hE x hx') (norm_nonneg _) (by positivity)
  have hKh : ((2 ^ m * k : ℕ) : ℝ) * hL p (N + m) ≤ p.T := by
    calc ((2 ^ m * k : ℕ) : ℝ) * hL p (N + m) ≤ (2 : ℝ) ^ (N + m) * hL p (N + m) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hKL) hh.le
      _ = p.T := by unfold hL; field_simp
  rw [Real.dist_eq, hSS, htarget, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  have hsum := Finset.sum_le_sum fun l hl => hbound l (Finset.mem_range.mp hl)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hite : (if (0 : ℕ) ∈ range (2 ^ m * k) then S * E * hL p (N + m) else 0) ≤
      S * E * hL p (N + m) := by
    split_ifs
    · exact le_rfl
    · positivity
  have hmain := hm1 m hmm1
  calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := hsum
    _ ≤ S * E * hL p (N + m) + 2 * ε * E * p.T := by
        have : ((2 ^ m * k : ℕ) : ℝ) * (2 * ε * E * hL p (N + m)) ≤ 2 * ε * E * p.T := by
          have h2 : 0 ≤ 2 * ε * E := by positivity
          nlinarith [hKh]
        push_cast at this ⊢
        linarith
    _ < ε' := by
        rw [hε'eq]
        nlinarith [hmain, hε, hE0, hT]

/-! ### G4d: combination; convergence in `P^M`-probability to `X - x₀`. -/

theorem tim_withDensity' {ι : Type*} {l : Filter ι} {P : Measure Ω} [SFinite P]
    {ρ : Ω → ℝ≥0∞} (hρ : ∫⁻ ω, ρ ω ∂P ≠ ∞) {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (h : TendstoInMeasure P f l g) : TendstoInMeasure (P.withDensity ρ) f l g := by
  intro ε hε
  have := tendsto_setLIntegral_zero (μ := P) (f := ρ) hρ
    (s := fun i => {x | ε ≤ edist (f i x) (g x)}) (h ε hε)
  exact this.congr' (Eventually.of_forall fun i => (withDensity_apply' ρ _).symm)

lemma SS_meas (M : Model p Ω) (hM : M.Standing) (N k m : ℕ) {Z : ℝ≥0 → Ω → ℝ}
    (hZ : ∀ t, Measurable (Z t)) : Measurable (SS M N k m Z) := by
  unfold SS
  refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ((hZ _).sub (hZ _))
  split_ifs
  · exact (cf_measF M hM _ _ l).measurable.mono (M.F.le _) le_rfl
  · exact measurable_const

lemma SS_BMx (M : Model p Ω) (N k m : ℕ) (ω : Ω) :
    SS M N k m (BMx M) ω = SS M N k m M.B ω +
      SS M N k m (fun t ω => ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω) ω := by
  unfold SS BMx
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `X = x₀ + J + ∫ Xσ η` on `[0,T]`, `P`-a.s. -/
lemma X_eq_P (M : Model p Ω) (hM : M.Standing) :
    ∀ᵐ ω ∂M.P, ∀ t : ℝ≥0, t ≤ p.T → M.X t ω = p.x₀ + (M.J t ω + ∫ u in (0 : ℝ)..(t : ℝ),
        Y M u.toNNReal ω * M.η u.toNNReal ω) := by
  filter_upwards [hM.X_sde] with ω hω t ht
  rw [hω t ht]
  have e : (fun u : ℝ => Y M u.toNNReal ω * M.η u.toNNReal ω) =
      fun u => M.X u.toNNReal ω * M.μ u.toNNReal ω := by
    funext u
    unfold Model.η Y
    have := (hM.σ_pos u.toNNReal ω).ne'
    field_simp
  rw [e]; ring

/-- **G4d**: under `P` (hence under `P^M`), the cell-average sums against `B^M` converge in
probability to `X_{t^N_k} - x₀`. -/
theorem SS_BMx_tendsto_P (M : Model p Ω) (hM : M.Standing) {N k : ℕ} (hk : k ≤ 2 ^ N) :
    TendstoInMeasure M.P (fun m => SS M N k m (BMx M)) atTop
      (fun ω => M.X (tg p.T N k) ω - p.x₀) := by
  haveI := hM.prob
  have hd : TendstoInMeasure M.P
      (fun m => SS M N k m (fun t ω => ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω)) atTop
      (fun ω => ∫ u in (0 : ℝ)..(tg p.T N k : ℝ), Y M u.toNNReal ω * M.η u.toNNReal ω) :=
    tendstoInMeasure_of_tendsto_ae
      (fun m => (SS_meas M hM N k m fun t =>
        ((intη_measF M hM t).measurable.mono (M.F.le _) le_rfl)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => SS_drift M hM hk ω)
  have hsum := tendstoInMeasure_add_real (SS_B_tendsto M hM hk) hd
  refine TendstoInMeasure.congr' (Eventually.of_forall fun m =>
    Eventually.of_forall fun ω => (SS_BMx M N k m ω).symm) ?_ hsum
  filter_upwards [X_eq_P M hM] with ω hω
  rw [hω _ (tg_le_T _ hk)]
  ring

theorem SS_BMx_tendsto_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {N k : ℕ}
    (hk : k ≤ 2 ^ N) :
    TendstoInMeasure M.PM (fun m => SS M N k m (BMx M)) atTop
      (fun ω => M.X (tg p.T N k) ω - p.x₀) := by
  haveI := hM.prob
  unfold Model.PM
  exact tim_withDensity' ((h5.2 p.T le_rfl).integrable one_le_two).lintegral_lt_top.ne
    (SS_BMx_tendsto_P M hM hk)

end StochCalcG4

/-! G5p (8c066573 relay 9, pure Mathlib + G3): dyadic tail bound from `IncrHyp` + `Aseq ≤ V`,
uniform L1 bound from UI + tails, and the Vitali step `∫ S_m = 0 → ∫ lim = 0`. -/

namespace StochCalcG5p

open MeasureTheory ProbabilityTheory Filter Finset StochCalcG3
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma integrable_min_one {Q : Measure Ω} [IsFiniteMeasure Q] {V : Ω → ℝ} (hVm : Measurable V)
    (hV0 : ∀ ω, 0 ≤ V ω) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun ω => min 1 (V ω / c)) Q := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_const.min (hVm.div_const _)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (div_nonneg (hV0 ω) hc))]
  exact min_le_left _ _

/-- Dyadic tail bound: `Q(2^j ≤ |Σ a D|) ≤ 2 E min(1, V/4^j)` when `Aseq ≤ V`. -/
theorem tail_dyadic {Q : Measure Ω} [IsFiniteMeasure Q] {𝒢 : ℕ → MeasurableSpace Ω}
    {D : ℕ → Ω → ℝ} {h : ℕ → ℝ} (H : IncrHyp Q 𝒢 D h) (a : ℕ → Ω → ℝ)
    (ha : ∀ k, StronglyMeasurable[𝒢 k] (a k)) (haC : ∀ k, ∃ C, ∀ ω, |a k ω| ≤ C) (n : ℕ)
    {V : Ω → ℝ} (hVm : Measurable V) (hV0 : ∀ ω, 0 ≤ V ω) (hAV : ∀ ω, Aseq h a n ω ≤ V ω)
    (j : ℕ) :
    Q {ω | (2 : ℝ) ^ j ≤ |∑ k ∈ range n, a k ω * D k ω|} ≤
      2 * ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q := by
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  have hmain := tail_le H a ha haC n (c := 2 ^ j) (δ := 4 ^ j) (by positivity) h4.le
  have hAm : Measurable (Aseq h a n) := by
    unfold Aseq
    exact Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (((ha k).measurable.mono (H.le k) le_rfl).pow_const 2)
  have hφm : Measurable fun ω => ENNReal.ofReal (min 1 (V ω / 4 ^ j)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (hVm.div_const _))
  have e1 : Q {ω | 4 ^ j < Aseq h a n ω} ≤ ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q := by
    calc Q {ω | 4 ^ j < Aseq h a n ω}
        ≤ Q {ω | 1 ≤ ENNReal.ofReal (min 1 (V ω / 4 ^ j))} := by
          refine measure_mono fun ω hω => ?_
          simp only [Set.mem_setOf_eq] at hω ⊢
          rw [ENNReal.one_le_ofReal]
          exact le_min le_rfl ((one_le_div h4).mpr (hω.le.trans (hAV ω)))
      _ ≤ (∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q) / 1 :=
          meas_ge_le_lintegral_div hφm.aemeasurable one_ne_zero ENNReal.one_ne_top
      _ = _ := div_one _
  have e2 : ENNReal.ofReal ((∫ ω, min (Aseq h a n ω) (4 ^ j) ∂Q) / ((2 : ℝ) ^ j) ^ 2) ≤
      ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q := by
    have hpow : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hpow, ← integral_div, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_min_one hVm hV0 _ h4.le)
      (Eventually.of_forall fun ω => le_min zero_le_one (div_nonneg (hV0 ω) h4.le))]
    refine ENNReal.ofReal_le_ofReal (integral_mono ?_ (integrable_min_one hVm hV0 _ h4.le)
      fun ω => ?_)
    · refine ((integrable_const ((4 : ℝ) ^ j)).mono' (hAm.min measurable_const).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)).div_const _
      have hA0 : 0 ≤ Aseq h a n ω := Aseq_nonneg h H.h_nonneg a n ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hA0 h4.le)]
      exact min_le_right _ _
    · have hA0 : 0 ≤ Aseq h a n ω := Aseq_nonneg h H.h_nonneg a n ω
      simp only
      rw [← min_div_div_right h4.le, div_self h4.ne', min_comm]
      exact min_le_min le_rfl (div_le_div_of_nonneg_right (hAV ω) h4.le)
  calc _ ≤ _ := hmain
    _ ≤ (∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q) +
        ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q := add_le_add e1 e2
    _ = _ := (two_mul _).symm

/-- The dyadic tail bounds tend to zero. -/
lemma tail_bound_tendsto {Q : Measure Ω} [IsFiniteMeasure Q] {V : Ω → ℝ} (hVm : Measurable V)
    (hV0 : ∀ ω, 0 ≤ V ω) :
    Tendsto (fun j : ℕ => ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := Q) (fun _ => 1)
    (F := fun (j : ℕ) ω => ENNReal.ofReal (min 1 (V ω / 4 ^ j))) (f := fun _ => 0)
    (fun j => (ENNReal.measurable_ofReal.comp (measurable_const.min (hVm.div_const _))))
    (fun j => Eventually.of_forall fun ω => by
      simpa using ENNReal.ofReal_le_ofReal (min_le_left 1 (V ω / 4 ^ j)))
    (by simp [measure_ne_top]) (Eventually.of_forall fun ω => ?_)
  · simpa using h
  · have h4 : Tendsto (fun j : ℕ => V ω / 4 ^ j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have h5 : Tendsto (fun j : ℕ => min 1 (V ω / 4 ^ j)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).min h4
    have h6 := ENNReal.tendsto_ofReal h5
    simpa using h6

/-- UI + uniform dyadic tails give a uniform L1 bound. -/
theorem eLpNorm_bdd {Q : Measure Ω} [IsFiniteMeasure Q] {ι : Type*} {S : ι → Ω → ℝ}
    (hSm : ∀ i, Measurable (S i)) (hUI : UnifIntegrable S 1 Q) {V : Ω → ℝ} (hVm : Measurable V)
    (hV0 : ∀ ω, 0 ≤ V ω)
    (hT : ∀ i (j : ℕ), Q {ω | (2 : ℝ) ^ j ≤ |S i ω|} ≤
      2 * ∫⁻ ω, ENNReal.ofReal (min 1 (V ω / 4 ^ j)) ∂Q) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ i, eLpNorm (S i) 1 Q ≤ C := by
  obtain ⟨δ, hδ, hδs⟩ := hUI one_pos
  have ht := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) (tail_bound_tendsto (Q := Q) hVm hV0)
    (Or.inr ENNReal.ofNat_ne_top)
  rw [mul_zero] at ht
  obtain ⟨j0, hj0⟩ := eventually_atTop.mp (ht.eventually (ge_mem_nhds (ENNReal.ofReal_pos.mpr hδ)))
  refine ⟨1 + Q Set.univ * ENNReal.ofReal (2 ^ j0), ?_, fun i => ?_⟩
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top,
      ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top⟩
  set s := {ω | (2 : ℝ) ^ j0 ≤ |S i ω|} with hs
  have hsm : MeasurableSet s := measurableSet_le measurable_const (hSm i).abs
  have h1 : eLpNorm (s.indicator (S i)) 1 Q ≤ 1 := by
    have := hδs i s hsm ((hT i j0).trans (hj0 j0 le_rfl))
    simpa using this
  have h2 : eLpNorm (sᶜ.indicator (S i)) 1 Q ≤ Q Set.univ * ENNReal.ofReal (2 ^ j0) := by
    have := eLpNorm_le_of_ae_bound (μ := Q) (p := 1) (f := sᶜ.indicator (S i)) (C := 2 ^ j0)
      (Eventually.of_forall fun ω => ?_)
    · simpa [mul_comm] using this
    by_cases hω : ω ∈ s
    · simp [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω)]
    · rw [Set.indicator_of_mem (Set.mem_compl hω), Real.norm_eq_abs]
      simp only [hs, Set.mem_setOf_eq, not_le] at hω
      exact hω.le
  calc eLpNorm (S i) 1 Q = eLpNorm (s.indicator (S i) + sᶜ.indicator (S i)) 1 Q := by
        rw [Set.indicator_add_compl_eq_piecewise, Set.piecewise_same]
    _ ≤ eLpNorm (s.indicator (S i)) 1 Q + eLpNorm (sᶜ.indicator (S i)) 1 Q :=
        eLpNorm_add_le (((hSm i).indicator hsm).aestronglyMeasurable)
          (((hSm i).indicator hsm.compl).aestronglyMeasurable) le_rfl
    _ ≤ _ := add_le_add h1 h2

/-- Vitali: mean-zero UI sequences converging in measure have an integrable mean-zero limit. -/
theorem integral_lim_zero {Q : Measure Ω} [IsFiniteMeasure Q] {S : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hSm : ∀ i, Measurable (S i)) (hUI : UnifIntegrable S 1 Q) {C : ℝ≥0∞} (hC : C < ∞)
    (hCb : ∀ i, eLpNorm (S i) 1 Q ≤ C) (hconv : TendstoInMeasure Q S atTop g)
    (h0 : ∀ i, ∫ ω, S i ω ∂Q = 0) : Integrable g Q ∧ ∫ ω, g ω ∂Q = 0 := by
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  have hgm : AEStronglyMeasurable g Q :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hSm (ns n)).aestronglyMeasurable) hae
  have hgL : eLpNorm g 1 Q ≤ C :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hSm (ns n)).aestronglyMeasurable) g hae).trans
      (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => hCb _))
  have hgM : MemLp g 1 Q := ⟨hgm, hgL.trans_lt hC⟩
  have hSM : ∀ i, MemLp (S i) 1 Q := fun i => ⟨(hSm i).aestronglyMeasurable, (hCb i).trans_lt hC⟩
  have hV := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n => (hSm n).aestronglyMeasurable) hgM hUI hconv
  have hI := tendsto_integral_of_L1 g hgm (Eventually.of_forall fun i => (hSM i).integrable le_rfl)
    (by simpa [eLpNorm_one_eq_lintegral_enorm] using hV)
  simp only [h0] at hI
  exact ⟨memLp_one_iff_integrable.mp hgM, (tendsto_nhds_unique hI tendsto_const_nhds)⟩

end StochCalcG5p

/-! G5 (8c066573 relay 10): dyadic `P^M`-martingale identity for `X`.
Pure part: in-measure subtraction, Fatou closure of UI / L1 bounds under a.e. limits.
Model part: `V` measurable and `√V ∈ L¹(P^M)`, generic cell sums `CS` (tail bound, mean zero),
and `dyadic_incr`: for dyadic `u = tg N i ≤ v = tg N j` and `A ∈ F u`,
`∫ 1_A (X v - X u) dP^M = 0`. -/

namespace StochCalcG5

open MeasureTheory ProbabilityTheory Filter Finset StochCalcG3
open scoped NNReal ENNReal Topology

section Pure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tim_sub {Q : Measure Ω} {f f' : ℕ → Ω → ℝ} {g g' : Ω → ℝ}
    (h : TendstoInMeasure Q f atTop g) (h' : TendstoInMeasure Q f' atTop g') :
    TendstoInMeasure Q (fun n ω => f n ω - f' n ω) atTop (fun ω => g ω - g' ω) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hs := (h _ hε2).add (h' _ hε2)
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => bot_le)
    fun n => (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_contra hc
  push_neg at hc
  have hle : edist (f n ω - f' n ω) (g ω - g' ω) ≤ edist (f n ω) (g ω) + edist (f' n ω) (g' ω) := by
    rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
    have := abs_sub (f n ω - g ω) (f' n ω - g' ω)
    rwa [show f n ω - g ω - (f' n ω - g' ω) = f n ω - f' n ω - (g ω - g' ω) by ring] at this
  exact absurd (hω.trans hle) (not_le.mpr ((ENNReal.add_lt_add hc.1 hc.2).trans_eq
    (ENNReal.add_halves ε)))

lemma eLpNorm_ae_lim_le {Q : Measure Ω} {S : ℕ → Ω → ℝ} (hSm : ∀ n, AEStronglyMeasurable (S n) Q)
    {g : Ω → ℝ} (h : ∀ᵐ ω ∂Q, Tendsto (fun n => S n ω) atTop (𝓝 (g ω))) {C : ℝ≥0∞}
    (hC : ∀ n, eLpNorm (S n) 1 Q ≤ C) : eLpNorm g 1 Q ≤ C :=
  (Lp.eLpNorm_lim_le_liminf_eLpNorm hSm g h).trans
    (Filter.liminf_le_of_frequently_le' (Frequently.of_forall hC))

theorem ui_of_ae_lim {Q : Measure Ω} {ι κ : Type*} {S : ι → Ω → ℝ} (hS : UnifIntegrable S 1 Q)
    (hSm : ∀ i, AEStronglyMeasurable (S i) Q) {g : κ → Ω → ℝ}
    (hg : ∀ c, ∃ ns : ℕ → ι, ∀ᵐ ω ∂Q, Tendsto (fun n => S (ns n) ω) atTop (𝓝 (g c ω))) :
    UnifIntegrable g 1 Q := by
  intro ε hε
  obtain ⟨δ, hδ, hδs⟩ := hS hε
  refine ⟨δ, hδ, fun c s hs hQs => ?_⟩
  obtain ⟨ns, hns⟩ := hg c
  refine eLpNorm_ae_lim_le (fun n => (hSm (ns n)).indicator hs) (hns.mono fun ω hω => ?_)
    fun n => hδs (ns n) s hs hQs
  by_cases h : ω ∈ s
  · simpa [Set.indicator_of_mem h] using hω
  · simp [Set.indicator_of_notMem h]

end Pure

open HedgePSNV EthierKurtz ItoLib StochCalcBr StochCalcDG3m StochCalcG4

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma V_measF (M : Model p Ω) (hM : M.Standing) : StronglyMeasurable[M.F p.T] (V M) := by
  unfold V
  by_cases ht0 : p.T = 0
  · simp only [ht0, NNReal.coe_zero, intervalIntegral.integral_same]
    exact stronglyMeasurable_const
  have hT : (0 : ℝ) < p.T := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun n ω => ∑ k ∈ range (2 ^ n), Y M (tg p.T n k) ω ^ 2 * ((p.T : ℝ) / 2 ^ n)) ?_ ?_
  · intro n
    refine Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_
    exact (((Y_measF M hM _).mono (M.F.mono (tg_le_T p.T (Finset.mem_range.mp hk).le))).pow
      2).mul_const _
  · refine tendsto_pi_nhds.mpr fun ω => ?_
    have hg : Continuous fun x : ℝ => Y M x.toNNReal ω ^ 2 := (Yr_cont M hM ω).pow 2
    have hR := StochCalcDG3p.riemann_left hg 0 hT.le (m := fun n => 2 ^ n)
      (δ := fun n => (p.T : ℝ) / 2 ^ n)
      (fun n => div_pos hT (by positivity))
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
      (fun n => by push_cast; field_simp)
    beta_reduce at hR
    rw [zero_add] at hR
    refine hR.congr fun n => Finset.sum_congr rfl fun k _ => ?_
    rw [zero_add, ← tg_coe, Real.toNNReal_coe]

lemma V_meas (M : Model p Ω) (hM : M.Standing) : Measurable (V M) :=
  ((V_measF M hM).mono (M.F.le _)).measurable

lemma Y_meas (M : Model p Ω) (hM : M.Standing) (s : ℝ≥0) : Measurable (Y M s) :=
  ((Y_measF M hM s).mono (M.F.le s)).measurable

/-- Assumption 4 + Tonelli: `E_P V < ∞`. -/
lemma V_int_P (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) : Integrable (V M) M.P := by
  have := hM.prob
  set f : Ω → ℝ → ℝ := fun ω u => Y M u.toNNReal ω ^ 2 with hfdef
  have hfc : ∀ ω, Continuous (f ω) := fun ω => (Yr_cont M hM ω).pow 2
  have hjoint : Measurable (Function.uncurry fun (u : ℝ≥0) (ω : Ω) => Y M u ω) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => Y_cont M hM ω)
      (fun u => Y_meas M hM u)
  have hjf : Measurable (fun q : Ω × ℝ => ENNReal.ofReal (f q.1 q.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have : (fun q : Ω × ℝ => f q.1 q.2) =
        (fun x => x ^ 2) ∘ (Function.uncurry fun (u : ℝ≥0) (ω : Ω) => Y M u ω) ∘
          (fun q : Ω × ℝ => (q.2.toNNReal, q.1)) := by
      funext q; simp [hfdef, Function.uncurry]
    rw [this]
    exact (continuous_pow 2).measurable.comp
      (hjoint.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  have hnn : ∀ ω, 0 ≤ V M ω := V_nonneg M
  have hpt : ∀ ω, ENNReal.ofReal (V M ω) =
      ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ENNReal.ofReal (f ω u) := by
    intro ω
    unfold V
    rw [intervalIntegral.integral_of_le p.T.coe_nonneg,
      ofReal_integral_eq_lintegral_ofReal
        ((hfc ω).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Eventually.of_forall fun u => sq_nonneg _),
      Measure.restrict_congr_set Ioc_ae_eq_Icc]
  unfold Model.Assumption4 at h4
  refine ⟨(V_meas M hM).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
  simp_rw [hpt]
  rw [lintegral_lintegral_swap hjf.aemeasurable]
  simpa [hfdef, Y] using h4

/-- `√V ∈ L¹(P^M)` (Cauchy-Schwarz with `Z_T ∈ L²(P)`). -/
lemma sqrtV_int_PM (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5) :
    Integrable (fun ω => Real.sqrt (V M ω)) M.PM := by
  haveI := hM.prob
  have hZm : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  unfold Model.PM
  rw [integrable_withDensity_iff_integrable_smul' hZm.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hZ2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have hV2 : MemLp (fun ω => Real.sqrt (V M ω)) 2 M.P := by
    rw [memLp_two_iff_integrable_sq (V_meas M hM).sqrt.aestronglyMeasurable]
    refine (V_int_P M hM h4).congr (Eventually.of_forall fun ω => ?_)
    simp only [Real.sq_sqrt (V_nonneg M ω)]
  refine (integrable_mul_of_memLp hZ2 hV2).congr (Eventually.of_forall fun ω => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (show 0 ≤ M.Z p.T ω from Real.exp_nonneg _)]

/-- Generic cell sum against `B^M` increments on the level-`L` grid. -/
noncomputable def CS (M : Model p Ω) (L : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ l ∈ range (2 ^ L), a l ω * (BMx M (tg p.T L (l + 1)) ω - BMx M (tg p.T L l) ω)

lemma CS_meas (M : Model p Ω) (hM : M.Standing) (L : ℕ) (a : ℕ → Ω → ℝ)
    (ha : ∀ l, Measurable (a l)) : Measurable (CS M L a) := by
  unfold CS
  refine Finset.measurable_fun_sum _ fun l _ => (ha l).mul ?_
  exact (((BMx_measF M hM _).mono (M.F.le _)).measurable).sub
    (((BMx_measF M hM _).mono (M.F.le _)).measurable)

theorem CS_tail (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (L : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (a : ℕ → Ω → ℝ) (ha : ∀ l, StronglyMeasurable[M.F (tg p.T L l)] (a l))
    (hac : ∀ l ω, |a l ω| ≤ |cf M L R l ω|) (j : ℕ) :
    M.PM {ω | (2 : ℝ) ^ j ≤ |CS M L a ω|} ≤
      2 * ∫⁻ ω, ENNReal.ofReal (min 1 (V M ω / 4 ^ j)) ∂M.PM := by
  haveI := PM_prob M hM h5
  have H := incrHyp_PM M hM h5 L (fun k => min k (2 ^ L))
    (fun x y hxy => min_le_min_right _ hxy) (fun k => min_le_right _ _)
  set a' : ℕ → Ω → ℝ := fun k => if k < 2 ^ L then a k else 0 with ha'
  have ha'm : ∀ k, StronglyMeasurable[M.F (tg p.T L (min k (2 ^ L)))] (a' k) := by
    intro k
    by_cases hk : k < 2 ^ L
    · simp only [ha', if_pos hk]; rw [min_eq_left hk.le]; exact ha k
    · simp only [ha', if_neg hk]; exact stronglyMeasurable_const
  have ha'le : ∀ k ω, |a' k ω| ≤ |cf M L R k ω| := by
    intro k ω
    by_cases hk : k < 2 ^ L
    · simp only [ha', if_pos hk]; exact hac k ω
    · simp only [ha', if_neg hk, Pi.zero_apply, abs_zero]; exact abs_nonneg _
  have haC : ∀ k, ∃ C, ∀ ω, |a' k ω| ≤ C :=
    fun k => ⟨R, fun ω => (ha'le k ω).trans (cf_bdd M L hR k ω)⟩
  have hAV : ∀ ω, Aseq (fun k => (tg p.T L (min (k + 1) (2 ^ L)) : ℝ) - tg p.T L (min k (2 ^ L)))
      a' (2 ^ L) ω ≤ V M ω := by
    intro ω
    refine le_trans ?_ (Aseq_le_V M hM L hR a' ha'le ω)
    unfold Aseq
    rw [Finset.sum_range_succ]
    refine le_add_of_le_of_nonneg (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
      (mul_nonneg (hL_nonneg p L) (sq_nonneg _))
    have hk' := Finset.mem_range.mp hk
    dsimp only
    rw [min_eq_left hk'.le, min_eq_left (Nat.succ_le_of_lt hk'), tg_succ_sub]
    rfl
  have hT := StochCalcG5p.tail_dyadic H a' ha'm haC (2 ^ L) (V_meas M hM) (V_nonneg M) hAV j
  have hCS : ∀ ω, CS M L a ω = ∑ k ∈ range (2 ^ L), a' k ω *
      (BMx M (tg p.T L (min (k + 1) (2 ^ L))) ω - BMx M (tg p.T L (min k (2 ^ L))) ω) := by
    intro ω
    unfold CS
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    simp only [ha', if_pos hk', min_eq_left hk'.le, min_eq_left (Nat.succ_le_of_lt hk')]
  simp only [hCS]
  exact hT

theorem CS_int (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (L : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (a : ℕ → Ω → ℝ) (ha : ∀ l, StronglyMeasurable[M.F (tg p.T L l)] (a l))
    (hac : ∀ l ω, |a l ω| ≤ |cf M L R l ω|) :
    Integrable (CS M L a) M.PM ∧ ∫ ω, CS M L a ω ∂M.PM = 0 := by
  haveI := PM_prob M hM h5
  have H := incrHyp_PM M hM h5 L (fun k => min k (2 ^ L))
    (fun x y hxy => min_le_min_right _ hxy) (fun k => min_le_right _ _)
  have hterm : ∀ l ∈ range (2 ^ L),
      Integrable (fun ω => a l ω * (BMx M (tg p.T L (l + 1)) ω - BMx M (tg p.T L l) ω)) M.PM ∧
      ∫ ω, a l ω * (BMx M (tg p.T L (l + 1)) ω - BMx M (tg p.T L l) ω) ∂M.PM = 0 := by
    intro l hl
    have hl' := Finset.mem_range.mp hl
    have hm : StronglyMeasurable[M.F (tg p.T L (min l (2 ^ L)))] (a l) := by
      rw [min_eq_left hl'.le]; exact ha l
    have hL2 : MemLp (a l) 2 M.PM :=
      MemLp.of_bound (hm.mono (H.le l)).aestronglyMeasurable R
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact (hac l ω).trans (cf_bdd M L hR l ω))
    have hD := H.memLp l
    have hmean := H.mean l (a l) hm hL2
    simp only [min_eq_left hl'.le, min_eq_left (Nat.succ_le_of_lt hl')] at hD hmean
    exact ⟨integrable_mul_of_memLp hL2 hD, hmean⟩
  refine ⟨?_, ?_⟩
  · unfold CS; exact integrable_finsetSum _ fun l hl => (hterm l hl).1
  · unfold CS
    rw [integral_finsetSum _ fun l hl => (hterm l hl).1]
    exact Finset.sum_eq_zero fun l hl => (hterm l hl).2

/-- Coefficients of `1_A (SS N j m - SS N i m)`. -/
noncomputable def aw (M : Model p Ω) (N i j m : ℕ) (A : Set Ω) (l : ℕ) (ω : Ω) : ℝ :=
  if 2 ^ m * i ≤ l ∧ l < 2 ^ m * j then A.indicator (fun _ => (1 : ℝ)) ω * cf M (N + m) m l ω
  else 0

lemma aw_le (M : Model p Ω) (N i j m : ℕ) (A : Set Ω) (l : ℕ) (ω : Ω) :
    |aw M N i j m A l ω| ≤ |cf M (N + m) (m : ℝ) l ω| := by
  unfold aw
  split_ifs
  · by_cases hω : ω ∈ A <;> simp [hω]
  · simp

lemma aw_measF (M : Model p Ω) (hM : M.Standing) {N i j : ℕ} {A : Set Ω}
    (hA : MeasurableSet[M.F (tg p.T N i)] A) (m l : ℕ) :
    StronglyMeasurable[M.F (tg p.T (N + m) l)] (aw M N i j m A l) := by
  unfold aw
  by_cases h : 2 ^ m * i ≤ l ∧ l < 2 ^ m * j
  · simp only [if_pos h]
    have hle : tg p.T N i ≤ tg p.T (N + m) l := by
      rw [← tg_K p.T N i m]; exact tg_mono p.T (N + m) h.1
    exact (stronglyMeasurable_const.indicator (M.F.mono hle A hA)).mul (cf_measF M hM (N + m) m l)
  · simp only [if_neg h]; exact stronglyMeasurable_const

lemma ind_SS_eq (M : Model p Ω) (N i j m : ℕ) (hij : i ≤ j) (A : Set Ω) (ω : Ω) :
    A.indicator (fun ω => SS M N j m (BMx M) ω - SS M N i m (BMx M) ω) ω =
      CS M (N + m) (aw M N i j m A) ω := by
  unfold SS CS aw
  have h2 : 2 ^ m * i ≤ 2 ^ m * j := Nat.mul_le_mul_left _ hij
  by_cases hA : ω ∈ A
  · rw [Set.indicator_of_mem hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Set.indicator_of_mem hA, one_mul]
    by_cases h1 : l < 2 ^ m * i
    · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 h2), if_neg (fun h => absurd h.1 (not_le.mpr h1))]
      ring
    · by_cases h3 : l < 2 ^ m * j
      · rw [if_neg h1, if_pos h3, if_pos ⟨not_lt.mp h1, h3⟩]; ring
      · rw [if_neg h1, if_neg h3, if_neg (fun h => h3 h.2)]; ring
  · rw [Set.indicator_of_notMem hA]
    symm
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Set.indicator_of_notMem hA]
    split_ifs <;> ring

/-- **G5a**: for dyadic `u = tg N i ≤ v = tg N j` and `A ∈ F u`, `E^M[1_A (X v - X u)] = 0`. -/
theorem dyadic_incr (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    {N i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ N) {A : Set Ω}
    (hA : MeasurableSet[M.F (tg p.T N i)] A) :
    Integrable (A.indicator fun ω => M.X (tg p.T N j) ω - M.X (tg p.T N i) ω) M.PM ∧
      ∫ ω, A.indicator (fun ω => M.X (tg p.T N j) ω - M.X (tg p.T N i) ω) ω ∂M.PM = 0 := by
  haveI := PM_prob M hM h5
  set S : ℕ → Ω → ℝ := fun m => CS M (N + m) (aw M N i j m A) with hS
  have ham : ∀ m l, StronglyMeasurable[M.F (tg p.T (N + m) l)] (aw M N i j m A l) :=
    fun m l => aw_measF M hM hA m l
  have hSm : ∀ m, Measurable (S m) := fun m =>
    CS_meas M hM (N + m) _ fun l => ((ham m l).mono (M.F.le _)).measurable
  have hT : ∀ m (k : ℕ), M.PM {ω | (2 : ℝ) ^ k ≤ |S m ω|} ≤
      2 * ∫⁻ ω, ENNReal.ofReal (min 1 (V M ω / 4 ^ k)) ∂M.PM := fun m k =>
    CS_tail M hM h5 (N + m) (Nat.cast_nonneg m) _ (ham m) (aw_le M N i j m A) k
  have hUI := unifIntegrable_of_dyadic_tail S hSm (V M) (V_meas M hM) (V_nonneg M)
    (sqrtV_int_PM M hM h4 h5) hT
  obtain ⟨C, hC, hCb⟩ := StochCalcG5p.eLpNorm_bdd hSm hUI (V_meas M hM) (V_nonneg M) hT
  have hconv : TendstoInMeasure M.PM S atTop
      (A.indicator fun ω => M.X (tg p.T N j) ω - M.X (tg p.T N i) ω) := by
    have h1 := tim_sub (SS_BMx_tendsto_PM M hM h5 hj) (SS_BMx_tendsto_PM M hM h5 (hij.trans hj))
    have h2 := h1.indicator A
    refine TendstoInMeasure.congr_left
      (fun m => Eventually.of_forall fun ω => ind_SS_eq M N i j m hij A ω)
      (TendstoInMeasure.congr_right (Eventually.of_forall fun ω => ?_) h2)
    by_cases hω : ω ∈ A <;> simp [hω]
  exact StochCalcG5p.integral_lim_zero hSm hUI hC hCb hconv fun m =>
    (CS_int M hM h5 (N + m) (Nat.cast_nonneg m) _ (ham m) (aw_le M N i j m A)).2

end StochCalcG5

/-! G5b = K1 (8c066573 relay 10): `X` is a `P^M`-martingale on `[0,T]`.
UI + L1 bound for all dyadic `X(tg N k) - x₀` (Fatou closure of the cell-sum family), dyadic
approximation from above `kup`, Vitali (`StochCalcG5p.integral_lim_zero`), then
`ae_eq_condExp_of_forall_setIntegral_eq`. -/

namespace StochCalcG5

open MeasureTheory ProbabilityTheory Filter Finset StochCalcG3
open scoped NNReal ENNReal Topology

section Pure2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem ui_ind_sub {Q : Measure Ω} {κ : Type*} {g : κ → Ω → ℝ} (hg : UnifIntegrable g 1 Q)
    (hgm : ∀ c, AEStronglyMeasurable (g c) Q) (a b : ℕ → κ) (A : Set Ω) :
    UnifIntegrable (fun n => A.indicator (fun ω => g (a n) ω - g (b n) ω)) 1 Q := by
  intro ε hε
  obtain ⟨δ, hδ, hδs⟩ := hg (half_pos hε)
  refine ⟨δ, hδ, fun n s hs hQs => ?_⟩
  calc eLpNorm (s.indicator (A.indicator fun ω => g (a n) ω - g (b n) ω)) 1 Q
      ≤ eLpNorm (s.indicator (g (a n)) - s.indicator (g (b n))) 1 Q := by
        refine eLpNorm_mono fun ω => ?_
        by_cases h1 : ω ∈ s <;> by_cases h2 : ω ∈ A <;> simp [h1, h2]
    _ ≤ eLpNorm (s.indicator (g (a n))) 1 Q + eLpNorm (s.indicator (g (b n))) 1 Q :=
        eLpNorm_sub_le ((hgm _).indicator hs) ((hgm _).indicator hs) le_rfl
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add (hδs _ s hs hQs) (hδs _ s hs hQs)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

lemma eLpNorm_ind_sub_le {Q : Measure Ω} {u v : Ω → ℝ} (hu : AEStronglyMeasurable u Q)
    (hv : AEStronglyMeasurable v Q) (A : Set Ω) :
    eLpNorm (A.indicator fun ω => u ω - v ω) 1 Q ≤ eLpNorm u 1 Q + eLpNorm v 1 Q :=
  (eLpNorm_mono (f := A.indicator fun ω => u ω - v ω) (g := u - v) fun ω => by
    by_cases h : ω ∈ A <;> simp [h]).trans (eLpNorm_sub_le hu hv le_rfl)

end Pure2

open HedgePSNV EthierKurtz ItoLib StochCalcBr StochCalcDG3m StochCalcG4

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma X_measF (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : StronglyMeasurable[M.F t] (M.X t) :=
  (hM.X_adapted t).mono (G_le_F' M hM t)

lemma X_meas (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.X t) :=
  ((X_measF M hM t).mono (M.F.le t)).measurable

/-- UI and a uniform L1 bound under `P^M` for all dyadic `X(tg N k) - x₀`. -/
theorem dyadic_family (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4)
    (h5 : M.Assumption5) :
    UnifIntegrable (fun c : ℕ × ℕ => fun ω => M.X (tg p.T c.1 (min c.2 (2 ^ c.1))) ω - p.x₀) 1
        M.PM ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ c : ℕ × ℕ,
        eLpNorm (fun ω => M.X (tg p.T c.1 (min c.2 (2 ^ c.1))) ω - p.x₀) 1 M.PM ≤ C := by
  haveI := PM_prob M hM h5
  set S : ℕ × ℕ × ℕ → Ω → ℝ := fun c => SS M c.1 (min c.2.1 (2 ^ c.1)) c.2.2 (BMx M) with hS
  have hcoef : ∀ (N k m l : ℕ), StronglyMeasurable[M.F (tg p.T (N + m) l)]
      (fun ω => if l < 2 ^ m * k then cf M (N + m) m l ω else 0) := by
    intro N k m l
    by_cases h : l < 2 ^ m * k
    · simp only [if_pos h]; exact cf_measF M hM (N + m) m l
    · simp only [if_neg h]; exact stronglyMeasurable_const
  have hcle : ∀ (N k m l : ℕ) (ω : Ω),
      |(fun ω => if l < 2 ^ m * k then cf M (N + m) m l ω else 0) ω| ≤
        |cf M (N + m) (m : ℝ) l ω| := by
    intro N k m l ω
    dsimp only
    split_ifs
    · exact le_rfl
    · simp
  have hSeq : ∀ c, S c = CS M (c.1 + c.2.2) (fun l ω =>
      if l < 2 ^ c.2.2 * min c.2.1 (2 ^ c.1) then cf M (c.1 + c.2.2) c.2.2 l ω else 0) :=
    fun c => rfl
  have hSm : ∀ c, Measurable (S c) := fun c => by
    rw [hSeq]
    exact CS_meas M hM _ _ fun l => ((hcoef _ _ _ l).mono (M.F.le _)).measurable
  have hT : ∀ c (j : ℕ), M.PM {ω | (2 : ℝ) ^ j ≤ |S c ω|} ≤
      2 * ∫⁻ ω, ENNReal.ofReal (min 1 (V M ω / 4 ^ j)) ∂M.PM := by
    intro c j
    rw [hSeq]
    exact CS_tail M hM h5 _ (Nat.cast_nonneg _) _ (hcoef _ _ _) (hcle _ _ _) j
  have hUI := unifIntegrable_of_dyadic_tail S hSm (V M) (V_meas M hM) (V_nonneg M)
    (sqrtV_int_PM M hM h4 h5) hT
  obtain ⟨C, hC, hCb⟩ := StochCalcG5p.eLpNorm_bdd hSm hUI (V_meas M hM) (V_nonneg M) hT
  have hseq : ∀ c : ℕ × ℕ, ∃ ns : ℕ → ℕ, ∀ᵐ ω ∂M.PM,
      Tendsto (fun n => S (c.1, c.2, ns n) ω) atTop
        (𝓝 (M.X (tg p.T c.1 (min c.2 (2 ^ c.1))) ω - p.x₀)) := by
    intro c
    obtain ⟨ns, -, hns⟩ :=
      (SS_BMx_tendsto_PM M hM h5 (min_le_right c.2 (2 ^ c.1))).exists_seq_tendsto_ae
    exact ⟨ns, hns⟩
  refine ⟨ui_of_ae_lim hUI (fun c => (hSm c).aestronglyMeasurable) fun c => ?_, C, hC,
    fun c => ?_⟩
  · obtain ⟨ns, hns⟩ := hseq c
    exact ⟨fun n => (c.1, c.2, ns n), hns⟩
  · obtain ⟨ns, hns⟩ := hseq c
    exact eLpNorm_ae_lim_le (fun n => (hSm _).aestronglyMeasurable) hns fun n => hCb _

/-- Dyadic index approximating `x` from above on the level-`n` `T`-grid. -/
noncomputable def kup (T : ℝ≥0) (n : ℕ) (x : ℝ≥0) : ℕ := ⌈(x : ℝ) / ((T : ℝ) / 2 ^ n)⌉₊

lemma kup_props (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (x : ℝ≥0) :
    x ≤ tg T n (kup T n x) ∧ (tg T n (kup T n x) : ℝ) < x + (T : ℝ) / 2 ^ n := by
  have hδ : (0 : ℝ) < (T : ℝ) / 2 ^ n := div_pos (NNReal.coe_pos.mpr hT) (by positivity)
  have h0 : 0 ≤ (x : ℝ) / ((T : ℝ) / 2 ^ n) := div_nonneg x.coe_nonneg hδ.le
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_le_coe, tg_coe]
    unfold kup
    calc (x : ℝ) = (x : ℝ) / ((T : ℝ) / 2 ^ n) * ((T : ℝ) / 2 ^ n) :=
          (div_mul_cancel₀ _ hδ.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hδ.le
  · rw [tg_coe]
    unfold kup
    calc (⌈(x : ℝ) / ((T : ℝ) / 2 ^ n)⌉₊ : ℝ) * ((T : ℝ) / 2 ^ n)
        < ((x : ℝ) / ((T : ℝ) / 2 ^ n) + 1) * ((T : ℝ) / 2 ^ n) :=
          mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one h0) hδ
      _ = x + (T : ℝ) / 2 ^ n := by rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul]

lemma kup_le (T : ℝ≥0) (hT : 0 < T) (n : ℕ) {x : ℝ≥0} (hx : x ≤ T) : kup T n x ≤ 2 ^ n := by
  have hδ : (0 : ℝ) < (T : ℝ) / 2 ^ n := div_pos (NNReal.coe_pos.mpr hT) (by positivity)
  unfold kup
  rw [Nat.ceil_le, div_le_iff₀ hδ]
  have h2 : ((2 ^ n : ℕ) : ℝ) * ((T : ℝ) / 2 ^ n) = T := by push_cast; field_simp
  rw [h2]
  exact NNReal.coe_le_coe.mpr hx

lemma kup_mono (T : ℝ≥0) (n : ℕ) {x y : ℝ≥0} (h : x ≤ y) : kup T n x ≤ kup T n y :=
  Nat.ceil_mono (div_le_div_of_nonneg_right (NNReal.coe_le_coe.mpr h) (by positivity))

lemma tg_kup_tendsto (T : ℝ≥0) (hT : 0 < T) (x : ℝ≥0) :
    Tendsto (fun n => tg T n (kup T n x)) atTop (𝓝 x) := by
  rw [← NNReal.tendsto_coe]
  have hδ : Tendsto (fun n : ℕ => (T : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hup : Tendsto (fun n : ℕ => (x : ℝ) + (T : ℝ) / 2 ^ n) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := (x : ℝ))).add hδ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => NNReal.coe_le_coe.mpr (kup_props T hT n x).1) (fun n => (kup_props T hT n x).2.le)

/-- Core of K1: `E^M[1_A (X t - X s)] = 0` for `s ≤ t ≤ T`, `A ∈ F s`. -/
theorem mart_core (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ p.T) {A : Set Ω} (hA : MeasurableSet[M.F s] A) :
    Integrable (A.indicator fun ω => M.X t ω - M.X s ω) M.PM ∧
      ∫ ω, A.indicator (fun ω => M.X t ω - M.X s ω) ω ∂M.PM = 0 := by
  haveI := PM_prob M hM h5
  rcases eq_or_lt_of_le hst with hst' | hst'
  · subst hst'
    simp
  have hT : 0 < p.T := lt_of_lt_of_le (lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s by positivity) hst') ht
  obtain ⟨hUI, C, hC, hCb⟩ := dyadic_family M hM h4 h5
  set g : ℕ × ℕ → Ω → ℝ := fun c ω => M.X (tg p.T c.1 (min c.2 (2 ^ c.1))) ω - p.x₀ with hg
  have hks : ∀ n, kup p.T n s ≤ 2 ^ n := fun n => kup_le p.T hT n (hst.trans ht)
  have hkt : ∀ n, kup p.T n t ≤ 2 ^ n := fun n => kup_le p.T hT n ht
  set f : ℕ → Ω → ℝ := fun n =>
    A.indicator (fun ω => g (n, kup p.T n t) ω - g (n, kup p.T n s) ω) with hf
  have hfX : ∀ n, f n = A.indicator (fun ω =>
      M.X (tg p.T n (kup p.T n t)) ω - M.X (tg p.T n (kup p.T n s)) ω) := by
    intro n
    simp only [hf, hg, min_eq_left (hks n), min_eq_left (hkt n), sub_sub_sub_cancel_right]
  have hAm : MeasurableSet A := M.F.le s A hA
  have hgm : ∀ c, AEStronglyMeasurable (g c) M.PM := fun c =>
    (X_meas M hM _).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hfm : ∀ n, Measurable (f n) := fun n => by
    rw [hfX n]
    exact ((X_meas M hM _).sub (X_meas M hM _)).indicator hAm
  have hUIf : UnifIntegrable f 1 M.PM :=
    ui_ind_sub hUI hgm (fun n => (n, kup p.T n t)) (fun n => (n, kup p.T n s)) A
  have hCb2 : ∀ n, eLpNorm (f n) 1 M.PM ≤ C + C := fun n =>
    (eLpNorm_ind_sub_le (hgm _) (hgm _) A).trans (add_le_add (hCb _) (hCb _))
  have hconv : TendstoInMeasure M.PM f atTop (A.indicator fun ω => M.X t ω - M.X s ω) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (hfm n).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    simp only [hfX]
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      exact (((hM.X_cont ω).tendsto t).comp (tg_kup_tendsto p.T hT t)).sub
        (((hM.X_cont ω).tendsto s).comp (tg_kup_tendsto p.T hT s))
    · simp only [Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have h0 : ∀ n, ∫ ω, f n ω ∂M.PM = 0 := by
    intro n
    rw [hfX n]
    have hA' : MeasurableSet[M.F (tg p.T n (kup p.T n s))] A :=
      M.F.mono (kup_props p.T hT n s).1 A hA
    exact (dyadic_incr M hM h4 h5 (kup_mono p.T n hst) (hkt n) hA').2
  exact StochCalcG5p.integral_lim_zero hfm hUIf (ENNReal.add_lt_top.mpr ⟨hC, hC⟩) hCb2 hconv h0

/-- **K1**: the asset price is a `P^M`-martingale on `[0,T]`. -/
theorem asset_price_PM_martingale (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4)
    (h5 : M.Assumption5) : IsMartingaleOn p.T M.F M.PM M.X := by
  haveI := PM_prob M hM h5
  have hint : ∀ t, t ≤ p.T → Integrable (M.X t) M.PM := by
    intro t ht
    have h := (mart_core M hM h4 h5 (show (0 : ℝ≥0) ≤ t by positivity) ht (A := Set.univ) MeasurableSet.univ).1
    simp only [Set.indicator_univ] at h
    refine (h.add (integrable_const p.x₀)).congr (Eventually.of_forall fun ω => ?_)
    simp [hM.X_zero ω]
  refine ⟨fun t _ => X_measF M hM t, hint, fun s t hst ht => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (M.F.le s) (hint t ht)
    (fun A _ _ => (hint s (hst.trans ht)).integrableOn) (fun A hA _ => ?_)
    (X_measF M hM s).aestronglyMeasurable).symm
  have hc := (mart_core M hM h4 h5 hst ht hA).2
  have hAm : MeasurableSet A := M.F.le s A hA
  rw [integral_indicator hAm, integral_sub (hint t ht).integrableOn
    (hint s (hst.trans ht)).integrableOn] at hc
  linarith

end StochCalcG5


open MeasureTheory ProbabilityTheory HedgePSNV in
open scoped NNReal ENNReal in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω]
    (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5) :
    IsMartingaleOn p.T M.F M.PM M.X := by
  exact StochCalcG5.asset_price_PM_martingale M hM h4 h5
