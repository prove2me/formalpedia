-- Prove2me | solution 1 for GhadimiLan.TwoPhase.theorem_2_4_b
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T22:36:47.923302+00:00
-- url     : https://prove2.me/submissions/573be48b-8493-493c-a810-f05c8580add5

-- Licensed under Apache 2.0. Complete two-phase randomized stochastic gradient theorem.
import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory


open MeasureTheory GhadimiLan.TwoPhase GhadimiLan.RSG
open scoped InnerProductSpace

namespace TwoPhaseRSGProof

variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

lemma gradient_lipschitz (P : Problem n Ξ) :
    LipschitzWith ⟨P.L, P.L_pos.le⟩ P.g := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖P.g x - P.g y‖ ≤ P.L * ‖x - y‖
  exact P.smooth.2.2 x y

lemma gradient_continuous (P : Problem n Ξ) : Continuous P.g :=
  (gradient_lipschitz P).continuous

lemma segment_derivative (P : Problem n Ξ) (x v : E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P.f (x + s • v)) (inner ℝ (P.g (x + t • v)) v) t := by
  convert (P.smooth.2.1 (x + t • v)).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add x) using 1 <;>
    first | rfl | simp only [one_smul, InnerProductSpace.toDual_apply_apply]

lemma smooth_descent (P : Problem n Ξ) (x v : E n) :
    P.f (x + v) ≤ P.f x + inner ℝ (P.g x) v + (P.L / 2) * ‖v‖ ^ 2 := by
  let F : ℝ → ℝ := fun t => P.f (x + t • v)
  let B : ℝ → ℝ := fun t => P.f x + t * inner ℝ (P.g x) v +
    (P.L / 2) * t ^ 2 * ‖v‖ ^ 2
  have hF : ∀ t, HasDerivAt F (inner ℝ (P.g (x + t • v)) v) t :=
    segment_derivative P x v
  have hB : ∀ t, HasDerivAt B (inner ℝ (P.g x) v + P.L * t * ‖v‖ ^ 2) t := by
    intro t
    convert (((hasDerivAt_id t).mul_const (inner ℝ (P.g x) v)).const_add (P.f x)).add
      ((((hasDerivAt_id t).pow 2).const_mul (P.L / 2)).mul_const (‖v‖ ^ 2)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      inner ℝ (P.g (x + t • v)) v ≤ inner ℝ (P.g x) v + P.L * t * ‖v‖ ^ 2 := by
    intro t ht
    have h1 := real_inner_le_norm (P.g (x + t • v) - P.g x) v
    have h2 := P.smooth.2.2 (x + t • v) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    rw [inner_sub_left] at h1
    nlinarith
  have hh := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hbound
  simpa [F, B] using hh (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)

lemma infimum_le (P : Problem n Ξ) (x : E n) : P.fstar ≤ P.f x :=
  P.infimum.1 (Set.mem_range_self x)

lemma df_sq (P : Problem n Ξ) : (Df P) ^ 2 = 2 * (P.f P.x₁ - P.fstar) / P.L := by
  apply Real.sq_sqrt
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (infimum_le P P.x₁)))
    P.L_pos.le

lemma gradient_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (P : Problem n Ξ) {x : Ω → E n} (hx : MemLp x 2 μ) :
    MemLp (fun ω => P.g (x ω)) 2 μ := by
  have hg : LipschitzWith ⟨P.L, P.L_pos.le⟩ (fun z => P.g z - P.g 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    change ‖(P.g a - P.g 0) - (P.g b - P.g 0)‖ ≤ P.L * ‖a - b‖
    simpa only [sub_sub_sub_cancel_right] using P.smooth.2.2 a b
  have hh := hg.comp_memLp (by simp) hx
  have ht := hh.add (memLp_const (P.g 0))
  change MemLp (fun ω => (P.g (x ω) - P.g 0) + P.g 0) 2 μ at ht
  simpa only [sub_add_cancel] using ht

end TwoPhaseRSGProof


open GhadimiLan.TwoPhase GhadimiLan.RSG

namespace TwoPhaseRSGProof

variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

lemma step_pos (P : Problem n Ξ) {N : ℕ} (hN : 1 ≤ N) :
    0 < rsgStep P.L P.Dt P.σ N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact lt_min (one_div_pos.mpr P.L_pos)
    (div_pos P.Dt_pos (mul_pos P.σ_pos (Real.sqrt_pos.2 hn)))

lemma step_le_inverse (P : Problem n Ξ) (N : ℕ) :
    rsgStep P.L P.Dt P.σ N ≤ 1 / P.L := min_le_left _ _

lemma step_mul_le_one (P : Problem n Ξ) (N : ℕ) :
    P.L * rsgStep P.L P.Dt P.σ N ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (step_le_inverse P N) P.L_pos.le
  simpa [P.L_pos.ne'] using h

lemma step_weight_pos (P : Problem n Ξ) {N : ℕ} (hN : 1 ≤ N) :
    0 < 2 * rsgStep P.L P.Dt P.σ N - P.L * rsgStep P.L P.Dt P.σ N ^ 2 := by
  have hp := step_pos P hN
  have hm := step_mul_le_one P N
  nlinarith

lemma uniform_pmf (P : Problem n Ξ) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    rsgPMF P.L (fun _ => rsgStep P.L P.Dt P.σ N) N k = 1 / (N : ℝ) := by
  have hw := (step_weight_pos P hN).ne'
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [rsgPMF, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul]
  apply (div_eq_div_iff (mul_ne_zero hn hw) hn).mpr
  ring

lemma step_final_bound (P : Problem n Ξ) {N : ℕ} (hN : 1 ≤ N) :
    P.L * ((Df P)^2 / ((N : ℝ) * rsgStep P.L P.Dt P.σ N) +
      rsgStep P.L P.Dt P.σ N * P.σ ^ 2) ≤ P.L * BN P.L (Df P) P.Dt P.σ N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Real.sqrt_pos.2 hn
  have hs2 := Real.sq_sqrt hn.le
  have hg := step_pos P hN
  have hu : rsgStep P.L P.Dt P.σ N ≤ P.Dt / (P.σ * Real.sqrt N) := min_le_right _ _
  have hi : 1 / rsgStep P.L P.Dt P.σ N ≤ P.L + P.σ * Real.sqrt N / P.Dt := by
    rcases le_total (1 / P.L) (P.Dt / (P.σ * Real.sqrt N)) with h | h
    · rw [rsgStep, min_eq_left h, one_div_one_div]
      exact le_add_of_nonneg_right (div_nonneg (mul_nonneg P.σ_pos.le hs.le) P.Dt_pos.le)
    · rw [rsgStep, min_eq_right h, one_div_div]
      have : 0 < P.L := P.L_pos
      linarith
  have h1 := mul_le_mul_of_nonneg_left hi (div_nonneg (sq_nonneg (Df P)) hn.le)
  have h2 := mul_le_mul_of_nonneg_right hu (sq_nonneg P.σ)
  apply mul_le_mul_of_nonneg_left _ P.L_pos.le
  calc
    _ = ((Df P)^2 / (N : ℝ)) * (1 / rsgStep P.L P.Dt P.σ N) +
        rsgStep P.L P.Dt P.σ N * P.σ^2 := by ring
    _ ≤ ((Df P)^2 / (N : ℝ)) * (P.L + P.σ * Real.sqrt N / P.Dt) +
        (P.Dt / (P.σ * Real.sqrt N)) * P.σ^2 := add_le_add h1 h2
    _ = BN P.L (Df P) P.Dt P.σ N := by
      unfold BN
      field_simp [ne_of_gt P.Dt_pos, ne_of_gt P.σ_pos, ne_of_gt hn, ne_of_gt hs]
      nlinarith [mul_nonneg (sq_nonneg (Df P)) P.σ_pos.le]

end TwoPhaseRSGProof


open MeasureTheory ProbabilityTheory GhadimiLan.TwoPhase GhadimiLan.RSG

namespace TwoPhaseRSGProof

variable {n N : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem n Ξ}

omit [IsProbabilityMeasure μ] in
lemma run_adapted (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    Measurable[A.ℱ (k - 1)] (A.x k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have he : A.x 1 = fun _ => P.x₁ := funext A.recursion.1
    rw [he]
    exact measurable_const
  | succ k hk ih =>
    have hm : Measurable[A.ℱ k] (A.x k) :=
      ih.mono (A.ℱ.mono (Nat.sub_le k 1)) le_rfl
    have ho := P.oracle_measurable.comp (hm.prodMk (A.a1.2 k hk).1)
    have he : A.x (k + 1) = fun ω => A.x k ω -
        rsgStep P.L P.Dt P.σ N • P.G (A.x k ω) (A.ξ k ω) :=
      funext (A.recursion.2 k hk)
    rw [he]
    convert hm.sub (ho.const_smul (rsgStep P.L P.Dt P.σ N)) using 1 <;> rfl

omit [IsProbabilityMeasure μ] in
lemma run_measurable (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) : Measurable (A.x k) :=
  (run_adapted A hk).mono (A.ℱ.le _) le_rfl

omit [IsProbabilityMeasure μ] in
lemma run_error_measurable (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    Measurable (fun ω => P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω)) := by
  have hξ := ((A.a1.2 k hk).1).mono (A.ℱ.le k) le_rfl
  exact (P.oracle_measurable.comp ((run_measurable A hk).prodMk hξ)).sub
    ((gradient_continuous P).measurable.comp (run_measurable A hk))

omit [IsProbabilityMeasure μ] in
lemma run_error_memLp (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    MemLp (fun ω => P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω)) 2 μ :=
  (memLp_two_iff_integrable_sq_norm
    (run_error_measurable A hk).aestronglyMeasurable).mpr (A.a1.2 k hk).2.2.2.1

lemma run_memLp (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) : MemLp (A.x k) 2 μ := by
  induction k, hk using Nat.le_induction with
  | base =>
    have he : A.x 1 = fun _ => P.x₁ := funext A.recursion.1
    rw [he]
    exact memLp_const _
  | succ k hk ih =>
    have hg := gradient_memLp P ih
    have ho : MemLp (fun ω => P.G (A.x k ω) (A.ξ k ω)) 2 μ := by
      have hh := (run_error_memLp A hk).add hg
      change MemLp (fun ω => (P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω)) + P.g (A.x k ω)) 2 μ at hh
      simpa only [sub_add_cancel] using hh
    have he : A.x (k + 1) = fun ω => A.x k ω -
        rsgStep P.L P.Dt P.σ N • P.G (A.x k ω) (A.ξ k ω) :=
      funext (A.recursion.2 k hk)
    rw [he]
    convert ih.sub (ho.const_smul (rsgStep P.L P.Dt P.σ N)) using 1 <;> rfl

lemma run_gradient_memLp (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    MemLp (fun ω => P.g (A.x k ω)) 2 μ := gradient_memLp P (run_memLp A hk)

lemma run_gradient_sq_integrable (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun ω => ‖P.g (A.x k ω)‖ ^ 2) μ :=
  (run_gradient_memLp A hk).norm.integrable_sq

noncomputable def trajectory (P : Problem n Ξ) (N : ℕ) (ζ : ℕ → Ξ) : ℕ → E n
  | 0 => P.x₁
  | j + 1 => trajectory P N ζ j - rsgStep P.L P.Dt P.σ N •
      P.G (trajectory P N ζ j) (ζ (j + 1))

lemma trajectory_measurable (P : Problem n Ξ) (N j : ℕ) :
    Measurable (fun ζ : ℕ → Ξ => trajectory P N ζ j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    convert ih.sub ((P.oracle_measurable.comp (ih.prodMk (measurable_pi_apply (j + 1)))).const_smul (rsgStep P.L P.Dt P.σ N)) using 1
    rfl

omit [IsProbabilityMeasure μ] in
lemma trajectory_eq_run (A : Run P N μ) (ω : Ω) (j : ℕ) :
    trajectory P N (fun k => A.ξ k ω) j = A.x (j + 1) ω := by
  induction j with
  | zero => exact (A.recursion.1 ω).symm
  | succ j ih =>
    rw [trajectory, ih, A.recursion.2 (j + 1) (by omega)]

omit [IsProbabilityMeasure μ] in
lemma index_indep_gradient (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    IndepFun A.R (fun ω => P.g (A.x k ω)) μ := by
  have hh := A.index_indep.comp measurable_id
    ((gradient_continuous P).measurable.comp (trajectory_measurable P N (k - 1)))
  have he : (P.g ∘ fun ζ => trajectory P N ζ (k - 1)) ∘ (fun ω k => A.ξ k ω) =
      fun ω => P.g (A.x k ω) := by
    funext ω
    simp only [Function.comp_def, trajectory_eq_run, Nat.sub_add_cancel hk]
  rw [he] at hh
  exact hh

end TwoPhaseRSGProof


open MeasureTheory Filter
open scoped MeasureTheory

namespace TwoPhaseRSGProof

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem integrable_inner_of_memLp {z e : Ω → E}
    (hz : MemLp z 2 μ) (he : MemLp e 2 μ) :
    Integrable (fun ω => inner ℝ (z ω) (e ω)) μ := by
  have hh := hz.norm.integrable_mul he.norm
  exact hh.mono' (hz.aestronglyMeasurable.inner he.aestronglyMeasurable)
    (Eventually.of_forall fun ω => norm_inner_le_norm (z ω) (e ω))

theorem integral_inner_eq_zero {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {z e : Ω → E}
    (hz : MemLp z 2 μ) (he : MemLp e 2 μ)
    (hzm : AEStronglyMeasurable[m] z μ)
    (hzero : μ[e | m] =ᵐ[μ] 0) :
    (∫ ω, inner ℝ (z ω) (e ω) ∂μ) = 0 := by
  let : MeasurableSpace Ω := mΩ
  have hp := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) hzm
    (integrable_inner_of_memLp hz he) (he.integrable (by norm_num))
  have hfun : (fun ω => (innerSL ℝ) (z ω) (e ω)) =
      (fun ω => inner ℝ (z ω) (e ω)) := rfl
  rw [hfun] at hp
  rw [← integral_condExp hm]
  have heq : μ[fun ω => inner ℝ (z ω) (e ω) | m] =ᵐ[μ] 0 := by
    filter_upwards [hp, hzero] with ω hω h0
    simpa [h0] using hω
  rw [integral_congr_ae heq]
  simp

theorem condExp_sub_centered {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {g z : Ω → E}
    (hg : Integrable g μ) (hz : Integrable z μ)
    (hzm : StronglyMeasurable[m] z)
    (hc : μ[g | m] =ᵐ[μ] z) : μ[(fun ω => g ω - z ω) | m] =ᵐ[μ] 0 := by
  let : MeasurableSpace Ω := mΩ
  have hs := condExp_sub hg hz m
  have hfun : g - z = (fun ω => g ω - z ω) := rfl
  rw [hfun, condExp_of_stronglyMeasurable hm hzm hz] at hs
  filter_upwards [hs, hc] with ω hsω hcω
  simpa [hcω] using hsω

end TwoPhaseRSGProof


open MeasureTheory Filter
open scoped MeasureTheory

namespace TwoPhaseRSGProof

variable {Ω E ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem integral_norm_add_sq {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, ‖f ω + g ω‖ ^ 2 ∂μ) = (∫ ω, ‖f ω‖ ^ 2 ∂μ) +
      2 * (∫ ω, inner ℝ (f ω) (g ω) ∂μ) + (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
  have hi : Integrable (fun ω => 2 * inner ℝ (f ω) (g ω)) μ :=
    (integrable_inner_of_memLp hf hg).const_mul 2
  have ha : Integrable (fun ω => ‖f ω‖ ^ 2 + 2 * inner ℝ (f ω) (g ω)) μ := by
    convert hf.norm.integrable_sq.add hi using 1 <;> rfl
  simp_rw [norm_add_sq_real]
  rw [integral_add ha hg.norm.integrable_sq,
    integral_add hf.norm.integrable_sq hi, integral_const_mul]

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem integral_norm_sum_sq (s : Finset ι) (e : ι → Ω → E)
    (he : ∀ i ∈ s, MemLp (e i) 2 μ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ ω, inner ℝ (e i ω) (e j ω) ∂μ) = 0) :
    (∫ ω, ‖∑ i ∈ s, e i ω‖ ^ 2 ∂μ) = ∑ i ∈ s, ∫ ω, ‖e i ω‖ ^ 2 ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hei := he i (Finset.mem_insert_self i s)
    have hes : ∀ j ∈ s, MemLp (e j) 2 μ := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have hsum := memLp_finsetSum s hes
    have hz : (∫ ω, inner ℝ (e i ω) (∑ j ∈ s, e j ω) ∂μ) = 0 := by
      simp_rw [inner_sum]
      rw [integral_finsetSum s (fun j hj => integrable_inner_of_memLp hei (hes j hj))]
      apply Finset.sum_eq_zero
      intro j hj
      exact ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun hij => hi (hij.symm ▸ hj))
    simp only [Finset.sum_insert hi]
    rw [integral_norm_add_sq hei hsum, hz, ih hes]
    · ring
    · intro j hj k hk hjk
      exact ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk

end TwoPhaseRSGProof


open MeasureTheory Filter
open scoped MeasureTheory

namespace TwoPhaseRSGProof

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem martingale_sum_bound (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (e : ℕ → Ω → E) (σ : ℝ) (T : ℕ)
    (hmeas : ∀ k, 1 ≤ k → StronglyMeasurable[F k] (e k))
    (hlp : ∀ k, 1 ≤ k → MemLp (e k) 2 μ)
    (hcenter : ∀ k, 1 ≤ k → μ[e k | F (k-1)] =ᵐ[μ] 0)
    (hbound : ∀ k, 1 ≤ k → (∫ ω, ‖e k ω‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    (∫ ω, ‖∑ k ∈ Finset.Icc 1 T, e k ω‖ ^ 2 ∂μ) ≤ (T : ℝ) * σ ^ 2 := by
  have hcross : ∀ i ∈ Finset.Icc 1 T, ∀ j ∈ Finset.Icc 1 T, i < j →
      (∫ ω, inner ℝ (e i ω) (e j ω) ∂μ) = 0 := by
    intro i hi j hj hij
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hj1 := (Finset.mem_Icc.mp hj).1
    apply integral_inner_eq_zero (F.le (j-1)) (hlp i hi1) (hlp j hj1)
      ((hmeas i hi1).mono (F.mono (by omega))).aestronglyMeasurable (hcenter j hj1)
  rw [integral_norm_sum_sq (Finset.Icc 1 T) e
    (fun i hi => hlp i (Finset.mem_Icc.mp hi).1)]
  · calc
      _ ≤ ∑ _k ∈ Finset.Icc 1 T, σ ^ 2 :=
        Finset.sum_le_sum fun k hk => hbound k (Finset.mem_Icc.mp hk).1
      _ = (T : ℝ) * σ ^ 2 := by simp
  · intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hcross i hi j hj h
    · simpa only [real_inner_comm] using hcross j hj i hi h

end TwoPhaseRSGProof


open MeasureTheory Filter GhadimiLan.TwoPhase GhadimiLan.RSG
open scoped MeasureTheory

namespace TwoPhaseRSGProof

variable {n S N T : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem n Ξ}
  (A : System (S := S) (N := N) (T := T) P μ)

noncomputable def postError (s : Fin S) (k : ℕ) (ω : Ω) : E n :=
  P.G (output (A.runs s) ω) (A.η s k ω) - P.g (output (A.runs s) ω)

omit [IsProbabilityMeasure μ] in
theorem postError_measurable (hg : Continuous P.g) (s : Fin S) (k : ℕ) (hk : 1 ≤ k) :
    Measurable[A.𝒢 s k] (postError A s k) := by
  have hx := (A.post_a1.1 s).mono ((A.𝒢 s).mono (Nat.zero_le k)) le_rfl
  exact (P.oracle_measurable.comp (hx.prodMk (A.post_a1.2 s k hk).1)).sub
    (hg.measurable.comp hx)

omit [IsProbabilityMeasure μ] in
theorem postError_memLp (hg : Continuous P.g) (s : Fin S) (k : ℕ) (hk : 1 ≤ k) :
    MemLp (postError A s k) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    ((postError_measurable A hg s k hk).mono ((A.𝒢 s).le k) le_rfl).aestronglyMeasurable).mpr
  exact (A.post_a1.2 s k hk).2.2.2.1

theorem postError_centered (hg : Continuous P.g) (s : Fin S) (k : ℕ) (hk : 1 ≤ k) :
    μ[postError A s k | A.𝒢 s (k-1)] =ᵐ[μ] 0 := by
  have ha := A.post_a1.2 s k hk
  have hgint : Integrable (fun ω => P.g (output (A.runs s) ω)) μ :=
    integrable_condExp.congr ha.2.2.1
  apply condExp_sub_centered ((A.𝒢 s).le (k-1)) ha.2.1 hgint
    ((hg.measurable.comp ((A.post_a1.1 s).mono
      ((A.𝒢 s).mono (Nat.zero_le (k-1))) le_rfl)).stronglyMeasurable) ha.2.2.1

theorem post_sum_bound (hg : Continuous P.g) (s : Fin S) :
    (∫ ω, ‖∑ k ∈ Finset.Icc 1 T, postError A s k ω‖ ^ 2 ∂μ) ≤ (T : ℝ) * P.σ ^ 2 := by
  apply martingale_sum_bound (A.𝒢 s) (postError A s) P.σ T
  · exact fun k hk => (postError_measurable A hg s k hk).stronglyMeasurable
  · exact fun k hk => postError_memLp A hg s k hk
  · exact fun k hk => postError_centered A hg s k hk
  · exact fun k hk => (A.post_a1.2 s k hk).2.2.2.2

omit [IsProbabilityMeasure μ] in
theorem estimate_error_eq_sum (s : Fin S) (hT : 1 ≤ T) (ω : Ω) :
    estimate A.runs A.η T s ω - P.g (output (A.runs s) ω) =
      (1 / (T : ℝ)) • ∑ k ∈ Finset.Icc 1 T, postError A s k ω := by
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  simp only [postError, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, estimate, smul_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [ht]

theorem post_estimation_bound (hg : Continuous P.g) (s : Fin S) (hT : 1 ≤ T) :
    Integrable (fun ω => ‖estimate A.runs A.η T s ω - P.g (output (A.runs s) ω)‖ ^ 2) μ ∧
    (∫ ω, ‖estimate A.runs A.η T s ω - P.g (output (A.runs s) ω)‖ ^ 2 ∂μ) ≤
      P.σ ^ 2 / (T : ℝ) := by
  have hlp := memLp_finsetSum (Finset.Icc 1 T)
    (fun k hk => postError_memLp A hg s k (Finset.mem_Icc.mp hk).1)
  have ht : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  simp_rw [estimate_error_eq_sum A s hT]
  constructor
  · exact (hlp.const_smul (1 / (T : ℝ))).norm.integrable_sq
  · simp_rw [norm_smul, Real.norm_eq_abs, mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ |1 / (T : ℝ)| ^ 2 * ((T : ℝ) * P.σ ^ 2) :=
        mul_le_mul_of_nonneg_left (post_sum_bound A hg s) (sq_nonneg _)
      _ = P.σ ^ 2 / (T : ℝ) := by rw [sq_abs]; field_simp

end TwoPhaseRSGProof


open GhadimiLan.TwoPhase

namespace TwoPhaseRSGProof

theorem candidate_count_budget {Λ : ℝ} (hΛ : 0 < Λ) (hΛ1 : Λ < 1)
    {S : ℕ} (hS : S = Nat.ceil (Real.logb 2 (2 / Λ))) :
    1 ≤ S ∧ (1 / 2 : ℝ) ^ S ≤ Λ / 2 := by
  have hr : (1 : ℝ) < 2 / Λ := (lt_div_iff₀ hΛ).mpr (by linarith)
  constructor
  · rw [hS]
    exact Nat.one_le_ceil_iff.mpr (Real.logb_pos (by norm_num) hr)
  · have hh : Real.logb 2 (2 / Λ) ≤ (S : ℝ) := by rw [hS]; exact Nat.le_ceil _
    have hp : 2 / Λ ≤ (2 : ℝ) ^ S := by
      simpa only [Real.rpow_natCast] using
        (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 2 / Λ)).mp hh
    have hi := one_div_le_one_div_of_le (by positivity : 0 < 2 / Λ) hp
    simpa [one_div_pow] using hi

theorem post_count_budget {Λ ε σ : ℝ} (hΛ : 0 < Λ) (hε : 0 < ε) (hσ : 0 < σ)
    (S : ℕ) {T : ℕ} (hT : T = Nat.ceil (24 * ((S : ℝ) + 1) * σ ^ 2 / (Λ * ε))) :
    1 ≤ T ∧ 12 * (S : ℝ) * σ ^ 2 / ((T : ℝ) * ε) ≤ Λ / 2 := by
  have ha : 0 < 24 * ((S : ℝ) + 1) * σ ^ 2 / (Λ * ε) := by positivity
  have ht : 1 ≤ T := by rw [hT]; exact Nat.one_le_ceil_iff.mpr ha
  have htpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  refine ⟨ht, ?_⟩
  have hh : 24 * ((S : ℝ) + 1) * σ ^ 2 / (Λ * ε) ≤ T := by
    rw [hT]; exact Nat.le_ceil _
  have hh' := (div_le_iff₀ (mul_pos hΛ hε)).mp hh
  apply (div_le_iff₀ (mul_pos htpos hε)).mpr
  nlinarith [sq_nonneg σ]

theorem trajectory_count_budget {L D Dt σ ε : ℝ}
    (hL : 0 < L) (hDt : 0 < Dt) (hσ : 0 < σ) (hε : 0 < ε)
    {N : ℕ} (hN : N = Nat.ceil (max (32 * L ^ 2 * D ^ 2 / ε)
      ((32 * L * (Dt + D ^ 2 / Dt) * σ / ε) ^ 2))) :
    1 ≤ N ∧ L * BN L D Dt σ N ≤ ε / 16 := by
  let b : ℝ := 32 * L * (Dt + D ^ 2 / Dt) * σ / ε
  have hb : 0 < b := by dsimp [b]; positivity
  have hm : 0 < max (32 * L ^ 2 * D ^ 2 / ε) (b ^ 2) :=
    lt_of_lt_of_le (sq_pos_of_pos hb) (le_max_right _ _)
  have hn : 1 ≤ N := by rw [hN]; exact Nat.one_le_ceil_iff.mpr hm
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmax : max (32 * L ^ 2 * D ^ 2 / ε) (b ^ 2) ≤ (N : ℝ) := by
    rw [hN]; exact Nat.le_ceil _
  have ha := (le_max_left _ _).trans hmax
  have hbb := (le_max_right _ _).trans hmax
  have hs : b ≤ Real.sqrt (N : ℝ) := (Real.le_sqrt (le_of_lt hb) (le_of_lt hnpos)).mpr hbb
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hnpos
  have hfirst : L ^ 2 * D ^ 2 / (N : ℝ) ≤ ε / 32 := by
    apply (div_le_iff₀ hnpos).mpr
    have := (div_le_iff₀ hε).mp ha
    nlinarith
  have hsecond : L * (Dt + D ^ 2 / Dt) * σ / Real.sqrt (N : ℝ) ≤ ε / 32 := by
    apply (div_le_iff₀ hspos).mpr
    have := (div_le_iff₀ hε).mp hs
    nlinarith
  refine ⟨hn, ?_⟩
  unfold BN
  calc
    _ = L ^ 2 * D ^ 2 / (N : ℝ) + L * (Dt + D ^ 2 / Dt) * σ / Real.sqrt (N : ℝ) := by ring
    _ ≤ ε / 16 := by linarith

end TwoPhaseRSGProof


open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace TwoPhaseRSGProof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measure_gt_le_integral_div {f : Ω → ℝ} (hf : Integrable f μ)
    (hn : ∀ ω, 0 ≤ f ω) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a < f ω} ≤ (∫ ω, f ω ∂μ) / a := by
  apply (le_div_iff₀ ha).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hf a
  have hm : μ.real {ω | a < f ω} ≤ μ.real {ω | a ≤ f ω} :=
    measureReal_mono (by intro ω h; exact show a ≤ f ω from le_of_lt h)
  nlinarith

omit [IsProbabilityMeasure μ] in
theorem independent_all_bad_bound {S : ℕ} (X : Fin S → Ω → ℝ)
    (hind : iIndepFun X μ) (a : ℝ)
    (hb : ∀ s, μ.real {ω | a < X s ω} ≤ 1 / 2) :
    μ.real {ω | ∀ s, a < X s ω} ≤ (1 / 2 : ℝ) ^ S := by
  have hi := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun _ => Set.Ioi a) (fun _ _ => measurableSet_Ioi)
  have heq : μ {ω | ∀ s, a < X s ω} = ∏ s, μ {ω | a < X s ω} := by
    have hset : (⋂ i ∈ (Finset.univ : Finset (Fin S)), X i ⁻¹' Set.Ioi a) =
        {ω | ∀ s, a < X s ω} := by ext ω; simp
    have hsets : ∀ s, X s ⁻¹' Set.Ioi a = {ω | a < X s ω} := fun _ => rfl
    rw [hset] at hi
    simp_rw [hsets] at hi
    exact hi
  unfold Measure.real
  rw [heq, ENNReal.toReal_prod]
  calc
    _ ≤ ∏ _s : Fin S, (1 / 2 : ℝ) := Finset.prod_le_prod
      (fun s _ => ENNReal.toReal_nonneg) (fun s _ => hb s)
    _ = (1 / 2 : ℝ) ^ S := by simp

theorem good_event_lower_bound {S : ℕ} (X Y : Fin S → Ω → ℝ)
    (hX : ∀ s, Measurable (X s)) (hY : ∀ s, Measurable (Y s))
    (hind : iIndepFun X μ) {ε Λ c : ℝ} (hε : 0 < ε)
    (hXi : ∀ s, Integrable (X s) μ) (hYi : ∀ s, Integrable (Y s) μ)
    (hXn : ∀ s ω, 0 ≤ X s ω) (hYn : ∀ s ω, 0 ≤ Y s ω)
    (hXb : ∀ s, (∫ ω, X s ω ∂μ) ≤ ε / 16)
    (hYb : ∀ s, (∫ ω, Y s ω ∂μ) ≤ c)
    (hS : (1 / 2 : ℝ) ^ S ≤ Λ / 2)
    (hT : (S : ℝ) * (c / (ε / 12)) ≤ Λ / 2) :
    ENNReal.ofReal (1 - Λ) ≤ μ {ω | (∃ s, X s ω ≤ ε / 8) ∧ ∀ s, Y s ω ≤ ε / 12} := by
  let B : Set Ω := ⋂ s, {ω | ε / 8 < X s ω}
  let D : Set Ω := ⋃ s, {ω | ε / 12 < Y s ω}
  have hBm : MeasurableSet B := by
    exact MeasurableSet.iInter fun s => measurableSet_lt measurable_const (hX s)
  have hDm : MeasurableSet D := by
    exact MeasurableSet.iUnion fun s => measurableSet_lt measurable_const (hY s)
  have hBb : μ.real B ≤ Λ / 2 := by
    have hBeq : B = {ω | ∀ s, ε / 8 < X s ω} := by ext ω; simp [B]
    rw [hBeq]
    apply le_trans (independent_all_bad_bound X hind (ε / 8) ?_) hS
    intro s
    have hh := measure_gt_le_integral_div (hXi s) (hXn s) (by positivity : 0 < ε / 8)
    have hd : (∫ ω, X s ω ∂μ) / (ε / 8) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < ε / 8)).mpr
      linarith [hXb s]
    exact hh.trans hd
  have hDb : μ.real D ≤ Λ / 2 := by
    calc
      _ ≤ ∑ s : Fin S, μ.real {ω | ε / 12 < Y s ω} :=
        measureReal_iUnion_fintype_le (fun s => {ω | ε / 12 < Y s ω})
      _ ≤ ∑ _s : Fin S, c / (ε / 12) := by
        apply Finset.sum_le_sum
        intro s _
        exact (measure_gt_le_integral_div (hYi s) (hYn s)
          (by positivity : 0 < ε / 12)).trans
          (div_le_div_of_nonneg_right (hYb s) (by positivity))
      _ = (S : ℝ) * (c / (ε / 12)) := by simp
      _ ≤ Λ / 2 := hT
  have hu : μ.real (B ∪ D) ≤ Λ := (measureReal_union_le B D).trans (by linarith)
  have hc := measureReal_add_measureReal_compl (μ := μ) (hBm.union hDm)
  have hlow : 1 - Λ ≤ μ.real (B ∪ D)ᶜ := by
    simp only [measure_univ, ENNReal.toReal_one, measureReal_def] at hc
    simp only [measureReal_def] at hu ⊢
    linarith
  have heq : (B ∪ D)ᶜ = {ω | (∃ s, X s ω ≤ ε / 8) ∧ ∀ s, Y s ω ≤ ε / 12} := by
    ext ω
    simp [B, D, not_lt]
  rw [← heq, ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hlow

end TwoPhaseRSGProof


open MeasureTheory ProbabilityTheory GhadimiLan.TwoPhase GhadimiLan.RSG
open scoped MeasureTheory

namespace TwoPhaseRSGProof

theorem norm_sq_compare {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * ‖y - x‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖y‖ + ‖y-x‖ := by
    calc
      ‖x‖ = ‖y - (y-x)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖y-x‖ := norm_sub_le _ _
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (y-x),
    sq_nonneg (‖y‖ - ‖y-x‖)]

variable {n S N T : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem n Ξ}
  (A : System (S := S) (N := N) (T := T) P μ)

omit [IsProbabilityMeasure μ] in
theorem estimate_measurable (s : Fin S) : Measurable (estimate A.runs A.η T s) := by
  have hx := (A.post_a1.1 s).mono ((A.𝒢 s).le 0) le_rfl
  have hm : Measurable (fun ω => ∑ k ∈ Finset.Icc 1 T,
      P.G (output (A.runs s) ω) (A.η s k ω)) := by
    apply Finset.measurable_sum
    intro k hk
    exact P.oracle_measurable.comp (hx.prodMk
      ((A.post_a1.2 s k (Finset.mem_Icc.mp hk).1).1.mono ((A.𝒢 s).le k) le_rfl))
  convert hm.const_smul (1 / (T : ℝ)) using 1
  rfl

omit [IsProbabilityMeasure μ] in
theorem selected_gradient_bound {ε : ℝ} (ω : Ω)
    (hs : ∃ s, ‖P.g (output (A.runs s) ω)‖ ^ 2 ≤ ε / 8)
    (he : ∀ s, ‖estimate A.runs A.η T s ω - P.g (output (A.runs s) ω)‖ ^ 2 ≤ ε / 12) :
    ‖P.g (chosen A ω)‖ ^ 2 ≤ ε := by
  obtain ⟨s, hs⟩ := hs
  have h1 := norm_sq_compare (P.g (chosen A ω)) (estimate A.runs A.η T (A.sStar ω) ω)
  have h2 := norm_sq_compare (estimate A.runs A.η T s ω) (P.g (output (A.runs s) ω))
  rw [norm_sub_rev (P.g (output (A.runs s) ω))] at h2
  have hmin := A.selected_min ω s
  have hminsq : ‖estimate A.runs A.η T (A.sStar ω) ω‖ ^ 2 ≤
      ‖estimate A.runs A.η T s ω‖ ^ 2 := by
    nlinarith [norm_nonneg (estimate A.runs A.η T (A.sStar ω) ω)]
  have he1 := he (A.sStar ω)
  have he2 := he s
  change ‖estimate A.runs A.η T (A.sStar ω) ω - P.g (chosen A ω)‖ ^ 2 ≤ ε / 12 at he1
  linarith

theorem two_phase_probability (hg : Continuous P.g) {ε Λ : ℝ} (hε : 0 < ε)
    (hT : 1 ≤ T)
    (hgrad : ∀ s, Integrable (fun ω => ‖P.g (output (A.runs s) ω)‖ ^ 2) μ ∧
      (∫ ω, ‖P.g (output (A.runs s) ω)‖ ^ 2 ∂μ) ≤ ε / 16)
    (hS : (1 / 2 : ℝ) ^ S ≤ Λ / 2)
    (hpost : 12 * (S : ℝ) * P.σ ^ 2 / ((T : ℝ) * ε) ≤ Λ / 2) :
    ENNReal.ofReal (1-Λ) ≤ μ {ω | ‖P.g (chosen A ω)‖ ^ 2 ≤ ε} := by
  let X := fun (s : Fin S) (ω : Ω) => ‖P.g (output (A.runs s) ω)‖ ^ 2
  let Y := fun (s : Fin S) (ω : Ω) =>
    ‖estimate A.runs A.η T s ω - P.g (output (A.runs s) ω)‖ ^ 2
  have hx : ∀ s, Measurable (X s) := fun s =>
    (hg.measurable.comp ((A.post_a1.1 s).mono ((A.𝒢 s).le 0) le_rfl)).norm.pow_const 2
  have hy : ∀ s, Measurable (Y s) := fun s =>
    ((estimate_measurable A s).sub (hg.measurable.comp
      ((A.post_a1.1 s).mono ((A.𝒢 s).le 0) le_rfl))).norm.pow_const 2
  have hind : iIndepFun X μ := A.outputs_indep.comp
    (fun _ x => ‖P.g x‖ ^ 2) (fun _ => hg.measurable.norm.pow_const 2)
  have hb : (S : ℝ) * ((P.σ ^ 2 / (T : ℝ)) / (ε / 12)) ≤ Λ / 2 := by
    convert hpost using 1
    ring
  have hgood := good_event_lower_bound X Y hx hy hind hε
    (fun s => (hgrad s).1) (fun s => (post_estimation_bound A hg s hT).1)
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _)
    (fun s => (hgrad s).2) (fun s => (post_estimation_bound A hg s hT).2) hS hb
  apply hgood.trans (measure_mono ?_)
  intro ω hω
  exact selected_gradient_bound A ω hω.1 hω.2

end TwoPhaseRSGProof


open MeasureTheory ProbabilityTheory GhadimiLan.TwoPhase GhadimiLan.RSG

namespace TwoPhaseRSGProof

variable {n N : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem n Ξ}

omit [IsProbabilityMeasure μ] in
lemma output_sum (A : Run P N μ) (ω : Ω) :
    output A ω = ∑ k ∈ Finset.Icc 1 N, if A.R ω = k then A.x k ω else 0 := by
  rw [Finset.sum_eq_single (A.R ω)]
  · simp [output]
  · intro k _ hne
    simp [Ne.symm hne]
  · intro h
    exact False.elim (h (A.index.2.1 ω))

omit [IsProbabilityMeasure μ] in
lemma measurable_output (A : Run P N μ) : Measurable (output A) := by
  have he : output A = fun ω => ∑ k ∈ Finset.Icc 1 N,
      if A.R ω = k then A.x k ω else 0 := funext (output_sum A)
  rw [he]
  apply Finset.measurable_sum
  intro k hk
  exact (run_measurable A (Finset.mem_Icc.mp hk).1).ite
    (A.index.1 (measurableSet_singleton k)) measurable_const

lemma output_memLp (A : Run P N μ) : MemLp (output A) 2 μ := by
  have he : output A = fun ω => ∑ k ∈ Finset.Icc 1 N,
      {ω | A.R ω = k}.indicator (A.x k) ω := by
    funext ω
    rw [output_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : A.R ω = k <;> simp [h]
  rw [he]
  exact memLp_finsetSum _ (fun k hk => (run_memLp A (Finset.mem_Icc.mp hk).1).indicator
    (A.index.1 (measurableSet_singleton k)))

lemma output_gradient_sq_integrable (A : Run P N μ) :
    Integrable (fun ω => ‖P.g (output A ω)‖ ^ 2) μ :=
  (gradient_memLp P (output_memLp A)).norm.integrable_sq

omit [IsProbabilityMeasure μ] in
lemma gradient_output_sum (A : Run P N μ) (ω : Ω) :
    ‖P.g (output A ω)‖ ^ 2 = ∑ k ∈ Finset.Icc 1 N,
      (if A.R ω = k then (1 : ℝ) else 0) * ‖P.g (A.x k ω)‖ ^ 2 := by
  rw [Finset.sum_eq_single (A.R ω)]
  · simp [output]
  · intro k _ hne
    simp [Ne.symm hne]
  · intro h
    exact False.elim (h (A.index.2.1 ω))

omit [IsProbabilityMeasure μ] in
lemma index_indicator_integral (A : Run P N μ) {k : ℕ} (hk : k ∈ Finset.Icc 1 N)
    (hN : 1 ≤ N) :
    (∫ ω, if A.R ω = k then (1 : ℝ) else 0 ∂μ) = 1 / (N : ℝ) := by
  have he : (fun ω => if A.R ω = k then (1 : ℝ) else 0) =
      {ω | A.R ω = k}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : A.R ω = k <;> simp [h]
  have hi : (∫ ω, if A.R ω = k then (1 : ℝ) else 0 ∂μ) = μ.real {ω | A.R ω = k} := by
    rw [he]
    convert integral_indicator_one (μ := μ) (s := {ω | A.R ω = k})
      (A.index.1 (measurableSet_singleton k)) using 1
    rfl
  rw [hi, measureReal_def, A.index.2.2 k hk, uniform_pmf P hN k,
    ENNReal.toReal_ofReal (by positivity)]

lemma random_output_expectation (A : Run P N μ) (hN : 1 ≤ N) :
    (∫ ω, ‖P.g (output A ω)‖ ^ 2 ∂μ) =
      (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, ∫ ω, ‖P.g (A.x k ω)‖ ^ 2 ∂μ := by
  have hs : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω =>
      (if A.R ω = k then (1 : ℝ) else 0) * ‖P.g (A.x k ω)‖ ^ 2) μ := by
    intro k hk
    have hh := (run_gradient_sq_integrable A (Finset.mem_Icc.mp hk).1).indicator
      (A.index.1 (measurableSet_singleton k))
    have he : (fun ω => (if A.R ω = k then (1 : ℝ) else 0) * ‖P.g (A.x k ω)‖ ^ 2) =
        {ω | A.R ω = k}.indicator (fun ω => ‖P.g (A.x k ω)‖ ^ 2) := by
      funext ω
      by_cases h : A.R ω = k <;> simp [h]
    rw [he]
    exact hh
  simp_rw [gradient_output_sum A]
  rw [integral_finsetSum _ hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hi := (index_indep_gradient A (Finset.mem_Icc.mp hk).1).comp
    (show Measurable (fun j : ℕ => if j = k then (1 : ℝ) else 0) from
      measurable_of_countable _)
    (continuous_norm.pow 2).measurable
  have hleft : Measurable (fun ω => if A.R ω = k then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun j : ℕ => if j = k then (1 : ℝ) else 0)).comp A.index.1
  have hright := (run_gradient_sq_integrable A (Finset.mem_Icc.mp hk).1).aestronglyMeasurable
  have hi2 : IndepFun (fun ω => if A.R ω = k then (1 : ℝ) else 0)
      (fun ω => ‖P.g (A.x k ω)‖^2) μ := by
    convert hi using 1 <;> rfl
  rw [hi2.integral_fun_mul_eq_mul_integral hleft.aestronglyMeasurable hright,
    index_indicator_integral A hk hN]

end TwoPhaseRSGProof


open MeasureTheory ProbabilityTheory GhadimiLan.TwoPhase GhadimiLan.RSG
open scoped InnerProductSpace

namespace TwoPhaseRSGProof

variable {n N : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem n Ξ}

lemma noisy_descent (P : Problem n Ξ) (x e : E n) (γ : ℝ) :
    P.f (x - γ • (P.g x + e)) ≤ P.f x - (γ - P.L * γ^2 / 2) * ‖P.g x‖^2 -
      γ * (1 - P.L * γ) * inner ℝ (P.g x) e + (P.L * γ^2 / 2) * ‖e‖^2 := by
  have hh := smooth_descent P x (-γ • (P.g x + e))
  have he : x + -γ • (P.g x + e) = x - γ • (P.g x + e) := by module
  rw [he] at hh
  simp only [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq, norm_add_sq_real] at hh
  nlinarith

lemma run_error_centered (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    μ[(fun ω => P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω)) | A.ℱ (k - 1)] =ᵐ[μ] 0 := by
  apply condExp_sub_centered (A.ℱ.le _) (A.a1.2 k hk).2.1
    ((run_gradient_memLp A hk).integrable one_le_two)
    (((gradient_continuous P).measurable.comp (run_adapted A hk)).stronglyMeasurable)
    (A.a1.2 k hk).2.2.1

lemma run_inner_zero (A : Run P N μ) {k : ℕ} (hk : 1 ≤ k) :
    (∫ ω, inner ℝ (P.g (A.x k ω))
      (P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω)) ∂μ) = 0 := by
  exact integral_inner_eq_zero (A.ℱ.le _) (run_gradient_memLp A hk) (run_error_memLp A hk)
    (((gradient_continuous P).measurable.comp (run_adapted A hk)).aestronglyMeasurable)
    (run_error_centered A hk)

omit [IsProbabilityMeasure μ] in
lemma run_descent_telescope (A : Run P N μ) (ω : Ω) (K : ℕ) :
    let γ := rsgStep P.L P.Dt P.σ N
    (γ - P.L * γ^2 / 2) * (∑ k ∈ Finset.Icc 1 K, ‖P.g (A.x k ω)‖^2) ≤
      P.f P.x₁ - P.f (A.x (K+1) ω) - γ*(1-P.L*γ) *
        (∑ k ∈ Finset.Icc 1 K, inner ℝ (P.g (A.x k ω))
          (P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω))) + (P.L*γ^2/2) *
        (∑ k ∈ Finset.Icc 1 K, ‖P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω)‖^2) := by
  dsimp only
  induction K with
  | zero => simp [A.recursion.1 ω]
  | succ K ih =>
    have h := noisy_descent P (A.x (K+1) ω)
      (P.G (A.x (K+1) ω) (A.ξ (K+1) ω) - P.g (A.x (K+1) ω))
      (rsgStep P.L P.Dt P.σ N)
    rw [add_sub_cancel, ← A.recursion.2 (K+1) (by omega) ω] at h
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    linarith

lemma expected_descent (A : Run P N μ) (_hN : 1 ≤ N) :
    let γ := rsgStep P.L P.Dt P.σ N
    (γ - P.L * γ^2 / 2) * (∑ k ∈ Finset.Icc 1 N, ∫ ω, ‖P.g (A.x k ω)‖^2 ∂μ) ≤
      P.f P.x₁ - P.fstar + (P.L*γ^2/2) * (N : ℝ) * P.σ^2 := by
  let γ := rsgStep P.L P.Dt P.σ N
  let Z := fun k ω => inner ℝ (P.g (A.x k ω))
    (P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω))
  let Q := fun k ω => ‖P.G (A.x k ω) (A.ξ k ω) - P.g (A.x k ω)‖^2
  have hG : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖P.g (A.x k ω)‖^2) μ :=
    fun k hk => run_gradient_sq_integrable A (Finset.mem_Icc.mp hk).1
  have hZ : ∀ k ∈ Finset.Icc 1 N, Integrable (Z k) μ := fun k hk =>
    integrable_inner_of_memLp (run_gradient_memLp A (Finset.mem_Icc.mp hk).1)
      (run_error_memLp A (Finset.mem_Icc.mp hk).1)
  have hQ : ∀ k ∈ Finset.Icc 1 N, Integrable (Q k) μ := fun k hk =>
    (A.a1.2 k (Finset.mem_Icc.mp hk).1).2.2.2.1
  have hZm : Integrable (fun ω => γ*(1-P.L*γ) * ∑ k ∈ Finset.Icc 1 N, Z k ω) μ := by
    exact (integrable_finsetSum _ hZ).const_mul _
  have hQm : Integrable (fun ω => (P.L*γ^2/2) * ∑ k ∈ Finset.Icc 1 N, Q k ω) μ := by
    exact (integrable_finsetSum _ hQ).const_mul _
  have hR : Integrable (fun ω => P.f P.x₁-P.fstar -
      γ*(1-P.L*γ) * (∑ k ∈ Finset.Icc 1 N, Z k ω)) μ := by
    convert (integrable_const (P.f P.x₁-P.fstar)).sub hZm using 1
    rfl
  have hi := integral_mono
    ((integrable_finsetSum _ hG).const_mul (γ-P.L*γ^2/2))
    (hR.add hQm)
    (fun ω => (run_descent_telescope A ω N).trans (by
      change P.f P.x₁ - P.f (A.x (N+1) ω) -
        γ*(1-P.L*γ) * (∑ k ∈ Finset.Icc 1 N, Z k ω) +
        (P.L*γ^2/2) * (∑ k ∈ Finset.Icc 1 N, Q k ω) ≤
        P.f P.x₁ - P.fstar - γ*(1-P.L*γ) * (∑ k ∈ Finset.Icc 1 N, Z k ω) +
        (P.L*γ^2/2) * (∑ k ∈ Finset.Icc 1 N, Q k ω)
      have hf := infimum_le P (A.x (N+1) ω)
      linarith))
  change (∫ ω, (γ-P.L*γ^2/2) * (∑ k ∈ Finset.Icc 1 N, ‖P.g (A.x k ω)‖^2) ∂μ) ≤
    ∫ ω, (P.f P.x₁-P.fstar - γ*(1-P.L*γ) * (∑ k ∈ Finset.Icc 1 N, Z k ω)) +
      (P.L*γ^2/2) * (∑ k ∈ Finset.Icc 1 N, Q k ω) ∂μ at hi
  rw [integral_const_mul, integral_add hR hQm,
    integral_sub (integrable_const _) hZm,
    integral_const_mul, integral_const_mul, integral_finsetSum _ hG,
    integral_finsetSum _ hZ, integral_finsetSum _ hQ] at hi
  have hz : (∑ k ∈ Finset.Icc 1 N, ∫ ω, Z k ω ∂μ) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact run_inner_zero A (Finset.mem_Icc.mp hk).1
  have hq : (∑ k ∈ Finset.Icc 1 N, ∫ ω, Q k ω ∂μ) ≤ (N:ℝ)*P.σ^2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.Icc 1 N, P.σ^2 := Finset.sum_le_sum
        (fun k hk => (A.a1.2 k (Finset.mem_Icc.mp hk).1).2.2.2.2)
      _ = _ := by simp [Nat.card_Icc]
  rw [hz] at hi
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, mul_zero, sub_zero] at hi
  have hc : 0 ≤ P.L*γ^2/2 := div_nonneg (mul_nonneg P.L_pos.le (sq_nonneg γ)) (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hq hc
  dsimp only
  change (γ-P.L*γ^2/2) * _ ≤ _
  nlinarith

end TwoPhaseRSGProof


open MeasureTheory GhadimiLan.TwoPhase GhadimiLan.RSG

namespace TwoPhaseRSGProof

variable {n N : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Problem n Ξ}

lemma run_gradient_bound (A : Run P N μ) (hN : 1 ≤ N) :
    Integrable (fun ω => ‖P.g (output A ω)‖ ^ 2) μ ∧
    (∫ ω, ‖P.g (output A ω)‖ ^ 2 ∂μ) ≤ P.L * BN P.L (Df P) P.Dt P.σ N := by
  refine ⟨output_gradient_sq_integrable A, ?_⟩
  let γ := rsgStep P.L P.Dt P.σ N
  let Q := ∑ k ∈ Finset.Icc 1 N, ∫ ω, ‖P.g (A.x k ω)‖^2 ∂μ
  have hg : 0 < γ := step_pos P hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hm : P.L*γ ≤ 1 := step_mul_le_one P N
  have hc : γ/2 ≤ γ-P.L*γ^2/2 := by nlinarith
  have hd := expected_descent A hN
  change (γ-P.L*γ^2/2)*Q ≤ _ at hd
  have hsmall := mul_le_mul_of_nonneg_right hc hQ
  have hb : γ*Q ≤ 2*(P.f P.x₁-P.fstar)+P.L*γ^2*(N:ℝ)*P.σ^2 := by nlinarith
  rw [random_output_expectation A hN]
  change (1/(N:ℝ))*Q ≤ _
  calc
    _ ≤ (2*(P.f P.x₁-P.fstar)+P.L*γ^2*(N:ℝ)*P.σ^2)/((N:ℝ)*γ) := by
      apply (le_div_iff₀ (mul_pos hn hg)).mpr
      convert hb using 1 <;> first | rfl | field_simp
    _ = P.L*((Df P)^2/((N:ℝ)*γ)+γ*P.σ^2) := by
      rw [df_sq P]
      field_simp [P.L_pos.ne', hn.ne', hg.ne']
    _ ≤ _ := step_final_bound P hN

end TwoPhaseRSGProof


open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Theorem 2.4(b), Eqs. (2.24)–(2.27), p. 12. The logarithm in (2.24)
is read in base two, as required by the paper's final 2⁻ˢ bound. -/
theorem full_native_result {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : System (S := S) (N := N) (T := T) P μ)
    (ε Λ : ℝ) (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hS : S = Nat.ceil (Real.logb 2 (2 / Λ)))
    (hN : N = Nat.ceil (max (32 * P.L ^ 2 * Df P ^ 2 / ε)
      ((32 * P.L * (P.Dt + Df P ^ 2 / P.Dt) * P.σ / ε) ^ 2)))
    (hT : T = Nat.ceil (24 * ((S : ℝ) + 1) * P.σ ^ 2 / (Λ * ε))) :
    ENNReal.ofReal (1 - Λ) ≤
      μ {ω | ‖P.g (chosen A ω)‖ ^ 2 ≤ ε} := by
  have hnb := TwoPhaseRSGProof.trajectory_count_budget P.L_pos P.Dt_pos P.σ_pos hε hN
  have hsb := TwoPhaseRSGProof.candidate_count_budget hΛ0 hΛ1 hS
  have htb := TwoPhaseRSGProof.post_count_budget hΛ0 hε P.σ_pos S hT
  apply TwoPhaseRSGProof.two_phase_probability A (TwoPhaseRSGProof.gradient_continuous P)
    hε htb.1 _ hsb.2 htb.2
  intro s
  have hh := TwoPhaseRSGProof.run_gradient_bound (A.runs s) hnb.1
  exact ⟨hh.1, hh.2.trans hnb.2⟩

end GhadimiLan.TwoPhase


open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Theorem 2.4(b), Eqs. (2.24)–(2.27), p. 12. The logarithm in (2.24)
is read in base two, as required by the paper's final 2⁻ˢ bound. -/
theorem theorem_2_4_b {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : System (S := S) (N := N) (T := T) P μ)
    (ε Λ : ℝ) (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hS : S = Nat.ceil (Real.logb 2 (2 / Λ)))
    (hN : N = Nat.ceil (max (32 * P.L ^ 2 * Df P ^ 2 / ε)
      ((32 * P.L * (P.Dt + Df P ^ 2 / P.Dt) * P.σ / ε) ^ 2)))
    (hT : T = Nat.ceil (24 * ((S : ℝ) + 1) * P.σ ^ 2 / (Λ * ε))) :
    ENNReal.ofReal (1 - Λ) ≤
      μ {ω | ‖P.g (chosen A ω)‖ ^ 2 ≤ ε} := by
  exact full_native_result μ P A ε Λ hε hΛ0 hΛ1 hS hN hT

end GhadimiLan.TwoPhase

open GhadimiLan.TwoPhase

theorem solution {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : System (S := S) (N := N) (T := T) P μ)
    (ε Λ : ℝ) (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hS : S = Nat.ceil (Real.logb 2 (2 / Λ)))
    (hN : N = Nat.ceil (max (32 * P.L ^ 2 * Df P ^ 2 / ε)
      ((32 * P.L * (P.Dt + Df P ^ 2 / P.Dt) * P.σ / ε) ^ 2)))
    (hT : T = Nat.ceil (24 * ((S : ℝ) + 1) * P.σ ^ 2 / (Λ * ε))) :
    ENNReal.ofReal (1 - Λ) ≤
      μ {ω | ‖P.g (chosen A ω)‖ ^ 2 ≤ ε} := GhadimiLan.TwoPhase.theorem_2_4_b μ P A ε Λ hε hΛ0 hΛ1 hS hN hT
